package bcpi.dataflow;

import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.Varnode;

import com.google.common.math.LongMath;
import com.google.common.primitives.UnsignedLong;

import java.util.BitSet;
import java.util.List;
import java.util.Objects;
import java.util.OptionalLong;
import java.util.function.BinaryOperator;
import java.util.function.LongBinaryOperator;
import java.util.function.LongFunction;
import java.util.function.LongPredicate;
import java.util.function.LongUnaryOperator;
import java.util.function.UnaryOperator;

/**
 * The abstract domain for integer varnodes.
 */
public class IntDomain implements SparseDomain<IntDomain, IntDomain> {
	private static final BitSet SUPPORTED = new BitSet(PcodeOp.PCODE_MAX);
	static {
		SUPPORTED.set(PcodeOp.BOOL_AND);
		SUPPORTED.set(PcodeOp.BOOL_NEGATE);
		SUPPORTED.set(PcodeOp.BOOL_OR);
		SUPPORTED.set(PcodeOp.BOOL_XOR);
		SUPPORTED.set(PcodeOp.CAST);
		SUPPORTED.set(PcodeOp.COPY);
		SUPPORTED.set(PcodeOp.INT_2COMP);
		SUPPORTED.set(PcodeOp.INT_ADD);
		SUPPORTED.set(PcodeOp.INT_AND);
		SUPPORTED.set(PcodeOp.INT_DIV);
		SUPPORTED.set(PcodeOp.INT_EQUAL);
		SUPPORTED.set(PcodeOp.INT_LEFT);
		SUPPORTED.set(PcodeOp.INT_LESS);
		SUPPORTED.set(PcodeOp.INT_LESSEQUAL);
		SUPPORTED.set(PcodeOp.INT_MULT);
		SUPPORTED.set(PcodeOp.INT_NEGATE);
		SUPPORTED.set(PcodeOp.INT_NOTEQUAL);
		SUPPORTED.set(PcodeOp.INT_OR);
		SUPPORTED.set(PcodeOp.INT_REM);
		SUPPORTED.set(PcodeOp.INT_RIGHT);
		SUPPORTED.set(PcodeOp.INT_SDIV);
		SUPPORTED.set(PcodeOp.INT_SEXT);
		SUPPORTED.set(PcodeOp.INT_SLESS);
		SUPPORTED.set(PcodeOp.INT_SLESSEQUAL);
		SUPPORTED.set(PcodeOp.INT_SREM);
		SUPPORTED.set(PcodeOp.INT_SRIGHT);
		SUPPORTED.set(PcodeOp.INT_SUB);
		SUPPORTED.set(PcodeOp.INT_XOR);
		SUPPORTED.set(PcodeOp.INT_ZEXT);
		SUPPORTED.set(PcodeOp.MULTIEQUAL);
		SUPPORTED.set(PcodeOp.POPCOUNT);
		SUPPORTED.set(PcodeOp.SUBPIECE);
	}

	// Represents a congruence class of numbers
	//
	//     {o + k*m | k ∈ ℤ}
	//
	// Constants are represented by m == 0; otherwise, we have an infinite
	// set of integers satisfying
	//
	//     {n | n == o (mod m)}
	//
	// The top lattice element is ℤ itself, encoded as o == 0, m == 1.
	// The bottom lattice element is the empty set, encoded as o == 1, m == 1.
	private long offset;
	private long modulus;

	private IntDomain(long offset, long modulus) {
		this.offset = offset;
		this.modulus = modulus;
	}

	/**
	 * Reduce modulo a possibly-zero modulus.
	 */
	private static long reduce(long offset, long modulus) {
		if (modulus == 0) {
			return offset;
		} else {
			return Math.floorMod(offset, modulus);
		}
	}

	/**
	 * Create a new IntDomain, automatically reducing the offset.
	 */
	private static IntDomain create(long offset, long modulus) {
		return new IntDomain(reduce(offset, modulus), Math.abs(modulus));
	}

	/**
	 * @return The bottom element of this lattice.
	 */
	public static IntDomain bottom() {
		return new IntDomain(1, 1);
	}

	/**
	 * @return Whether this is the bottom lattice element.
	 */
	public boolean isBottom() {
		return this.offset == 1 && this.modulus == 1;
	}

	/**
	 * @return The top element of this lattice.
	 */
	public static IntDomain top() {
		return new IntDomain(0, 1);
	}

	/**
	 * @return Whether this is the top lattice element.
	 */
	public boolean isTop() {
		return this.offset == 0 && this.modulus == 1;
	}

	/**
	 * @return An abstract value for a constant.
	 */
	public static IntDomain constant(long value) {
		return new IntDomain(value, 0);
	}

	/**
	 * @return Whether this abstract value is a constant.
	 */
	public boolean isConstant() {
		return this.modulus == 0;
	}

	/**
	 * @return The value of this integer, if it is constant.
	 */
	public OptionalLong getIfConstant() {
		if (isConstant()) {
			return OptionalLong.of(this.offset);
		} else {
			return OptionalLong.empty();
		}
	}

	/**
	 * @return An abstract value for an arbitrary multiple.
	 */
	public static IntDomain multipleOf(long modulus) {
		return create(0, modulus);
	}

	/**
	 * @return Whether this value could equal the given number.
	 */
	public boolean contains(long value) {
		return reduce(value, this.modulus) == this.offset;
	}

	@Override
	public IntDomain copy() {
		return new IntDomain(this.offset, this.modulus);
	}

	@Override
	public boolean joinInPlace(IntDomain other) {
		var joined = join(other);
		var same = equals(joined);
		this.modulus = joined.modulus;
		this.offset = joined.offset;
		return !same;
	}

	@Override
	public IntDomain join(IntDomain other) {
		if (isBottom()) {
			return other.copy();
		} else if (other.isBottom()) {
			return copy();
		}

		return map(other, (a, m, b, n) -> {
			long diff = LongMath.checkedSubtract(Math.max(a, b), Math.min(a, b));
			long gcd = LongMath.gcd(m, n);
			gcd = LongMath.gcd(gcd, diff);
			return create(a, gcd);
		});
	}

	@Override
	public IntDomain getDefault(Varnode vn) {
		if (vn.isConstant()) {
			return constant(vn.getOffset());
		} else if (vn.getDef() == null) {
			// Parameters etc. can be anything
			return top();
		} else {
			// Locals start out uninitialized
			return bottom();
		}
	}

	@FunctionalInterface
	private interface UnaryOp {
		IntDomain apply(long offset, long modulus);
	}

	/** Compute a new value from this offset and modulus, propagating bottom. */
	private IntDomain map(UnaryOp op) {
		if (isBottom()) {
			return bottom();
		}

		try {
			return op.apply(this.offset, this.modulus);
		} catch (ArithmeticException e) {
			// ...
		}

		return top();
	}

	@FunctionalInterface
	private interface UnaryConstOp {
		IntDomain apply(long n);
	}

	/** Apply a unary operator if the input is constant. */
	private IntDomain mapConstant(UnaryConstOp op) {
		return map((o, m) -> m == 0 ? op.apply(o) : top());
	}

	/** Apply a unary operator if the input is constant. */
	private IntDomain mapLong(LongUnaryOperator op) {
		return mapConstant(n -> constant(op.applyAsLong(n)));
	}

	/** @return -this */
	public IntDomain negate() {
		return map((o, m) -> create(-o, m));
	}

	/** @return ~this */
	public IntDomain not() {
		return this.add(constant(1)).negate();
	}

	/** @return The number of set bits. */
	public IntDomain bitCount() {
		return mapLong(Long::bitCount);
	}

	@FunctionalInterface
	private interface BinaryOp {
		IntDomain apply(long a, long m, long b, long n);
	}

	/** Compute a new value from two offsets and moduli, propagating bottom. */
	private IntDomain map(IntDomain other, BinaryOp op) {
		return map((a, m) -> other.map((b, n) -> op.apply(a, m, b, n)));
	}

	/** @return this + rhs */
	public IntDomain add(IntDomain rhs) {
		return map(rhs, (a, m, b, n) -> {
			var gcd = LongMath.gcd(m, n);
			var offset = LongMath.checkedAdd(a, b);
			return create(offset, gcd);
		});
	}

	/** @return this - rhs */
	public IntDomain subtract(IntDomain rhs) {
		return map(rhs, (a, m, b, n) -> {
			var gcd = LongMath.gcd(m, n);
			var offset = LongMath.checkedSubtract(a, b);
			return create(offset, gcd);
		});
	}

	/** @return this * rhs */
	public IntDomain multiply(IntDomain rhs) {
		return map(rhs, (a, m, b, n) -> {
			//    (a + m*j) * (b + n*k)
			// == a*b + a*n*k + b*m*j + m*n*j*k
			var ab = LongMath.checkedMultiply(a, b);
			var an = LongMath.checkedMultiply(a, n);
			var bm = LongMath.checkedMultiply(b, m);
			var mn = LongMath.checkedMultiply(m, n);
			return constant(ab)
				.add(multipleOf(an))
				.add(multipleOf(bm))
				.add(multipleOf(mn));
		});
	}

	/** @return this / rhs */
	public IntDomain divide(IntDomain rhs) {
		return rhs.mapConstant(r -> {
			if (r == 0) {
				return bottom();
			} else if (r == 1) {
				return copy();
			} else if (r == -1) {
				return negate();
			} else {
				return mapLong(l -> l / r);
			}
		});
	}

	/** @return this % rhs */
	public IntDomain remainder(IntDomain rhs) {
		return rhs.mapConstant(r -> {
			if (r == 0) {
				return bottom();
			}

			return map((o, m) -> {
				long modulus;
				if (m == 0 || m % r == 0) {
					modulus = 0;
				} else {
					modulus = LongMath.gcd(m, Math.abs(r));
				}
				// Negative dividends give a different remainder
				var pos = create(o % r, modulus);
				var neg = create((o - m) % r, modulus);
				return pos.join(neg);
			});
		});
	}

	/** @return |this| % rhs */
	public IntDomain mod(IntDomain rhs) {
		return rhs.mapConstant(r -> {
			if (r == 0) {
				return bottom();
			}

			return map((o, m) -> {
				long modulus;
				if (m == 0 || m % r == 0) {
					modulus = 0;
				} else {
					modulus = LongMath.gcd(m, Math.abs(r));
				}
				return create(o % r, modulus);
			});
		});
	}

	/** @return this / rhs */
	public IntDomain divideUnsigned(IntDomain rhs) {
		return rhs.mapConstant(r -> {
			if (r == 0) {
				return bottom();
			} else if (r == 1) {
				return copy();
			} else {
				return mapLong(l -> Long.divideUnsigned(l, r));
			}
		});
	}

	/** @return this % rhs */
	public IntDomain remainderUnsigned(IntDomain rhs) {
		return rhs.mapConstant(r -> {
			if (r == 0) {
				return bottom();
			} else if (r == 1) {
				return constant(0);
			} else {
				// TODO: Figure out join() for unsigned inputs so we can match mod()
				return mapLong(l -> Long.remainderUnsigned(l, r));
			}
			/*
			return map((o, m) -> {
				long modulus;
				if (m == 0 || Long.remainderUnsigned(m, r) == 0) {
					modulus = 0;
				} else {
					var um = UnsignedLong.fromLongBits(m).bigIntegerValue();
					var ur = UnsignedLong.fromLongBits(r).bigIntegerValue();
					modulus = um.gcd(ur).longValueExact();
				}
				return create(Long.remainderUnsigned(o, r), modulus);
			});
			*/
		});
	}

	@FunctionalInterface
	private interface BinaryConstOp {
		IntDomain apply(long lhs, long rhs);
	}

	/** Apply a binary operator if the inputs are both constant. */
	private IntDomain mapConstants(IntDomain rhs, BinaryConstOp op) {
		return mapConstant(l -> rhs.mapConstant(r -> op.apply(l, r)));
	}

	/** Apply a binary operator if the inputs are both constant. */
	private IntDomain mapLongs(IntDomain rhs, LongBinaryOperator op) {
		return mapConstants(rhs, (l, r) -> constant(op.applyAsLong(l, r)));
	}

	/** @return this & rhs */
	public IntDomain and(IntDomain rhs) {
		return mapLongs(rhs, (l, r) -> l & r);
	}

	/** @return this | rhs */
	public IntDomain or(IntDomain rhs) {
		return mapLongs(rhs, (l, r) -> l | r);
	}

	/** @return this ^ rhs */
	public IntDomain xor(IntDomain rhs) {
		return mapLongs(rhs, (l, r) -> l ^ r);
	}

	/** @return this << rhs */
	public IntDomain shiftLeft(IntDomain rhs) {
		return rhs.mapConstant(n -> {
			if (n < Long.SIZE) {
				return this.multiply(constant(1L << n));
			} else {
				return top();
			}
		});
	}

	/** @return this >> rhs */
	public IntDomain shiftRight(IntDomain rhs) {
		return mapLongs(rhs, (l, r) -> l >> r);
	}

	/** @return this >>> rhs */
	public IntDomain shiftRightUnsigned(IntDomain rhs) {
		return mapLongs(rhs, (l, r) -> l >>> r);
	}

	/**
	 * @return A copy of this value truncated to fit the given varnode.
	 */
	private IntDomain truncate(Varnode vn) {
		long bits = 8 * vn.getSize();
		if (bits < Long.SIZE) {
			return mod(constant(1L << bits));
		} else {
			return copy();
		}
	}

	/**
	 * @return A copy of this value sign-extended to fit the given varnode.
	 */
	private IntDomain signExtend(Varnode vn) {
		long bits = 8 * vn.getSize();
		if (bits >= Long.SIZE) {
			return copy();
		}

		long bit = 1L << bits;
		return mapConstant(n -> constant((n & bit) == 0 ? n : n | -bit));
	}

	/**
	 * @return A VarMap that sign-extends.
	 */
	private static VarMap<IntDomain> sext(VarMap<IntDomain> map) {
		return v -> map.get(v).signExtend(v);
	}

	/**
	 * Evaluate a unary pcode operation.
	 */
	private static IntDomain unaryOp(PcodeOp op, VarMap<IntDomain> map, UnaryOperator<IntDomain> func) {
		var input = map.getInput(op, 0);
		return func.apply(input)
			.truncate(op.getOutput());
	}

	/** @return this != 0 */
	private IntDomain isNonzero() {
		var canBeZero = contains(0);
		var canBeNonzero = !isBottom() && (this.offset != 0 || this.modulus != 0);
		if (canBeZero && canBeNonzero) {
			return top();
		} else if (canBeZero) {
			return constant(0);
		} else if (canBeNonzero) {
			return constant(1);
		} else {
			return bottom();
		}
	}

	/** @return this == 0 */
	private IntDomain isZero() {
		return constant(1).subtract(isNonzero());
	}

	/**
	 * Evaluate a binary pcode operation.
	 */
	private static IntDomain binaryOp(PcodeOp op, VarMap<IntDomain> map, BinaryOperator<IntDomain> func) {
		var lhs = map.getInput(op, 0);
		var rhs = map.getInput(op, 1);
		return func.apply(lhs, rhs)
			.truncate(op.getOutput());
	}

	@FunctionalInterface
	private interface LongBinaryPredicate {
		boolean test(long lhs, long rhs);
	}

	/**
	 * Evaluate a binary pcode predicate.
	 */
	private static IntDomain binaryPred(PcodeOp op, VarMap<IntDomain> map, LongBinaryPredicate pred) {
		return binaryOp(op, map, (a, b) -> a.mapConstants(b, (l, r) -> constant(pred.test(l, r) ? 1 : 0)));
	}

	@Override
	public boolean supports(PcodeOp op) {
		return SUPPORTED.get(op.getOpcode());
	}

	@Override
	public IntDomain visit(PcodeOp op, VarMap<IntDomain> map) {
		switch (op.getOpcode()) {
			case PcodeOp.COPY:
			case PcodeOp.CAST:
				return map.getInput(op, 0).copy();

			case PcodeOp.MULTIEQUAL:
				// Phi node
				return bottom().join(map.getInputs(op));

			case PcodeOp.SUBPIECE:
				// (l, r) -> l >> 8 * r
				return binaryOp(op, map, (l, r) -> l.shiftRightUnsigned(r.multiply(constant(8))));

			case PcodeOp.POPCOUNT:
				return unaryOp(op, map, IntDomain::bitCount);

			case PcodeOp.INT_EQUAL:
				// l == r <=> (l - r) != 0
				return binaryOp(op, map, IntDomain::subtract).isNonzero();
			case PcodeOp.INT_NOTEQUAL:
				// l == r <=> (l - r) == 0
				return binaryOp(op, map, IntDomain::subtract).isZero();

			case PcodeOp.INT_LESS:
				return binaryPred(op, map, (l, r) -> Long.compareUnsigned(l, r) < 0);
			case PcodeOp.INT_LESSEQUAL:
				return binaryPred(op, map, (l, r) -> Long.compareUnsigned(l, r) <= 0);

			case PcodeOp.INT_SLESS:
				return binaryPred(op, sext(map), (l, r) -> l < r);
			case PcodeOp.INT_SLESSEQUAL:
				return binaryPred(op, sext(map), (l, r) -> l <= r);

			case PcodeOp.INT_ZEXT:
				return map.getInput(op, 0).copy();
			case PcodeOp.INT_SEXT:
				return sext(map).getInput(op, 0).copy();

			case PcodeOp.INT_ADD:
				return binaryOp(op, map, IntDomain::add);
			case PcodeOp.INT_SUB:
				return binaryOp(op, map, IntDomain::subtract);

			case PcodeOp.INT_2COMP:
				return unaryOp(op, map, IntDomain::negate);
			case PcodeOp.INT_NEGATE:
				return unaryOp(op, map, IntDomain::not);

			case PcodeOp.INT_XOR:
				return binaryOp(op, map, IntDomain::xor);
			case PcodeOp.INT_AND:
				return binaryOp(op, map, IntDomain::and);
			case PcodeOp.INT_OR:
				return binaryOp(op, map, IntDomain::or);

			case PcodeOp.INT_LEFT:
				return binaryOp(op, map, IntDomain::shiftLeft);
			case PcodeOp.INT_RIGHT:
				return binaryOp(op, map, IntDomain::shiftRightUnsigned);
			case PcodeOp.INT_SRIGHT:
				return binaryOp(op, sext(map), IntDomain::shiftRight);

			case PcodeOp.INT_MULT:
				return binaryOp(op, map, IntDomain::multiply);

			case PcodeOp.INT_DIV:
				return binaryOp(op, map, IntDomain::divideUnsigned);
			case PcodeOp.INT_SDIV:
				return binaryOp(op, sext(map), IntDomain::divide);

			case PcodeOp.INT_REM:
				return binaryOp(op, map, IntDomain::remainderUnsigned);
			case PcodeOp.INT_SREM:
				return binaryOp(op, sext(map), IntDomain::remainder);

			case PcodeOp.BOOL_NEGATE:
				return map.getInput(op, 0).isZero();
			case PcodeOp.BOOL_XOR:
				return binaryOp(op, map, IntDomain::xor).isNonzero();
			case PcodeOp.BOOL_AND:
				return binaryOp(op, map, IntDomain::and).isNonzero();
			case PcodeOp.BOOL_OR:
				return binaryOp(op, map, IntDomain::or).isNonzero();

			default:
				return top();
		}
	}

	@Override
	public int hashCode() {
		var x = this.modulus;
		var y = this.offset;
		return Long.hashCode((x + y) * (x + y + 1) / 2 + y);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == this) {
			return true;
		} else if (!(obj instanceof IntDomain)) {
			return false;
		}

		var other = (IntDomain) obj;
		return this.modulus == other.modulus
			&& this.offset == other.offset;
	}

	@Override
	public String toString() {
		if (isBottom()) {
			return "⊥";
		} else if (isTop()) {
			return "⊤";
		} else if (isConstant()) {
			return String.format("{%d}", this.offset);
		} else {
			return String.format("{%d (mod %d)}", this.offset, this.modulus);
		}
	}

	private static final boolean CHECK = true;
	private static final long CHECK_MIN = -16;
	private static final long CHECK_MAX = 16;

	/**
	 * Check that the IntDomain implementation of a unary operator is
	 * consistent with the same operation on longs.
	 */
	private static void checkUnary(String op, LongUnaryOperator f, UnaryOperator<IntDomain> g) {
		// Check f(x) == g(x) for many x
		for (long x = CHECK_MIN; x <= CHECK_MAX; ++x) {
			var ix = constant(x);
			var fx = f.applyAsLong(x);
			var gx = g.apply(constant(x));
			var expected = String.format("%s(%d) == %d", op, x, fx);
			if (!gx.equals(constant(fx))) {
				var error = String.format("%s != %s", expected, gx);
				throw new RuntimeException(error);
			}

			// Check f(x) ∈ g(x ⊔ y) for many y
			for (long y = CHECK_MIN; y <= CHECK_MAX; ++y) {
				var xy = ix.join(constant(y));
				var gxy = g.apply(xy);
				if (!gxy.contains(fx)) {
					var actual = String.format("%s(%d ⊔ %d) == %s(%s) == %s", op, x, y, op, xy, gxy);
					var error = String.format("%s ∉ %s", expected, actual);
					throw new RuntimeException(error);
				}
			}
		}
	}

	/**
	 * Check that the IntDomain implementation of a binary operator is
	 * consistent with the same operation on longs.
	 */
	private static void checkBinary(String op, LongPredicate rhsRange, LongBinaryOperator f, BinaryOperator<IntDomain> g) {
		// Check f(x, y) == g(x, y) for many x, y
		for (long x = CHECK_MIN; x <= CHECK_MAX; ++x) {
			var ix = constant(x);

			for (long y = CHECK_MIN; y <= CHECK_MAX; ++y) {
				if (!rhsRange.test(y)) {
					continue;
				}

				var iy = constant(y);
				var fxy = f.applyAsLong(x, y);
				var gxy = g.apply(ix, iy);
				var expected = String.format("(%d %s %d) == %d", x, op, y, fxy);
				if (!gxy.equals(constant(fxy))) {
					var error = String.format("%s != %s", expected, gxy);
					throw new RuntimeException(error);
				}

				// Check f(x, y) ∈ g(x ⊔ z, y ⊔ w) for many z, w
				for (long z = CHECK_MIN; z <= CHECK_MAX; ++z) {
					var xz = ix.join(constant(z));

					for (long w = CHECK_MIN; w <= CHECK_MAX; ++w) {
						if (!rhsRange.test(y)) {
							continue;
						}

						var yw = iy.join(constant(w));
						var gxzyw = g.apply(xz, yw);
						if (!gxzyw.contains(fxy)) {
							var actual = String.format("((%d ⊔ %d) %s (%d ⊔ %d)) == (%s %s %s) == %s", x, z, op, y, w, xz, op, yw, gxzyw);
							var error = String.format("%s ∉ %s", expected, actual);
							throw new RuntimeException(error);
						}
					}
				}
			}
		}
	}

	private static void checkBinary(String op, LongBinaryOperator f, BinaryOperator<IntDomain> g) {
		checkBinary(op, y -> true, f, g);
	}

	static {
		if (CHECK) {
			checkUnary("-", x -> -x, IntDomain::negate);
			checkUnary("~", x -> ~x, IntDomain::not);
			checkUnary("bitCount", Long::bitCount, IntDomain::bitCount);

			checkBinary("+", (x, y) -> x + y, IntDomain::add);
			checkBinary("-", (x, y) -> x - y, IntDomain::subtract);
			checkBinary("*", (x, y) -> x * y, IntDomain::multiply);

			checkBinary("/", y -> y != 0, (x, y) -> x / y, IntDomain::divide);
			checkBinary("%", y -> y != 0, (x, y) -> x % y, IntDomain::remainder);

			checkBinary("/u", y -> y != 0, Long::divideUnsigned, IntDomain::divideUnsigned);
			checkBinary("%u", y -> y != 0, Long::remainderUnsigned, IntDomain::remainderUnsigned);

			checkBinary("<<", y -> y >= 0, (x, y) -> x << y, IntDomain::shiftLeft);
			checkBinary(">>", y -> y >= 0, (x, y) -> x >> y, IntDomain::shiftRight);
			checkBinary(">>>", y -> y >= 0, (x, y) -> x >>> y, IntDomain::shiftRightUnsigned);
		}
	}
}
