import ghidra.app.decompiler.ClangFieldToken;
import ghidra.app.decompiler.ClangLine;
import ghidra.app.decompiler.ClangToken;
import ghidra.app.decompiler.ClangTokenGroup;
import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileOptions;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.decompiler.component.DecompilerUtils;
import ghidra.app.decompiler.parallel.DecompileConfigurer;
import ghidra.app.decompiler.parallel.DecompilerCallback;
import ghidra.app.decompiler.parallel.ParallelDecompiler;
import ghidra.app.extension.datatype.finder.DecompilerVariable;
import ghidra.app.extension.datatype.finder.DecompilerReference;
import ghidra.app.script.GhidraScript;
import ghidra.graph.GraphAlgorithms;
import ghidra.graph.jung.JungDirectedGraph;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.block.BasicBlockModel;
import ghidra.program.model.block.CodeBlock;
import ghidra.program.model.block.CodeBlockIterator;
import ghidra.program.model.block.CodeBlockReference;
import ghidra.program.model.block.CodeBlockReferenceIterator;
import ghidra.program.model.block.graph.CodeBlockEdge;
import ghidra.program.model.block.graph.CodeBlockVertex;
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.DataTypeComponent;
import ghidra.program.model.data.DefaultDataType;
import ghidra.program.model.data.Structure;
import ghidra.program.model.data.StructureDataType;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.listing.Program;
import ghidra.util.Msg;
import ghidra.util.task.TaskMonitor;

import generic.concurrent.QCallback;

import com.google.common.base.Strings;
import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multiset;

import java.io.BufferedReader;
import java.io.IOException;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * Analyzes cache misses to suggest reorderings of struct fields.
 */
public class StructOrderAnalysis extends GhidraScript {
	@Override
	public void run() throws Exception {
		// Read address_info.csv to find relevant addresses
		String[] args = getScriptArgs();
		Path csv = Paths.get(args[0]);
		BcpiData data = BcpiData.parse(csv, this.currentProgram);

		// Get the decompilation of each function containing an address
		// for which we have data.  This is much faster than calling
		// DataTypeReferenceFinder once per field.
		Set<Function> functions = data.getRelevantFunctions();
		FieldReferences refs = FieldReferences.collect(this.currentProgram, functions, this.monitor);

		// Use our collected data to infer field access patterns
		AccessPatterns patterns = AccessPatterns.collect(this.currentProgram, data, refs, this.monitor);

		if (args.length > 1) {
			printDetails(patterns, args[1]);
		} else {
			printSummary(patterns);
		}
	}

	private static class SummaryRow {
		final Structure struct;
		final int nSamples;
		final int nPatterns;

		SummaryRow(Structure struct, int nSamples, int nPatterns) {
			this.struct = struct;
			this.nSamples = nSamples;
			this.nPatterns = nPatterns;
		}
	}

	private void printSummary(AccessPatterns patterns) {
		List<SummaryRow> rows = new ArrayList<>();
		for (Structure struct : patterns.getStructures()) {
			int nSamples = 0;
			int nPatterns = 0;
			for (AccessPattern pattern : patterns.getPatterns(struct)) {
				nSamples += patterns.getCount(struct, pattern);
				nPatterns += 1;
			}
			rows.add(new SummaryRow(struct, nSamples, nPatterns));
		}

		Collections.sort(rows, Comparator
			.<SummaryRow>comparingInt(r -> r.nSamples)
			.reversed());

		System.out.print("Found data for these structs:\n\n");

		int longestName = rows.stream()
			.mapToInt(row -> row.struct.getName().length())
			.max()
			.orElse(0);
		int longestSamples = rows.stream()
			.mapToInt(row -> Integer.toString(row.nSamples).length())
			.max()
			.orElse(0);
		int longestPatterns = rows.stream()
			.mapToInt(row -> Integer.toString(row.nPatterns).length())
			.max()
			.orElse(0);

		for (SummaryRow row : rows) {
			String name = Strings.padEnd(row.struct.getName(), longestName, ' ');
			String nSamples = Strings.padStart(Integer.toString(row.nSamples), longestSamples, ' ');
			String nPatterns = Strings.padStart(Integer.toString(row.nPatterns), longestPatterns, ' ');
			System.out.format("%s  %s samples, %s patterns\n", name, nSamples, nPatterns);
		}
	}

	private void printDetails(AccessPatterns patterns, String filterRegex) {
		for (Structure struct : patterns.getStructures()) {
			if (!struct.getName().matches(filterRegex)) {
				continue;
			}

			printOriginal(patterns, struct);
			printOptimized(patterns.optimize(struct));
		}
	}

	private void printOriginal(AccessPatterns patterns, Structure struct) {
		Table table = new Table();
		table.addColumn();

		Map<DataTypeComponent, Integer> rows = new HashMap<>();
		int padding = 0;
		for (DataTypeComponent field : struct.getComponents()) {
			if (field.getDataType().equals(DefaultDataType.dataType)) {
				padding += field.getLength();
			} else {
				if (padding != 0) {
					int row = table.addRow();
					table.get(row, 0)
						.append("\t// char padding[")
						.append(padding)
						.append("];");
					padding = 0;
				}

				int row = table.addRow();
				rows.put(field, row);
				table.get(row, 0)
					.append("\t")
					.append(field.getDataType().getName())
					.append(" ")
					.append(field.getFieldName())
					.append(";");
			}
		}
		if (padding != 0) {
			int row = table.addRow();
			table.get(row, 0)
				.append("\t// char padding[")
				.append(padding)
				.append("];");
		}

		List<AccessPattern> structPatterns = new ArrayList<>(patterns.getPatterns(struct));
		Collections.sort(structPatterns, Comparator
			.<AccessPattern>comparingInt(p -> patterns.getCount(struct, p))
			.reversed());
		for (AccessPattern pattern : structPatterns) {
			int col = table.addColumn();
			for (DataTypeComponent field : pattern.getFields()) {
				table.get(rows.get(field), col)
					.append(patterns.getCount(struct, pattern));
			}
		}

		System.out.print("\nOriginal layout:\n\n");
		System.out.format("struct %s {\n", struct.getName());
		System.out.print(table);
		System.out.print("};\n\n");

		System.out.print("Access patterns:\n\n");
		for (AccessPattern pattern : structPatterns) {
			int count = patterns.getCount(struct, pattern);
			System.out.format("%s (%d times)\n", pattern, count);
		}
	}

	private void printOptimized(Structure struct) {
		System.out.print("\nSuggested layout:\n\n");

		System.out.format("struct %s {\n", struct.getName());
		for (DataTypeComponent field : struct.getComponents()) {
			System.out.format("\t%s %s;\n", field.getDataType().getName(), field.getFieldName());
		}
		System.out.print("};\n\n--\n");
	}
}

/**
 * A properly aligned table.
 */
class Table {
	private final List<List<StringBuilder>> rows = new ArrayList<>();
	private int nCols = 0;

	/**
	 * @return The number of rows.
	 */
	int nRows() {
		return this.rows.size();
	}

	/**
	 * @return The number of columns.
	 */
	int nColumns() {
		return nCols;
	}

	/**
	 * @return The index of the new row.
	 */
	int addRow() {
		List<StringBuilder> row = new ArrayList<>();
		for (int i = 0; i < this.nCols; ++i) {
			row.add(new StringBuilder());
		}
		this.rows.add(row);
		return this.rows.size() - 1;
	}

	/**
	 * Add a new column.
	 */
	int addColumn() {
		for (List<StringBuilder> row : this.rows) {
			row.add(new StringBuilder());
		}
		return this.nCols++;
	}

	/**
	 * @return The StringBuilder in the given cell.
	 */
	StringBuilder get(int row, int col) {
		return this.rows.get(row).get(col);
	}

	@Override
	public String toString() {
		List<Integer> widths = new ArrayList<>();
		for (int i = 0; i < this.nCols; ++i) {
			int width = 0;
			for (List<StringBuilder> row : this.rows) {
				int curWidth = row.get(i).length();
				if (width < curWidth) {
					width = curWidth;
				}
			}
			widths.add(width + 1);
		}

		StringBuilder result = new StringBuilder();
		for (List<StringBuilder> row : this.rows) {
			for (int i = 0; i < this.nCols; ++i) {
				StringBuilder cell = row.get(i);
				result.append(cell);

				int width = widths.get(i);
				for (int j = cell.length(); j < width; ++j) {
					result.append(' ');
				}
			}
			result.append('\n');
		}

		return result.toString();
	}
}

/**
 * Holds the data collected by BCPI.
 */
class BcpiData {
	private final Multiset<Address> data;
	private final Program program;

	private BcpiData(Multiset<Address> data, Program program) {
		this.data = data;
		this.program = program;
	}

	/**
	 * Parse a CSV file generated by bcpiutil.
	 */
	static BcpiData parse(Path csv, Program program) throws IOException {
		Multiset<Address> data = HashMultiset.create();

		try (BufferedReader reader = Files.newBufferedReader(csv)) {
			String line = null;
			while ((line = reader.readLine()) != null) {
				String values[] = line.split(",");
				int count = Integer.parseInt(values[0]);
				Address[] addresses = program.parseAddress(values[1]);
				for (Address address : addresses) {
					data.add(address, count);
				}
			}
		}

		return new BcpiData(data, program);
	}

	/**
	 * @return All the functions that contain an address for which we have data.
	 */
	Set<Function> getRelevantFunctions() {
		Set<Function> functions = new HashSet<>();

		Listing listing = this.program.getListing();
		for (Address address : this.getAddresses()) {
			Function func = listing.getFunctionContaining(address);
			if (func != null) {
				functions.add(func);
			}
		}

		return functions;
	}

	/**
	 * @return All addresses for which we have data.
	 */
	Set<Address> getAddresses() {
		return this.data.elementSet();
	}

	/**
	 * @return The number of events collected for the given address.
	 */
	int getCount(Address address) {
		return this.data.count(address);
	}
}

/**
 * Maps code addresses to the struct field(s) they reference.
 */
class FieldReferences {
	private final Map<Address, Set<DataTypeComponent>> refs = new ConcurrentHashMap<>();
	private final AtomicInteger decompileCount = new AtomicInteger();
	private final Program program;
	private final Set<Function> functions;

	private FieldReferences(Program program, Set<Function> functions) {
		this.program = program;
		this.functions = functions;
	}

	/**
	 * Collect the struct field references in the specified functions.
	 */
	static FieldReferences collect(Program program, Set<Function> functions, TaskMonitor monitor) throws Exception {
		FieldReferences refs = new FieldReferences(program, functions);
		refs.collect(monitor);
		return refs;
	}

	private void collect(TaskMonitor monitor) throws Exception {
		Callback callback = new Callback();
		try {
			decompileFunctions(callback, this.program, this.functions, monitor);
		} finally {
			callback.dispose();
		}

		Msg.info(this, "Decompiled " + this.decompileCount.intValue() + " functions");

		int refCount = 0;
		for (Map.Entry<Address, Set<DataTypeComponent>> entry : this.refs.entrySet()) {
			refCount += entry.getValue().size();
		}
		Msg.info(this, "Found " + refCount + " field references");
	}

	/**
	 * Facade over ParallelDecompiler::decompileFunctions() that handles the API change between
	 * Ghidra 9.1 and 9.2.
	 */
	<R> void decompileFunctions(QCallback<Function, R> callback, Program program, Collection<Function> functions, TaskMonitor monitor) throws Exception {
		MethodHandles.Lookup lookup = MethodHandles.lookup();
		MethodHandle method92 = null;
		MethodHandle method91 = null;
		try {
			MethodType type92 = MethodType.methodType(List.class, QCallback.class, Collection.class, TaskMonitor.class);
			method92 = lookup.findStatic(ParallelDecompiler.class, "decompileFunctions", type92);
		} catch (ReflectiveOperationException e) {
			MethodType type91 = MethodType.methodType(List.class, QCallback.class, Program.class, Collection.class, TaskMonitor.class);
			method91 = lookup.findStatic(ParallelDecompiler.class, "decompileFunctions", type91);
		}

		try {
			if (method92 != null) {
				method92.invoke(callback, functions, monitor);
			} else {
				method91.invoke(callback, program, functions, monitor);
			}
		} catch (Exception e) {
			throw e;
		} catch (Throwable e) {
			throw new Exception(e);
		}
	}

	/**
	 * Get the fields accessed at a particular address.
	 */
	Set<DataTypeComponent> getFields(Address address) {
		return this.refs.getOrDefault(address, Collections.emptySet());
	}

	/**
	 * Based on Ghidra's DecompilerDataTypeReferenceFinder.
	 */
	private class Callback extends DecompilerCallback<Void> {
		Callback() {
			super(program, new DecompilerConfigurer());
		}

		@Override
		public Void process(DecompileResults results, TaskMonitor monitor) {
			processDecompilation(results);
			return null;
		}
	}

	private static class DecompilerConfigurer implements DecompileConfigurer {
		@Override
		public void configure(DecompInterface decompiler) {
			decompiler.toggleCCode(true);
			decompiler.toggleSyntaxTree(true);
			decompiler.setSimplificationStyle("decompile");

			DecompileOptions xmlOptions = new DecompileOptions();
			xmlOptions.setDefaultTimeout(60);
			decompiler.setOptions(xmlOptions);
		}
	}

	/**
	 * Process a single decompiled function.
	 */
	void processDecompilation(DecompileResults results) {
		int count = this.decompileCount.incrementAndGet();
		if (count % 1000 == 0) {
			Msg.info(this, "Decompiled " + count + " functions");
		}

		Function function = results.getFunction();
		if (function.isThunk()) {
			return;
		}

		ClangTokenGroup tokens = results.getCCodeMarkup();
		if (tokens == null) {
			Msg.warn(this, "Failed to decompile " + function.getName());
			return;
		}

		for (ClangLine line : DecompilerUtils.toLines(tokens)) {
			processLine(line);
		}
	}

	/**
	 * Process a single line of a decompiled function.
	 */
	private void processLine(ClangLine line) {
		for (ClangToken token : line.getAllTokens()) {
			if (token instanceof ClangFieldToken) {
				processField((ClangFieldToken) token);
			}
		}
	}

	/**
	 * Process a field access.
	 */
	private void processField(ClangFieldToken token) {
		DataTypeComponent field = getField(token);
		if (field == null || ignoreDataType(field.getParent())) {
			return;
		}

		Address address = getAddress(token);
		this.refs.computeIfAbsent(address, a -> ConcurrentHashMap.newKeySet())
			.add(field);
	}

	/**
	 * Finds the field associated with a ClangFieldToken.
	 */
	private DataTypeComponent getField(ClangFieldToken token) {
		DataType baseType = DecompilerReference.getBaseType(token.getDataType());

		if (baseType instanceof Structure) {
			Structure parent = (Structure) baseType;
			int offset = token.getOffset();
			if (offset >= 0 && offset < parent.getLength()) {
				return parent.getComponentAt(offset);
			}
		}

		return null;
	}

	/**
	 * Finds the address of a field access.
	 */
	private Address getAddress(ClangFieldToken token) {
		// Access DecompilerVariable's protected constructor through an
		// anonymous subclass
		return (new DecompilerVariable(token) {}).getAddress();
	}

	/**
	 * Check if a struct should be processed.  We are looking for non-system
	 * DWARF types.
	 */
	private boolean ignoreDataType(DataType type) {
		String name = type.getPathName();

		if (!name.startsWith("/DWARF/")) {
			return true;
		}

		if (name.contains("/std/")
		    || name.contains("/stdlib.h/")
		    || name.contains("/stdio.h/")
		    || name.contains("/_UNCATEGORIZED_/")) {
			return true;
		}

		return false;
	}
}

/**
 * A set of fields accessed in a block.
 */
class AccessPattern {
	private final Set<DataTypeComponent> fields;

	AccessPattern(Set<DataTypeComponent> fields) {
		this.fields = fields;
	}

	Set<DataTypeComponent> getFields() {
		return this.fields;
	}

	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();

		DataType struct = null;
		for (DataTypeComponent field : this.fields) {
			if (struct == null) {
				struct = field.getParent();
				result.append(struct.getName())
					.append("::{");
			} else {
				result.append(", ");
			}
			result.append(field.getFieldName());
		}

		return result
			.append("}")
			.toString();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == this) {
			return true;
		} else if (!(obj instanceof AccessPattern)) {
			return false;
		}

		AccessPattern other = (AccessPattern) obj;
		return this.fields.equals(other.fields);
	}

	@Override
	public int hashCode() {
		return Objects.hash(fields);
	}
}

/**
 * Struct field access patterns.
 */
class AccessPatterns {
	// Stores the access patterns for each struct
	private final Map<Structure, Multiset<AccessPattern>> patterns = new HashMap<>();
	private final Listing listing;
	private final BasicBlockModel bbModel;
	private final BcpiData data;
	private final FieldReferences refs;

	private AccessPatterns(Program program, BcpiData data, FieldReferences refs) {
		this.listing = program.getListing();
		this.bbModel = new BasicBlockModel(program);
		this.data = data;
		this.refs = refs;
	}

	/**
	 * Infer access patterns from the collected data.
	 */
	static AccessPatterns collect(Program program, BcpiData data, FieldReferences refs, TaskMonitor monitor) throws Exception {
		AccessPatterns patterns = new AccessPatterns(program, data, refs);
		patterns.collect(monitor);
		return patterns;
	}

	private void collect(TaskMonitor monitor) throws Exception {
		for (Address baseAddress : this.data.getAddresses()) {
			Map<Structure, Set<DataTypeComponent>> pattern = new HashMap<>();
			int count = this.data.getCount(baseAddress);

			Set<CodeBlock> blocks = getCodeBlocksFrom(baseAddress, monitor);
			for (CodeBlock block : blocks) {
				for (Address address : block.getAddresses(true)) {
					// Don't count accesses before the miss
					if (block.contains(baseAddress) && address.compareTo(baseAddress) < 0) {
						continue;
					}

					for (DataTypeComponent field : this.refs.getFields(address)) {
						Structure struct = (Structure) field.getParent();
						pattern.computeIfAbsent(struct, k -> new HashSet<>())
							.add(field);
					}
				}
			}

			if (pattern.isEmpty()) {
				Msg.warn(this, "No structure accesses found for " + count + " samples at address " + baseAddress);
			}

			for (Map.Entry<Structure, Set<DataTypeComponent>> entry : pattern.entrySet()) {
				this.patterns.computeIfAbsent(entry.getKey(), k -> HashMultiset.create())
					.add(new AccessPattern(entry.getValue()), count);
			}
		}
	}

	/**
	 * @return All the code blocks that flow from the given address.
	 */
	private Set<CodeBlock> getCodeBlocksFrom(Address address, TaskMonitor monitor) throws Exception {
		// Get all the basic blocks in the function contining the given address
		Function function = this.listing.getFunctionContaining(address);
		if (function == null) {
			return Collections.emptySet();
		}

		AddressSetView body = function.getBody();
		CodeBlockIterator blocks = this.bbModel.getCodeBlocksContaining(body, monitor);

		// Build the control flow graph for that function
		JungDirectedGraph<CodeBlockVertex, CodeBlockEdge> graph = new JungDirectedGraph<>();
		while (blocks.hasNext()) {
			CodeBlock block = blocks.next();
			CodeBlockVertex vertex = new CodeBlockVertex(block);
			graph.addVertex(vertex);

			CodeBlockReferenceIterator dests = block.getDestinations(monitor);
			while (dests.hasNext()) {
				CodeBlockReference dest = dests.next();
				CodeBlock destBlock = dest.getDestinationBlock();
				if (!body.contains(destBlock)) {
					// Ignore non-local control flow
					continue;
				}

				CodeBlockVertex destVertex = new CodeBlockVertex(destBlock);
				graph.addVertex(destVertex);
				graph.addEdge(new CodeBlockEdge(vertex, destVertex));
			}
		}

		// Add a dummy source node in case the whole function is a loop
		CodeBlockVertex dummy = new CodeBlockVertex("SOURCE");
		graph.addVertex(dummy);
		for (CodeBlock entry : this.bbModel.getCodeBlocksContaining(function.getEntryPoint(), monitor)) {
			graph.addEdge(new CodeBlockEdge(dummy, new CodeBlockVertex(entry)));
		}

		// Compute the dominators of the given address
		CodeBlock[] sources = this.bbModel.getCodeBlocksContaining(address, monitor);
		Set<CodeBlock> dominators = new HashSet<>();
		for (CodeBlock source : sources) {
			CodeBlockVertex sourceVertex = new CodeBlockVertex(source);
			Set<?> vertices = GraphAlgorithms.findDominance(graph, sourceVertex, monitor);
			for (Object vertex : vertices) {
				// Work around the issue fixed by https://github.com/NationalSecurityAgency/ghidra/commit/307425c1961e94799e2c1167eabcd749dafcb61d
				if (vertex instanceof CodeBlockVertex) {
					dominators.add(((CodeBlockVertex) vertex).getCodeBlock());
				}
			}
		}
		return dominators;
	}

	/**
	 * @return All the structures about which we have data.
	 */
	Set<Structure> getStructures() {
		return this.patterns.keySet();
	}

	/**
	 * @return All the access patterns we saw for a structure.
	 */
	Set<AccessPattern> getPatterns(Structure struct) {
		return this.patterns.get(struct).elementSet();
	}

	/**
	 * @return The number of occurrences of an access pattern.
	 */
	int getCount(Structure struct, AccessPattern pattern) {
		return this.patterns.get(struct).count(pattern);
	}

	/**
	 * @return The number of accesses we have to this field.
	 */
	private int getCount(DataTypeComponent field) {
		int count = 0;
		Multiset<AccessPattern> patterns = this.patterns.get(field.getParent());
		if (patterns != null) {
			for (Multiset.Entry<AccessPattern> entry : patterns.entrySet()) {
				if (entry.getElement().getFields().contains(field)) {
					count += entry.getCount();
				}
			}
		}
		return count;
	}

	/**
	 * Optimize the layout of a struct according to its access pattern.
	 */
	Structure optimize(Structure struct) {
		List<DataTypeComponent> fields = new ArrayList<>();
		for (DataTypeComponent field : struct.getComponents()) {
			// Skip padding
			if (!field.getDataType().equals(DefaultDataType.dataType)) {
				fields.add(field);
			}
		}

		Collections.sort(fields, Comparator
			.<DataTypeComponent>comparingInt(f -> getCount(f))
			.reversed());

		// Sort the fields by our estimated cost
		StructureDataType optimized = new StructureDataType(struct.getCategoryPath(), struct.getName(), 0);
		for (DataTypeComponent field : fields) {
			optimized.add(field.getDataType(), field.getLength(), field.getFieldName(), field.getComment());
		}
		return optimized;
	}
}
