package bcpi;

import ghidra.program.model.address.Address;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Program;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multiset;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Holds the data collected by BCPI.
 */
public class BcpiData {
	private final Map<Address, BcpiDataRow> rows;

	private BcpiData(Map<Address, BcpiDataRow> rows) {
		this.rows = ImmutableMap.copyOf(rows);
	}

	/**
	 * Parse a CSV file generated by bcpiutil.
	 */
	public static BcpiData parse(Path csv, List<Program> programs) throws IOException {
		Map<Address, BcpiDataRow> rows = new HashMap<>();

		try (BufferedReader reader = Files.newBufferedReader(csv)) {
			String line = null;
			while ((line = reader.readLine()) != null) {
				String[] values = line.split(",");

				for (Program program : programs) {
					Address address = program.getAddressFactory().getAddress(values[0]);
					if (address == null) {
						continue;
					}

					Function function = program.getListing().getFunctionContaining(address);
					if (function == null) {
						continue;
					}

					Multiset<String> counters = HashMultiset.create();
					for (int i = 1; i < values.length; ++i) {
						String[] kv = values[i].split("=");
						counters.add(kv[0], Integer.parseInt(kv[1]));
					}
					rows.put(address, new BcpiDataRow(address, program, function, counters));
					break;
				}
			}
		}

		return new BcpiData(rows);
	}

	/**
	 * @return All the functions that contain an address for which we have data.
	 */
	public Set<Function> getFunctions() {
		return this.rows.values()
			.stream()
			.map(row -> row.function)
			.collect(Collectors.toSet());
	}

	/**
	 * @return All addresses for which we have data.
	 */
	public Set<Address> getAddresses() {
		return this.rows.keySet();
	}

	/**
	 * @return The number of events collected for the given address and counter.
	 */
	public int getCount(Address address, String counter) {
		BcpiDataRow row = this.rows.get(address);
		if (row == null) {
			return 0;
		} else {
			return row.getCount(counter);
		}
	}

	/**
	 * @return All the data.
	 */
	public Collection<BcpiDataRow> getRows() {
		return this.rows.values();
	}

	/**
	 * @return The row associated with the given address, or null.
	 */
	public BcpiDataRow getRow(Address address) {
		return this.rows.get(address);
	}
}
