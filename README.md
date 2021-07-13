Continuous Profiler and Analysis Tools
======================================

Installation
------------

Platforms:
 - FreeBSD 12+

Dependencies:
 - Ghidra

Run the following to install dependencies:

```
# pkg install ghidra
```

```
# make
```

Getting Started
---------------

Our bcpid collection daemon can should be run as root and records will be 
placed in `/var/tmp`.  The daemon can also be run in foreground mode for 
testing as with `-f` parameter and you change the output directory using the 
`-o` parameter.

The default counters are picked up `conf/ARCH_NAME.conf` where architecture 
name is displayed in the first line of `pmccontrol -l`.  The configuration file 
accepts pmc formatted comma separated parameters to the counters.  We also 
include two additional parameters `sample_rate` and `label`.

NOTE: Moving forward you should set the label using the standard pmc counter 
names with a few extensions we've made.  Currently we use `instructions`, 
`branches`, `dc-misses`, and `l2dc-misses`.

```
# bcpid/bcpid
```

Extract cache miss samples from the bcpi data in `/var/tmp` and stores them in 
`address_info.csv`.

`COUNTER` means the pmc counter, e.g. `mem_load_retired.l1_miss`

`BINARY` is the path to the executable object to analyze

```
# bcpiquery/bcpiquery extract -c COUNTER -o BINARY
```

At the moment Ghidra requires that you provide a binary with DWARF symbols 
included.  If needed you can merge the symbols and binary using the following 
command:

```
# scripts/merge-debug.sh program program.symbol program.full
```

This will run our cache miss analysis on the addresses generated in the 
previous step and generate a list of structures present in the samples.

WARNING: The first time you run this it may take a substantial amount of time.  
For the FreeBSD kernel with DWARF symbols we usually require 30 minutes for the 
Ghidra to finish the analysis.  Subsequent runs should be on the order of 
seconds.

`Analyze.sh` takes 3 args:
`PATH_TO_PROJECT` -> where to store the ghidra project
`PATH_TO_CSV` -> where to find `address_info.csv` generated by `bcpiquery`
`PATH_TO_BIN` -> where to find the binary

```
# scripts/analyze.sh ./ghidra_projects ./address_info.csv program.full
```

You can also generate a report for a given structure:

```
# scripts/analyze.sh ./ghidra_projects ./address_info.csv program.full structname
```
