# gitbrute-rs

Rust clone of gitbrute.go

```
USAGE:
    gitbrute-rs [FLAGS] [OPTIONS] --prefix <deadbeef>

FLAGS:
        --force               Re-run, even if current hash matches prefix.
    -h, --help                Prints help information
        --timezone            Allow timezone modifications at 15 minutes granularity.
        --timezone-minutes    Allow timezone modifications at minute granularity.
    -V, --version             Prints version information
        --verbose             Issue diagnostic messages.

OPTIONS:
        --cpus <2>             Number of CPUs to use. Defaults to number of processors.
        --prefix <deadbeef>    Desired prefix.
        --prefix-bits <13>     Number of significant bits in the prefix.
```
