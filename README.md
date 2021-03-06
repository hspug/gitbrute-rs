# gitbrute-rs

Rust clone of https://github.com/bradfitz/gitbrute

It adds two new features:

- Timezone modifications try to change the timezone information before starting to also change the times.
- Partial prefixes are useful if you only want to specify a few bits in a nibble.

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

Cleaning leftover commits
-------------------------
```
$ SKIPBRUTE=y git rebase -i --exec 'gitbrute-rs --prefix a' <first non numbered commit>
$ git reflog expire --expire=0 --all
$ git gc --prune=now
```
