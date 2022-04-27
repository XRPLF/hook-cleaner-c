# Hook Cleaner
Hook Cleaner removes unwanted compiler-provided exports and functions from a wasm binary to make it (more) suitable for being used as a Hook

## Requirements
None, as long as you have any version of
* gcc
* make
* linux
from the past 15 years you can build this.

## Build
```bash
git clone https://github.com/RichardAH/hook-cleaner-c.git
cd hook-cleaner-c
make
```

## Use
```bash
./cleaner accept.wasm
```
