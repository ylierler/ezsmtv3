# EzsmtPlus

## Development Quick Start

Setup build pipeline using cmake:

```sh
mkdir build
cd build
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DCMAKE_BUILD_TYPE=Debug ..
```

Build the project:

``` sh
# In <project_root>/build
cmake --build .
```

Feedback loop: Build, test, run:

``` sh
# In <project_root>/build
cmake --build . && ./test && ./ezsmtPlus -file <some_file>
```

## Build For Release

```

```

## Format All Code

``` sh
clang-format -i src/*.cc src/*.h tests/*.cc
```
