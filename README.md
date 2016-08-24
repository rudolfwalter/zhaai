# Zhaai

This is a toy project, and does not take itself seriously.

## Building:

```bash
gcc -ansi -Wall -Wextra -pedantic-errors -march=native -fno-strict-aliasing  main.c
```

or

```bash
clang -ansi -Weverything -Wno-missing-prototypes -Wno-missing-variable-declarations -Wno-switch-enum -pedantic-errors -march=native -fno-strict-aliasing  main.c
```

In case any of your built-in integer sizes don't match the expectations (see util.h), you can define the fixed-width integers on the command line.

Eg, if your `size_t` is not 64-bit, but you have the `long long` type, add `-Wno-long-long '-Duint64_t=unsigned long long'` to your flags.

