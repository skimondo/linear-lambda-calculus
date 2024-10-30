# Coq

## How to run project

*Execute inside coq directory* [source](https://coq.inria.fr/doc/V8.18.0/refman/practical-tools/utilities.html)

to create a Makefile from `_CoqProject` file

```bash
coq_makefile -f _CoqProject -o Makefile
```

to build the project

```bash
make
```

Some frequently used `make` commands:

- `make clean`
- `make all.pdf`
