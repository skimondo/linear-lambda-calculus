# Coq

## How to run project

*Execute inside coq directory,* for more info check [here](https://coq.inria.fr/doc/V8.18.0/refman/practical-tools/utilities.html)

start by creating a Makefile using coq's congifuration `_CoqProject` file

```bash
coq_makefile -f _CoqProject -o Makefile
```

and the compile and run the project

```bash
make
```

Some frequently used `make` commands:

- `make clean`
- `make all.pdf`

