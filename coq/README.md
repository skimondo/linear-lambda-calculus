# Coq

## How to run project

### Execute inside coq directory

start by creating a Makefile using coq's congifuration `_CoqProject` file.
In order to use `coq_makefile` command, you need to have `coq` and `make` installed. check [dependencies](#dependencies)

```bash
coq_makefile -f _CoqProject -o Makefile
```

and then compile and run the project

```bash
make
```

Some frequently used `make` commands:

- `make clean`
- `make cleanall` *use this when modifying `_CoqProject` file*
- `make all.pdf`

## Dependencies

```sh
sudo apt-get install make
sudo apt-get install coq
```
