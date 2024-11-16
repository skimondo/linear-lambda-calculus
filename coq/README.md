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
- `make cleanall` *use this after modifying `_CoqProject` file*
- `make all.pdf`

## Contributing

In order to use the full power of Coq, using an IDE that can run tactics and proofs interactively is the best way to go.

Using `vscoq` extension for vscode is recommended. any other IDE that supports Coq will do too, like `Proof General` for Emacs.

### Setup LSP server in vscode

#### Make sure you have `opam` installed and up-to-date

```shell
opam update
opam upgrade
```

#### Install `coq-lsp` using `opam`

```shell
opam install coq-lsp
```

#### Install `vscoq` extension in vscode (Instructions taken from [vscoq](https://github.com/coq/vscoq))

To install the VS Code or VSCodium extension, first run code or codium. Then press F1 to open the command palette, start typing "Extensions: Install Extension", press enter, and search for "vscoq".
Finally, go to the extension settings and enter the vscoqtop full path from above in the field "Vscoq: Path".

```shell
which coqtop
```

If you want asynchronous processing of Coq files, you can go to the "Proof: Mode" and select "Continuous". Otherwise, processing will step by step and top-down as in VsCoq1.

## Dependencies

```sh
sudo apt-get install make
sudo apt-get install coq
```
