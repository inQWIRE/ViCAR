# ViCaR

Verified Categorical String Diagrams in Roq

## Building ViCaR

Tested with Coq 8.14-8.18.

To build ViCaR, run `make vicar`


## Examples

For examples to compile, do the following. Note: Examples only compile on coq >= 8.16

First, install [QuantumLib](https://github.com/inQWIRE/QuantumLib) through opam.

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-quantumlib
```

Then install [SQIR and VOQC](https://github.com/inQWIRE/SQIR)

```bash
opam pin -y coq-sqir https://github.com/inQWIRE/SQIR.git
opam pin -y coq-voqc https://github.com/inQWIRE/SQIR.git
```

Then install [VyZX](https://github.com/inQWIRE/VyZX)

```bash
opam pin -y coq-vicar https://github.com/inQWIRE/VyZX.git
```

Then install [ViCaR](https://github.com/inQWIRE/ViCaR) while in the directory by running

```bash
opam pin -y coq-vicar ./
```

then run

```bash
make examples
```
