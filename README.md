# ViCAR

**Vi**sualizing **C**ategories with **A**utomated **R**ewriting in Coq

### **ACT Submission: See [this](https://github.com/inQWIRE/ViCaR/releases/tag/act-submission) tag**

## Building ViCAR

Currently supports Coq 8.16-8.19.

To build ViCaR, run `make vicar`.

## Installing ViCAR through opam

To install ViCAR through opam, run 
```bash
opam pin -y coq-vicar https://github.com/inQWIRE/ViCAR.git
```

To use the visualizer, first have [coq-lsp](https://github.com/ejgallego/coq-lsp) installed, then install the VSCode extension found at [https://marketplace.visualstudio.com/items?itemName=inQWIRE.vizcar]. After instantiating the appropriate typeclass you would like to visualize you can run the vizcar command in vscode to activate visualizing. The vizcar plugin only visualizes terms using the ViCAR grammar. To automatically take a term to the ViCAR grammar, use the `categorify` tactic.

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
opam pin -y coq-vyzx https://github.com/inQWIRE/VyZX.git#category-abstraction
```

Then install [ViCaR](https://github.com/inQWIRE/ViCaR) while in the directory by running

```bash
opam pin -y coq-vicar ./
```

then run

```bash
make examples
```
