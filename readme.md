# Pipit

Pipit is an embedded language for implementing and verifying *reactive systems*, such as the anti-lock braking system in a car, or the  [system that fills the water reservoir of your coffee machine](https://youtu.be/6IybbQFPOl8).
Pipit is a research project and is in the early stages of development.

Pipit is implemented in  [F*](https://www.fstar-lang.org/).
The language is strongly inspired by Lustre.
The verification system is inspired by the [Kind2 model checker](https://github.com/kind2-mc/kind2/) and related work.
By embedding Pipit in a theorem prover, we aim to have an expressive language with a small verifiable core.
Pipit reuses F\*'s proof automation for proving properties of programs.
We also reuse F\*'s C code generation to generate real-time code.

The Pipit library is in the `src` subdirectory and has four main pieces:
* the source language, which provides some syntactic niceties for writing language (`Pipit.Sugar`);
* the core expression language, which provides a bigstep semantics (`Pipit.Exp` and submodules);
* transition systems, which is used for reasoning about programs (`Pipit.System` and submodules); and
* executable systems, which are used for compiling to C code (`Pipit.Exec` and submodules).

Programs written in the core language are translated to a transition system for verification; this translation is verified (it preserves semantics).
The translation to executable systems preserves types, but is not yet verified to preserve semantics.
The details of the formalisation and proofs are available in the [implementation notes](src/readme.md).

There are examples available in the `example` subdirectory ([readme](example/readme.md)).

## Dependencies and development

Pipit requires F\* and Karamel for generating C code.
Pipit indirectly requires [opam](https://opam.ocaml.org/), the OCaml package manager. 

Pipit requires a recent development version of F\*; I usually install it from source, available at [FStar on github](https://github.com/FStarLang/FStar).
(TODO: I am using version F* 2023.04.08~dev; test with a released version)

Karamel can be installed from source at [karamel on github](https://github.com/FStarLang/karamel/).

### Dependency installation

The following script should set up an environment.
Make sure you have [opam](https://opam.ocaml.org/) installed.
Run this from the Pipit directory:

``` sh
# Create a directory for the build environment
mkdir -p build/env; cd build/env

# Create a local opam switch with OCaml 4.14
opam switch create . 4.14.1

# git clone https://github.com/FStarLang/karamel

# Is it necessary to check out a specific commit of F*?
# git clone https://github.com/FStarLang/FStar
# cd FStar; git checkout 5a15885098c69006bb56ff2712534fe75a5fd839; cd ..

# Tell opam to use the development version of F* (but don't install it yet)
opam pin add fstar --dev-repo --no-action

# Tell opam where to find the local repo for Karamel (and install it and F*)
opam pin add karamel --dev-repo --yes
```

### IDE configuration

When using an IDE (Emacs, VSCode), you might need to specify the exact version of FStar and Z3 binaries to use.


#### VSCode

There are a few VSCode extensions that provide different levels of F\* support; you should use [fstar-vscode-assistant](https://marketplace.visualstudio.com/items?itemName=FStarLang.fstar-vscode-assistant).

You may need to tell VSCode the path of your F\* installation.
Copy `template.fst.config.json` to `.fst.config.json` and modify it to include the path to `fstar.exe` as necessary.

If you have multiple versions of Z3 installed, you will probably also have to specify the path to the F\*-compatible Z3 with the `--smt /.../bin/z3` option.
For example, my `.fst.config.json` is:

```json
{ "fstar_exe":"/Users/amos/proj/ext/fstar/_opam/bin/fstar.exe",
  "options":["--smt", "/Users/amos/proj/ext/fstar/_opam/bin/z3", "--cache_dir", ".cache.boot"],
  "include_dirs":["src","example"]
}
```

#### Emacs

Emacs

``` emacs-lisp
(setq-default
  fstar-executable "/Users/amos/proj/ext/fstar/_opam/bin/fstar.exe"
  fstar-smt-executable "/Users/amos/proj/ext/fstar/_opam/bin/z3")
```

