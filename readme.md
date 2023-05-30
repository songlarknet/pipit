# Pipit

Pipit is an embedded language for implementing and verifying *reactive systems*, such as the anti-lock braking system in a car, or the  [system that fills the water reservoir of your coffee machine](https://youtu.be/6IybbQFPOl8).
Pipit is a research project and is in the early stages of development.

Pipit is implemented in  [F\*](https://www.fstar-lang.org/).
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
# Create a local opam switch with OCaml 4.14
opam switch create . 4.14.1

# Tell opam to use the development version of F* but don't install it yet
opam pin add fstar --dev-repo --no-action

# Tell opam where to find the local repo for Karamel and install it and F*
opam pin add karamel --dev-repo --yes
```

### IDE configuration

When using an IDE (Emacs, VSCode), you probably need to specify the exact version of FStar and Z3 binaries to use.


#### VSCode

There are a few VSCode extensions that provide different levels of F\* support; you should use [fstar-vscode-assistant](https://marketplace.visualstudio.com/items?itemName=FStarLang.fstar-vscode-assistant).

If you are using a local `opam` switch, as described above, you may will to tell VSCode the path of your F\* installation.
Copy `template.fst.config.json` to `.fst.config.json`.

#### Emacs

To set up Emacs to use the local `opam` switch, I modified the global fstar options in Emacs.
I modified my `~/.doom.d/config.el` to include:

``` emacs-lisp
(setq-default
  fstar-executable "/Users/amos/proj/songlark/pipit/_opam/bin/fstar.exe"
  fstar-smt-executable "/Users/amos/proj/songlark/pipit/_opam/bin/z3"
  fstar-subp-prover-args
  '("--include" "/Users/amos/proj/songlark/pipit/src"
    "--include" "/Users/amos/proj/songlark/pipit/example"
    "--cache_dir" "/Users/amos/proj/songlark/pipit/build/cache"))
```

(Is it easy to set project-local options in Emacs? It would be convenient if the Emacs fstar-mode read `.fst.config.json` too.)

## Build instructions

Use `make verify` to check the proofs.
Use `make extract` to extract C code for the Pump example; the extracted C code is written to `build/extract`.
The embedded system that actually runs the Pump example is in the [app-pipit-pump repository](https://github.com/songlarknet/app-pipit-pump); it uses the Zephyr RTOS.

