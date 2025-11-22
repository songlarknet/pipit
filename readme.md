# Pipit

Pipit is an embedded language for implementing and verifying *reactive systems*, such as the anti-lock braking system in a car, or the  [system that fills the water reservoir of your coffee machine](https://youtu.be/6IybbQFPOl8).
Pipit is a research project and is in the early stages of development.

Pipit is implemented in  [F\*](https://www.fstar-lang.org/).
The language is strongly inspired by Lustre.
The verification system is inspired by the [Kind2 model checker](https://github.com/kind2-mc/kind2/) and related work.
By embedding Pipit in a theorem prover, we aim to have an expressive language with a small verifiable core.
Pipit reuses F\*'s proof automation for proving properties of programs.
We also reuse F\*'s C code generation to generate real-time code.

The Pipit library is in the `pipit` subdirectory and is divided into components:
* `source`: the source language, which provides some syntactic niceties for writing programs (`Pipit.Sugar`);
* `core`: the core expression language, which provides a bigstep semantics (`Pipit.Exp` and submodules);
* `abstract`: transition systems, which are used for reasoning about programs (`Pipit.System` and submodules); and
* `extract`: executable systems, which are used for compiling to C code (`Pipit.System.Exec` and submodules).

Programs written in the core language are translated to a transition system for verification; this translation is verified (it is an abstraction).
The translation to executable systems is verified (it is an equivalence).
The details of the formalisation and proofs are available in the [implementation notes](src/readme.md).

There are examples available in the `example` subdirectory ([readme](example/readme.md)).

## Dependencies and development

Pipit requires F\* and Karamel for generating C code.
Pipit uses [opam](https://opam.ocaml.org/), the OCaml package manager.

Pipit requires a recent development version of F\*.
We maintain a fork with the right version at [https://github.com/songlarknet/FStar/tree/pipit](songlarknet/FStar).

### Dependency installation

Before setting up a local development environment, make sure you have [opam](https://opam.ocaml.org/) and Python 2.7 installed.
If you are running a modern Linux distribution, such as the latest release of Ubuntu (23.04), you may need to [install Python 2.7 manually (see below)](#modern-linux-no-python-27).

The makefile target `make dev-init` will initialise a local development environment.
This will print a message telling you which versions of Z3 to install.
You can install them by running [FStar:.scripts/get_fstar_z3](https://github.com/FStarLang/FStar/blob/master/.scripts/get_fstar_z3.sh).

#### MacOS

To build on MacOS, you need to install these prerequisites:
```
brew install gmp
brew install coreutils
```

I also needed to set Python3 to use an older version, as 3.12 removes a `distutils` module. I ran:
```
brew install pyenv
pyenv global 3.9.15
```

### IDE configuration

#### VSCode

There are a few VSCode extensions that provide different levels of F\* support, but you should use [fstar-vscode-assistant](https://marketplace.visualstudio.com/items?itemName=FStarLang.fstar-vscode-assistant).

The local configuration in `pipit.fst.config.json` will use the local `opam` switch described above. If you've run `make dev-init`, the editor integration should be able to load the F* files without any changes.

## Build instructions

Use `make -j8` to check the proofs. This will also extract C code for the Pump example.

The embedded system that actually runs the Pump example is in the [app-pipit-pump repository](https://github.com/songlarknet/app-pipit-pump); it uses the Zephyr RTOS.

