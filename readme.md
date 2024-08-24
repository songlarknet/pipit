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
* the source language, which provides some syntactic niceties for writing programs (`Pipit.Sugar`);
* the core expression language, which provides a bigstep semantics (`Pipit.Exp` and submodules);
* transition systems, which are used for reasoning about programs (`Pipit.System` and submodules); and
* executable systems, which are used for compiling to C code (`Pipit.System.Exec` and submodules).

Programs written in the core language are translated to a transition system for verification; this translation is verified (it is an abstraction).
The translation to executable systems is verified (it is an equivalence).
The details of the formalisation and proofs are available in the [implementation notes](src/readme.md).

There are examples available in the `example` subdirectory ([readme](example/readme.md)).

## Dependencies and development

Pipit requires F\* and Karamel for generating C code.
Pipit uses [opam](https://opam.ocaml.org/), the OCaml package manager.

Pipit requires a recent development version of F\*.
We maintain a fork with the right version at [https://github.com/songlarknet/FStar/tree/pipit](songlarknet/FStar).
This fork currently has some minor improvements to avoid duplication of work during code-generation, which we expect to be integrated upstream in the near future.

### Dependency installation

Before setting up a local development environment, make sure you have [opam](https://opam.ocaml.org/) and Python 2.7 installed.
If you are running a modern Linux distribution, such as the latest release of Ubuntu (23.04), you may need to [install Python 2.7 manually (see below)](#modern-linux-no-python-27).

The makefile target `make dev-init` will initialise a local development environment.
This target runs the following commands:
``` sh
# Make sure the opam index is up-to-date
opam update

# Create a local opam switch with OCaml 4.14
opam switch create . 4.14.1

# Initialise git submodules (FStar and Karamel)
git submodule update --init

# Tell opam to use the development version of F* but don't install it yet
opam pin add fstar file://submodules/FStar --no-action

# Tell opam where to find the local repo for Karamel and install it and F*
opam pin add karamel file://submodules/karamel --yes
```
#### Modern Linux (no Python 2.7)

The opam package for the Z3 SMT solver requires Python 2.7.
Unfortunately, the latest release of Ubuntu (23.04) no longer includes packages for Python 2.
I had the most luck installing from source.
Run the following in a temporary directory in which you'd like to build Python:

```
cd $TMP
wget https://www.python.org/ftp/python/2.7.16/Python-2.7.16.tgz
tar xvzf Python-2.7.16.tgz
cd Python-2.7.16
./configure --enable-optimizations
make -j8
sudo make install
```

Then, you can install Z3 and other dependencies as follows.
The `--no-depexts` flag is important: it tells opam not to care that the `python-2.7` apt package is missing.
```
cd $PIPIT
opam update
opam switch create . 4.14.1
opam pin add fstar file://submodules/FStar --no-action
opam pin add karamel file://submodules/karamel --yes
```

#### MacOS

To build on MacOS, you need to install these prerequisites:
```
brew install gmp
brew install coreutils
```

### IDE configuration

When using an IDE (Emacs, VSCode), you probably need to specify the exact version of FStar and Z3 binaries to use.


#### VSCode

There are a few VSCode extensions that provide different levels of F\* support; you should use [fstar-vscode-assistant](https://marketplace.visualstudio.com/items?itemName=FStarLang.fstar-vscode-assistant).

If you are using a local `opam` switch as described above, you may want to tell VSCode the path of your F\* installation:
copy `template.fst.config.json` to `.fst.config.json`.

## Build instructions

Use `make verify -j8` to check the proofs.
Use `make extract -j8` to extract C code for the Pump example; the extracted C code is written to `build/extract`.
The embedded system that actually runs the Pump example is in the [app-pipit-pump repository](https://github.com/songlarknet/app-pipit-pump); it uses the Zephyr RTOS.

