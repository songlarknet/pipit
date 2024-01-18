# Dockerfile for Pipit
# Based partly on release.Dockerfile from FStar:
# https://github.com/FStarLang/FStar/blob/master/.docker/release.Dockerfile
# The image explicitly uses x86-64 as we download a prebuilt z3 binary:
FROM --platform=linux/amd64 ocaml/opam:debian-12-ocaml-4.14-no-flat-float-array

ENV Z3_URL=https://github.com/tahina-pro/z3/releases/download/z3-4.8.5-linux-clang/z3-4.8.5-linux-clang-x86_64.tar.gz
# ENV Z3_URL=docker/z3.tar.gz

RUN sudo apt-get install libgmp-dev python3 python3-distutils --yes

WORKDIR ./pipit

# Create local switch
RUN opam update
RUN opam switch create . 4.14.1

###### Z3 installation
# Download and extract z3, add it to the path; this release is linked in F* release.Dockerfile
ADD --chown=opam:opam ${Z3_URL} z3/z3.tar.gz
RUN tar xf z3/z3.tar.gz
ENV PATH="/home/opam/pipit/z3:${PATH}"


###### Kind2 installation
RUN sudo apt-get install pkg-config libzmq3-dev --yes
RUN eval $(opam env); opam install kind2


###### FStar+Karamel

# Do not copy _opam and build
COPY --chown=opam:opam submodules submodules

# Remove Z3 dependency from FStar, as we will install it manually
RUN grep -v z3 < submodules/FStar/fstar.opam > submodules/FStar/fstar-no-z3.opam && \
    mv submodules/FStar/fstar-no-z3.opam submodules/FStar/fstar.opam

# Installation takes ~15min
RUN opam pin add fstar file://submodules/FStar --yes
RUN opam pin add karamel file://submodules/karamel --yes

###### Pipit
COPY --chown=opam:opam example example
COPY --chown=opam:opam rts rts
COPY --chown=opam:opam src src
COPY --chown=opam:opam test test
COPY --chown=opam:opam Makefile Makefile

# Run verification.
RUN eval $(opam env); make verify -j8

# Run extraction
# RUN eval $(opam env); make extract -j8

# For benchmark script
RUN sudo apt-get install time --yes
