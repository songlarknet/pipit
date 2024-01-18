# Dockerfile for Pipit
# Based partly on release.Dockerfile from FStar:
# https://github.com/FStarLang/FStar/blob/master/.docker/release.Dockerfile
# The image explicitly uses x86-64 as we download a prebuilt z3 binary:
FROM --platform=linux/amd64 ocaml/opam:debian-12-ocaml-4.14-no-flat-float-array

# ENV Z3_URL=https://github.com/tahina-pro/z3/releases/download/z3-4.8.5-linux-clang/z3-4.8.5-linux-clang-x86_64.tar.gz
ENV Z3_URL=docker/z3.tar.gz

RUN sudo apt-get install libgmp-dev python3 python3-distutils --yes

WORKDIR ./pipit

# Do not copy _opam and build
COPY --chown=opam:opam submodules submodules
COPY --chown=opam:opam example example
COPY --chown=opam:opam rts rts
COPY --chown=opam:opam src src
COPY --chown=opam:opam test test
COPY --chown=opam:opam Makefile Makefile


# Remove Z3 dependency from FStar, as we will install it manually
RUN grep -v z3 < submodules/FStar/fstar.opam > submodules/FStar/fstar-no-z3.opam && \
    mv submodules/FStar/fstar-no-z3.opam submodules/FStar/fstar.opam

# Download and extract z3, add it to the path; this release is linked in F* release.Dockerfile
ADD --chown=opam:opam ${Z3_URL} z3/z3.tar.gz
RUN tar xf z3/z3.tar.gz
ENV PATH="/home/opam/pipit/z3:${PATH}"

# Create local switch
RUN opam update
RUN opam switch create . 4.14.1

# Installation takes ~15min
RUN opam pin add fstar submodules/FStar --yes
RUN opam pin add karamel submodules/karamel --yes

# Run verification. This is very slow and seems to ignore the -j8 - why?
RUN eval $(opam env); make verify -j8
# Docker (on my M1 Mac) is a bit slower:
# > real	13m29.993s
# > user	25m2.931s
# > sys 	0m27.907s

# Run extraction
RUN eval $(opam env); make extract -j8
# > real	0m26.726s
# > user	0m36.220s
# > sys	0m1.759s
