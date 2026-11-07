#!/bin/bash
# Spike 10: CertiRocq (formerly CertiCoq) main 943b52ae654708130f241ccf8a50ecb95a7956e2,
# with MetaRocq branch 9.1 at 51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56, per its INSTALL.md.
set -euxo pipefail
export DEBIAN_FRONTEND=noninteractive OPAMYES=1 OPAMROOTISOK=1 OPAMJOBS=10
apt-get update -qq && apt-get install -y -qq opam git build-essential clang libgmp-dev pkg-config python3 time unzip rsync bubblewrap >/dev/null
opam init -q --disable-sandboxing --bare -y
opam switch create certirocq ocaml-base-compiler.4.14.2 -q
eval $(opam env --switch=certirocq --set-switch)
opam repo add rocq-released https://rocq-prover.org/opam/released
cd /opt && [ -d certirocq ] || git clone -q https://github.com/CertiRocq/certirocq.git
cd certirocq && git checkout -q 943b52ae654708130f241ccf8a50ecb95a7956e2 && git submodule update --init --recursive -q || true
opam pin add --no-action -y git+https://github.com/MetaRocq/metarocq.git#51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56
/usr/bin/time -v opam install --deps-only -y .
./configure.sh
/usr/bin/time -v make -j10
/usr/bin/time -v make plugin
/usr/bin/time -v make cplugin || true
echo CERTIROCQ_READY
