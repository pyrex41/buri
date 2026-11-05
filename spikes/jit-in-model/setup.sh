set -eu
set -o pipefail
export DEBIAN_FRONTEND=noninteractive OPAMYES=1 OPAMROOTISOK=1
apt-get update -qq >/dev/null
apt-get install -y -qq opam python3 make gcc g++ git curl unzip bubblewrap m4 pkg-config libgmp-dev zlib1g-dev rsync patch gcc-riscv64-linux-gnu binutils-riscv64-linux-gnu qemu-user musl-tools strace >/dev/null 2>&1
echo STEP apt-done
opam init --disable-sandboxing --bare --no-setup >/dev/null 2>&1
opam switch create lps 5.2.1 >/dev/null 2>&1
eval "$(opam env --switch=lps --set-switch)"
opam repo add rocq-released https://rocq-prover.org/opam/released >/dev/null 2>&1
opam install -y 'dune>=3.23' 'rocq-core>=9.2' rocq-stdlib 'rocq-stdpp>=1.13.0' rocq-stdpp-bitvector 'coq-flocq>=4.2' rocq-read-file 2>&1 | tail -4
rocq --version; echo STEP opam-done
cp -a /lps/src /work && cd /work
dune build theories/Riscv theories/LinuxProcessSem theories/EquivalenceDefinition -j5 2>&1 | tail -5
echo STEP core-done
dune build theories/Common -j5 2>&1 | tail -5
echo STEP common-done
dune build theories/Examples/rwx_flag_ns -j5 2>&1 | tail -5
echo STEP rwx-example-done
touch /lps/READY; sleep infinity
