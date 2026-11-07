#!/bin/bash
# Spike 10: Poly/ML + HOL4 + CakeML v3479 in a fresh ubuntu:24.04 (arm64) container.
# Pins: CakeML v3479 = e8eca63affd1653105ca4b9cc2f5ca87a01cd0af, whose release notes name
# HOL trindemossen-2-v6 = a390cbabd3a4521bab4ee20281e3e42933a8a3ae. Poly/ML v5.9.1.
set -euxo pipefail
export DEBIAN_FRONTEND=noninteractive
apt-get update -qq && apt-get install -y -qq git build-essential libgmp-dev ca-certificates time >/dev/null
cd /opt
[ -d polyml ] || git clone -q --depth 1 -b v5.9.1 https://github.com/polyml/polyml
cd polyml && ./configure -q --prefix=/usr --enable-intinf-as-int >/dev/null && make -s -j10 >/dev/null && make -s compiler >/dev/null && make -s install >/dev/null
cd /opt
[ -d HOL ] || { git clone -q https://github.com/HOL-Theorem-Prover/HOL && (cd HOL && git checkout -q a390cbabd3a4521bab4ee20281e3e42933a8a3ae); }
cd HOL && poly --script tools/smart-configure.sml && /usr/bin/time -v bin/build -j 10
cd /opt
[ -d cakeml ] || { git clone -q https://github.com/CakeML/cakeml && (cd cakeml && git checkout -q e8eca63affd1653105ca4b9cc2f5ca87a01cd0af); }
echo HOL_READY
