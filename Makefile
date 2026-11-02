.PHONY: bootstrap test prove conformance check report demo check-cl-port check-arm manifest manifest-compare manifest-test
bootstrap:
	./scripts/bootstrap
	./scripts/bootstrap-rocq

test:
	./scripts/check-shen tests/kernel.shen
	./scripts/check-shen tests/evaluator.shen
	./scripts/check-shen tests/wire.shen
	./scripts/check-shen tests/frontend.shen
	./scripts/check-shen tests/trust.shen
	./scripts/check-shen tests/observed.shen
	./scripts/check-shen tests/bindings.shen
	./scripts/check-shen tests/sealed.shen
	./scripts/check-shen tests/constructor.shen
	./scripts/check-shen tests/adapter.shen
	./scripts/check-shen tests/bootstrap.shen
	./scripts/check-shen tests/compilerpass.shen
	./scripts/check-shen tests/checkedio.shen
	./scripts/check-shen tests/correctness.shen
	./scripts/check-shen tests/stages.shen
	./scripts/check-shen tests/equalityseal.shen
	./scripts/check-shen tests/scheme-port-merge.shen
	./scripts/check-shen tests/scheme-port-order.shen
	./scripts/check-shen tests/scheme-compose.shen
	./scripts/check-shen tests/cl-port-guard.shen
	./scripts/check-shen tests/observation.shen
	./scripts/check-shen tests/ledger.shen
	./scripts/check-shen tests/cl-lowering-capture.shen
	./scripts/check-shen tests/primitives.shen
	python3 tests/gates.py

prove:
	@mkdir -p _build
	./scripts/prove > _build/prove.log 2>&1 || { cat _build/prove.log; exit 1; }
	@cat _build/prove.log
	@grep -q '^BURI_ROCQ_OK [0-9][0-9]* audited theorems; ' _build/prove.log || { echo 'make prove: scripts/prove exited 0 without BURI_ROCQ_OK' >&2; exit 1; }
	./scripts/proof-mutations

conformance:
	./scripts/check-shen tests/conformance.shen

check: test prove conformance

report:
	./scripts/report

# Build identity manifest of the last gate run (identity evidence only, not proof).
manifest:
	python3 scripts/build-manifest.py write _build/manifest.json

manifest-compare:
	python3 scripts/build-manifest.py compare $(A) $(B)

manifest-test:
	python3 tests/manifest-gates.py

demo:
	./scripts/shen -l buri.shen -l proofs/compiler.shen -e '(buri.prove)' -e '(buri.normalize [run [compile [add [lit [succ [zero]]] [lit [succ [succ [zero]]]]] [halt]] [nil]] 100)'

# Native source regeneration requires the separately pinned Shen-CL checkout.
check-cl-port:
	./scripts/check-cl-port.sh

# Opt-in ARM model proof (E2E-20); needs SAIL_ARM_COQ and COQ_SAIL (docs/ARM-FOUNDATION.md section 10).
check-arm:
	./scripts/check-arm.sh
