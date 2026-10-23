.PHONY: bootstrap test prove conformance check report demo
bootstrap:
	./scripts/bootstrap
	./scripts/bootstrap-rocq

test:
	./scripts/check-shen tests/kernel.shen
	./scripts/check-shen tests/evaluator.shen
	./scripts/check-shen tests/wire.shen
	python3 tests/gates.py

prove:
	./scripts/prove
	./scripts/proof-mutations

conformance:
	./scripts/check-shen tests/conformance.shen

check: test prove conformance

report:
	./scripts/report

demo:
	./scripts/shen -l buri.shen -l proofs/compiler.shen -e '(buri.prove)' -e '(buri.normalize [run [compile [add [lit [succ [zero]]] [lit [succ [succ [zero]]]]] [halt]] [nil]] 100)'
