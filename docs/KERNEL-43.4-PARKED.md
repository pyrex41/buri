# Kernel 43.4 for the Shen-Scheme/Shen-CL lanes: parked (6 Nov 2026)

Decision (Reuben): full move eventually, parked for now; focus on Shen/JIT.

- Only Shen-Scheme v0.54 (c9ed732c) embeds 43.4; linux-x64 sha256 4a3805e2...57ef.
- v0.54 changes lowering: simple-error -> error + shen-string->unicode; assert-boolean inlined
  with shen-boolean-error; numeric-literal equality; cond gets else failure clause.
- 19 of 24 captures change shape; 17 hand-written Rocq modules give assert-boolean meaning;
  gensym names hard-coded in OrderCallPass.v:245-335, OrderCallProgress.v:259.
- Tests on v0.54: 23/26 pass (sealed, scheme-compose, primitives fail).
- Shen-CL: no 43.4 release (master 188c9a6 still 43.1).
- Existing mismatch: host_source_reviewed 8d261518 is in v0.53/v0.54, not v0.52; 21 lines differ
  from the pinned v0.52 binary's sources. Pin docs should say so.
- Plan: (1) decide CL; (2) pins+charter v3; (3) re-vendor+re-extract; (4) extend Scheme-subset
  model; (5) restate/re-prove by module family (bulk, several agent-days); (6) rebase patches,
  close upstream-fixed obligations; (7) sealed capsule helpers; (8) recapture + full gate.
Evidence was gathered on macOS-arm64 scratch copies of 64f6f89, not the linux-x64 gate route; logs were not kept in the repository.
