# Spike 1 (Shen/JIT Phase 0): the smallest JIT shape, for Theorem's process model.
#
# Writes one RV64 function into a code arena at runtime, synchronizes, calls it,
# and exits with its result. The binary is one RWX LOAD segment (rwx.lds), so the
# arena is writable and executable from process start, with no mmap(PROT_EXEC) or
# mprotect(PROT_EXEC), which the model deliberately leaves unmodeled.
#
# Expected behavior on every valid input: no output, exit status 42.
# Hand-written, uncompressed RV64I, so every proof step is visible.

    .option norvc
    .text
    .globl _start
_start:
    auipc a5, %pcrel_hi(arena)
    addi  a5, a5, %pcrel_lo(_start)   # a5 = code arena
    lui   a4, 0x2a00
    addi  a4, a4, 0x513     # a4 = addi a0, zero, 42
    sw    a4, 0(a5)
    lui   a4, 0x8
    addi  a4, a4, 0x67      # a4 = jalr zero, 0(ra)
    sw    a4, 4(a5)
    fence.i                 # no-op in the model; required on real hardware
    jalr  ra, 0(a5)         # run the code written above
    li    a7, 93            # exit
    ecall

    .section .arena, "aw", @progbits
    .balign 16
arena:
    .zero 64
