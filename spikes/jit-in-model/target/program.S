# Comparison binary: no generated code, ordinary immutable text. Exit status 42.
    .option norvc
    .text
    .globl _start
_start:
    li    a0, 42
    li    a7, 93
    ecall
