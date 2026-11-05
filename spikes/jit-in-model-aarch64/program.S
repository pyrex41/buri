// AArch64 counterpart of spikes/jit-in-model/program.S (Shen/JIT Phase 0).
//
// Writes one function into a code arena at runtime, does the cache maintenance
// the architecture requires for code that was just written, calls it, and exits
// with its result. One RWX LOAD segment (rwx.lds), with no mmap or mprotect.
//
// Expected behavior on every valid input: no output, exit status 42.
// Pass -DNO_SYNC to leave out the maintenance: the proof must be able to tell
// that binary apart, because real hardware may then run stale instructions.

    .text
    .globl _start
_start:
    adr   x5, arena
    movz  w4, #0x0540            // low half of: mov w0, #42 (0x52800540)
    movk  w4, #0x5280, lsl #16
    str   w4, [x5]
    movz  w4, #0x03c0            // low half of: ret (0xd65f03c0)
    movk  w4, #0xd65f, lsl #16
    str   w4, [x5, #4]
#ifndef NO_SYNC
    dc    cvau, x5               // clean the data cache to the point of unification
    dsb   ish
    ic    ivau, x5               // invalidate the instruction cache
    dsb   ish
    isb                          // discard anything already fetched
#endif
    blr   x5                     // run the code written above
    mov   x8, #93                // exit
    svc   #0

    .section .arena, "aw", @progbits
    .balign 64
arena:
    .zero 64
