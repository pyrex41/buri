/* One RWX LOAD segment holding ELF headers, code, and the runtime code arena.
   Adapted from Theorem's theories/Examples/rwx_flag_ns/source/rwx.lds. */
PHDRS { seg PT_LOAD FLAGS(7) FILEHDR PHDRS; }
ENTRY(_start)
SECTIONS {
  . = 0x10000 + SIZEOF_HEADERS;
  . = ALIGN(4);
  .text : { *(.text*) } :seg
  .rodata : { *(.rodata*) *(.srodata*) }
  .data : { *(.data*) *(.sdata*) }
  . = ALIGN(16);
  .arena : { *(.arena) }
  .bss : { *(.bss*) *(.sbss*) *(COMMON) }
  /DISCARD/ : { *(.comment) *(.note*) *(.riscv.attributes) *(.eh_frame*) }
}
