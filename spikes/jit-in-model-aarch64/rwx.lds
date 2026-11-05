/* One RWX LOAD segment holding ELF headers, code, and the runtime code arena.
   Same layout as spikes/jit-in-model/rwx.lds. */
PHDRS { seg PT_LOAD FLAGS(7) FILEHDR PHDRS; }
ENTRY(_start)
SECTIONS {
  . = 0x10000 + SIZEOF_HEADERS;
  . = ALIGN(4);
  .text : { *(.text*) } :seg
  .rodata : { *(.rodata*) }
  .data : { *(.data*) }
  . = ALIGN(64);
  .arena : { *(.arena) }
  .bss : { *(.bss*) *(COMMON) }
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
