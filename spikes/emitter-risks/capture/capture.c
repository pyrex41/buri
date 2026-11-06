/* Spike 8: runs the real JIT on code objects from a stage 0 file and dumps what it emitted.
   usage: capture FILE.sbc NAME OUT.bin */
#include "../src/runtime/jit.h"
#include "../src/runtime/reader.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
struct block { size_t size; struct block *next; }; /* spikes-overlay/arena.c */
int main(int argc, char **argv)
{
    FILE *f = fopen(argv[1], "rb");
    static char text[1 << 20];
    size_t len = fread(text, 1, sizeof text, f);
    fclose(f);
    VM *vm = vm_create(1 << 16, 1 << 16);
    LoadStats stats = {0};
    const char *error = NULL;
    if (!vm || !jit_init(vm) || !load_stage0(vm, text, len, &stats, &error)) {
        fprintf(stderr, "setup failed: %s\n", error ? error : "VM");
        return 1;
    }
    V fn = *cell_function(vm, symbol_cell(intern_cstr(vm, argv[2])));
    V a[4] = {make_pair(vm, fix(1), fix(2)), fix(5), fix(6), fix(7)};
    V r = jit_call(vm, fn, (size_t)atoi(argv[4]), a);
    printf("run tag=%u\n", tag3(r));
    fn = *cell_function(vm, symbol_cell(intern_cstr(vm, argv[2])));
    uint64_t *clo = ptr(fn);
    uint64_t *code = ptr(clo[CLO_CODE]);
    unsigned char *native = (unsigned char *)(uintptr_t)code[CODE_NATIVE];
    struct block *b = (struct block *)native - 1;
    size_t cand = b->size - sizeof(struct block);
    printf("entry=0x%llx native=0x%llx frame=%lld arity=%lld block=%zu\n", (unsigned long long)clo[PROC_ENTRY],
           (unsigned long long)code[CODE_NATIVE], (long long)code[CODE_FRAME], (long long)code[CODE_ARITY], cand);
    printf("offsets hp=%zu hlimit=%zu fp=%zu top=%zu stack_limit=%zu count=%zu args=%zu\n", offsetof(VM, hp),
           offsetof(VM, hlimit), offsetof(VM, fp), offsetof(VM, top), offsetof(VM, stack_limit),
           offsetof(VM, count), offsetof(VM, args));
    printf("vm=0x%llx compile_stub=0x%llx\n", (unsigned long long)(uintptr_t)vm, (unsigned long long)(uintptr_t)vm->compile_stub);
    FILE *o = fopen(argv[3], "wb");
    fwrite(native, 1, cand, o);
    fclose(o);
    return 0;
}
