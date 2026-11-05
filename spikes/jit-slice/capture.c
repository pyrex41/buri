/* Spike 4: runs the real JIT on one code object and dumps exactly what it emitted.
   Compile with the same objects and flags as the arena build of runtime. */
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
    static char text[1 << 16];
    size_t len = fread(text, 1, sizeof text, f);
    fclose(f);
    VM *vm = vm_create(1 << 16, 1 << 16);
    LoadStats stats = {0};
    const char *error = NULL;
    if (!vm || !jit_init(vm) || !load_stage0(vm, text, len, &stats, &error)) {
        fprintf(stderr, "setup failed: %s\n", error ? error : "VM");
        return 1;
    }
    V fn = *cell_function(vm, symbol_cell(intern_cstr(vm, "sl.f")));
    /* Two runs through the real entry: a pair (fast path), then a non-pair (error). */
    V pair = make_pair(vm, fix(1), fix(2));
    V a1[2] = {pair, fix(5)};
    V r = jit_call(vm, fn, 2, a1);
    printf("run-ok tag=%u hd=%lld tl=%lld\n", tag3(r), (long long)fixval(ptr(r)[0]), (long long)fixval(ptr(r)[1]));
    V a2[2] = {fix(7), fix(5)};
    V e = jit_call(vm, fn, 2, a2);
    printf("run-err is_cleared=%d\n", e == V_CLEARED);

    /* Third run: no room left, so the allocation's slow path runs for real. */
    pair = make_pair(vm, fix(3), fix(4));
    fn = *cell_function(vm, symbol_cell(intern_cstr(vm, "sl.f")));
    size_t before = vm->collections;
    vm->hlimit = vm->hp;
    V a3[2] = {pair, fix(6)};
    r = jit_call(vm, fn, 2, a3);
    printf("run-slow tag=%u hd=%lld tl=%lld collections=%zu\n", tag3(r), (long long)fixval(ptr(r)[0]), (long long)fixval(ptr(r)[1]), vm->collections - before);

    fn = *cell_function(vm, symbol_cell(intern_cstr(vm, "sl.f")));
    uint64_t *clo = ptr(fn);
    uint64_t *code = ptr(clo[CLO_CODE]);
    unsigned char *native = (unsigned char *)(uintptr_t)code[CODE_NATIVE];
    printf("entry_in_closure=0x%llx native=0x%llx frame=%lld arity=%lld\n",
           (unsigned long long)clo[PROC_ENTRY], (unsigned long long)code[CODE_NATIVE],
           (long long)code[CODE_FRAME], (long long)code[CODE_ARITY]);
    struct block *b = (struct block *)native - 1;
    size_t cand = b->size - sizeof(struct block);
    printf("block_size=%zu\n", cand);
    printf("offsets hp=%zu hlimit=%zu fp=%zu top=%zu stack_limit=%zu check_limit=%zu count=%zu args=%zu sizeofV=%zu\n",
           offsetof(VM, hp), offsetof(VM, hlimit), offsetof(VM, fp), offsetof(VM, top),
           offsetof(VM, stack_limit), offsetof(VM, check_limit), offsetof(VM, count), offsetof(VM, args), sizeof(V));
    printf("vm=0x%llx compile_stub=0x%llx foreign_stub=0x%llx\n", (unsigned long long)(uintptr_t)vm,
           (unsigned long long)(uintptr_t)vm->compile_stub, (unsigned long long)(uintptr_t)vm->foreign_stub);
    FILE *o = fopen(argv[2], "wb");
    fwrite(native, 1, cand, o);
    fclose(o);
    return 0;
}
