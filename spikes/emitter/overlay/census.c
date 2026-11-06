/* Spike 7 census build: prints every move's operands and emitted bytes. Not the checker. */
#include <stdint.h>
#include <stdio.h>
void spike_check_move_gate(const uint8_t *at, const uint8_t *end, uint32_t dst, uint32_t src, uint32_t homes,
                           uint32_t cached, uint32_t keep)
{
    static FILE *f;
    if (!f) f = fopen("/tmp/move-census.txt", "a");
    fprintf(f, "%u %u %u %d %u %ld ", dst, src, homes, (int)cached, keep, (long)(end - at));
    for (const uint8_t *p = at; p < end; p++) fprintf(f, "%02x", *p);
    fputc('\n', f);
}
