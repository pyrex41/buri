/* Spike 7, route B: checks the bytes emitted for one (move D S) against its template.
   spike_check_move is a leaf with no stores; its compiled bytes are what coq/ proves.
   Returns 1 if [at, end) is exactly a template of this move, 0 if not, and 2 if the
   operands are outside the checker's domain, so nothing was checked.
   The arguments are wide so that the contract has no premise about register extension. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define NONE 0xffffffffu
#define C_MV(rd, rs) (0x8002u | (uint64_t)(rd) << 7 | (uint64_t)(rs) << 2)
/* Compressed ld and sd of a0 at off(s0). */
#define C_OFF(off) (((off) & 0x38) << 7 | ((off) & 0xc0) >> 1 | 8u)
#define C_LD_A0(off) (0x6000u | C_OFF(off))
#define C_SD_A0(off) (0xe000u | C_OFF(off))
/* Full ld rd, off(s0) and sd a0, off(s0). */
#define LD_S0(rd, off) ((off) << 20 | 8u << 15 | 3u << 12 | (uint64_t)(rd) << 7 | 3u)
#define SD_A0(off) (((off) >> 5) << 25 | 10u << 20 | 8u << 15 | 3u << 12 | ((off) & 31) << 7 | 0x23u)

__attribute__((noinline))
uint64_t spike_check_move(const uint16_t *at, const uint16_t *end, uint64_t dst, uint64_t src,
                          uint64_t homes, uint64_t cached, uint64_t keep)
{
    uint64_t w, n, s, ns, off;
    if (dst > 255 || src > 255 || homes > 6 || keep > 1)
        return 2;
    if (homes != 0 && cached != NONE)
        return 2;
    off = src * 8;
    if (dst >= 2 && dst < homes + 2) { /* to_home: straight into dst's register */
        uint64_t rd = 18 + dst;
        if (keep)
            return 0;
        if (src >= 2 && src < homes + 2) {
            if (src == dst)
                return end == at;
            w = C_MV(rd, 18 + src);
            n = 1;
        } else {
            w = LD_S0(rd, off);
            n = 2;
        }
        s = 0;
        ns = 0;
    } else {
        if (src == cached) {
            w = C_MV(10, 18);
            n = 1;
        } else if (src >= 2 && src < homes + 2) {
            w = C_MV(10, 18 + src);
            n = 1;
        } else if (off <= 0xf8) {
            w = C_LD_A0(off);
            n = 1;
        } else {
            w = LD_S0(10, off);
            n = 2;
        }
        off = dst * 8;
        if (off <= 0xf8) {
            s = C_SD_A0(off);
            ns = 1;
        } else {
            s = SD_A0(off);
            ns = 2;
        }
    }
    /* The store may be left out only when the value stays in CACHE. */
    uint64_t have = (uint64_t)((const char *)end - (const char *)at);
    if (have != 2 * (n + ns + keep)) {
        if (!keep || have != 2 * (n + 1))
            return 0;
        ns = 0;
    }
    for (uint64_t i = 0; i < n; i++, w >>= 16)
        if (at[i] != (uint16_t)w)
            return 0;
    at += n;
    for (uint64_t i = 0; i < ns; i++, s >>= 16)
        if (at[i] != (uint16_t)s)
            return 0;
    at += ns;
    if (keep && at[0] != C_MV(18, 10))
        return 0;
    return 1;
}

static unsigned long accepted, rejected, unchecked;

static void report(void)
{
    FILE *f = fopen("/tmp/move-check.txt", "a");
    if (f) {
        fprintf(f, "accepted %lu rejected %lu unchecked %lu\n", accepted, rejected, unchecked);
        fclose(f);
    }
}

void spike_check_move_gate(const uint8_t *at, const uint8_t *end, uint32_t dst, uint32_t src, uint32_t homes,
                           uint32_t cached, uint32_t keep)
{
    static int registered;
    if (!registered) {
        registered = 1;
        atexit(report);
    }
    uint64_t r = spike_check_move((const uint16_t *)at, (const uint16_t *)end, dst, src, homes, cached, keep);
    if (r == 1) {
        accepted++;
    } else if (r == 2) {
        unchecked++;
    } else {
        rejected++;
        fprintf(stderr, "spike-check: move %u %u homes %u cached %u keep %u rejected: %ld bytes\n", dst, src,
                homes, cached, keep, (long)(end - at));
        report();
        abort();
    }
}
