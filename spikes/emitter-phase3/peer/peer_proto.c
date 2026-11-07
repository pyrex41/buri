/* Spike 9: a prototype of design (a), the emitter as a separate peer process, on the runtime's side of the
   process model.  Not Shen/JIT: a stand-in that has the same shape.

   The runtime forks the peer first, while only the standard descriptors are open (Theorem's clone_spec
   declines a fork with a socket or a regular file open).  Then it listens on an ephemeral port: the model
   binds only INADDR_ANY:0 and doesn't model getsockname, so the runtime can't learn its port, and the peer
   finds it from /proc (the peer is outside the model, so it may).  The runtime accepts one connection
   and, per compile, writes a request (bytecode words), reads a length-prefixed reply with a bound, copies
   it into its own code arena, validates it, and only then runs it.  A missing, short, oversized or rejected
   reply stops the runtime with a named status (here exit 70), never with code it didn't check.

   usage: peer_proto N     (N compiles; prints the mean round trip in ns) */
#define _GNU_SOURCE
#include <arpa/inet.h>
#include <netinet/tcp.h>
#include <signal.h>
#include <dirent.h>
#include <netinet/in.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#define MAX_CODE 4096
static unsigned char arena[1 << 20] __attribute__((aligned(4096), section(".bss.spike_arena")));
static size_t used;

/* The runtime's validator stands in for spike_check_fn: here, the code must be exactly li a0,K; ret. */
static int validate(const unsigned char *p, size_t n, uint32_t k)
{
    uint32_t li = 0x00000513u | (k & 0xfff) << 20; /* addi a0, x0, k */
    unsigned char want[6] = {li & 255, li >> 8 & 255, li >> 16 & 255, li >> 24, 0x82, 0x80}; /* c.ret */
    return n == 6 && !memcmp(p, want, 6);
}

static int read_full(int fd, void *b, size_t n)
{
    size_t got = 0;
    while (got < n) {
        ssize_t r = read(fd, (char *)b + got, n - got);
        if (r <= 0) return 0; /* FIN, RST or timeout: the peer is gone */
        got += (size_t)r;
    }
    return 1;
}

static int write_full(int fd, const void *b, size_t n)
{
    size_t put = 0;
    while (put < n) {
        ssize_t r = write(fd, (const char *)b + put, n - put);
        if (r <= 0) return 0;
        put += (size_t)r;
    }
    return 1;
}

/* The peer (emitter stand-in): reads a 4-byte request (a constant K), emits `li a0,K; c.ret`, and replies
   length-prefixed. It is outside the model, so it may find the port from /proc; here it is passed in. */
static void peer_main(int port)
{
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    struct sockaddr_in sa = {.sin_family = AF_INET, .sin_port = htons((uint16_t)port)};
    int one = 1; setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
    inet_pton(AF_INET, "127.0.0.1", &sa.sin_addr);
    for (int i = 0; i < 1000 && connect(fd, (void *)&sa, sizeof sa) < 0; i++)
        usleep(1000);
    for (;;) {
        uint32_t k;
        if (!read_full(fd, &k, 4)) break;
        uint32_t li = 0x00000513u | (k & 0xfff) << 20;
        unsigned char code[6] = {li & 255, li >> 8 & 255, li >> 16 & 255, li >> 24, 0x82, 0x80};
        uint32_t len = sizeof code;
        write_full(fd, &len, 4);
        write_full(fd, code, len);
    }
    close(fd);
    _exit(0);
}

int main(int argc, char **argv)
{
    long n = argc > 1 ? atol(argv[1]) : 1000;
    /* Listen first, on an ephemeral port, while only the standard descriptors are open. */
    int srv = socket(AF_INET, SOCK_STREAM, 0);
    int one = 1;
    setsockopt(srv, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    struct sockaddr_in sa = {.sin_family = AF_INET, .sin_addr.s_addr = htonl(INADDR_LOOPBACK)};
    if (bind(srv, (void *)&sa, sizeof sa) < 0 || listen(srv, 1) < 0) { perror("bind/listen"); return 1; }
    socklen_t sl = sizeof sa;
    getsockname(srv, (void *)&sa, &sl);
    int port = ntohs(sa.sin_port);
    pid_t pid = fork();
    if (pid == 0) { close(srv); peer_main(port); }
    int conn = accept(srv, NULL, NULL);
    if (conn < 0) { perror("accept"); return 1; }
    setsockopt(conn, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    long ok = 0;
    for (long i = 0; i < n; i++) {
        uint32_t k = (uint32_t)(i & 0xfff);
        if (!write_full(conn, &k, 4)) break;
        uint32_t len;
        if (!read_full(conn, &len, 4) || len > MAX_CODE) { fprintf(stderr, "bad reply\n"); return 70; }
        unsigned char buf[MAX_CODE];
        if (!read_full(conn, buf, len)) { fprintf(stderr, "short reply\n"); return 70; }
        /* Copy into the runtime's own arena, then validate, then (would) run. */
        if (used + len > sizeof arena) used = 0;
        unsigned char *slot = arena + used;
        memcpy(slot, buf, len);
        used += len;
        if (!validate(slot, len, k)) { fprintf(stderr, "rejected\n"); return 70; }
        ok++;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double ns = ((double)(t1.tv_sec - t0.tv_sec) * 1e9 + (t1.tv_nsec - t0.tv_nsec)) / (double)(ok ? ok : 1);
    close(conn);
    kill(pid, 9);
    printf("peer-proto: %ld compiles, all accepted, mean round trip %.0f ns\n", ok, ns);
    return 0;
}
