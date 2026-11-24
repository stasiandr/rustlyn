// Writes a jump over the start of a method Mono compiled, as Mono writes its
// own code: on Apple silicon JIT memory is writable only while this thread has
// switched it to writable, and then it is not executable — so nothing managed
// may run between the two switches, and this has to be native.
#include <pthread.h>
#include <stdint.h>
#include <string.h>
#include <libkern/OSCacheControl.h>

int pilot_write_jump(void *at, void *target)
{
    uint32_t code[4];
    code[0] = 0x58000050; // ldr x16, #8
    code[1] = 0xD61F0200; // br x16
    uint64_t address = (uint64_t)target;
    memcpy(&code[2], &address, sizeof address);
    pthread_jit_write_protect_np(0);
    memcpy(at, code, sizeof code);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(at, sizeof code);
    return 0;
}
