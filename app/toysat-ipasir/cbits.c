#include "HsFFI.h"
#ifdef __GLASGOW_HASKELL__
#include "Rts.h"
#endif
#include "cabal_macros.h"
#include "ipasir.h"

extern void *toysat_ipasir_init();
extern void toysat_ipasir_release(void * solver);

static int initialized = 0;

IPASIR_API
const char *ipasir_signature()
{
    return "toysat-" VERSION_toysolver;
}

IPASIR_API
void *ipasir_init(void)
{
    if (initialized++ == 0) {
        int argc = 0;
        char *argv[] = { NULL };
        char **pargv = argv;

#if __GLASGOW_HASKELL__ >= 703
        RtsConfig conf = defaultRtsConfig;
        conf.rts_opts_enabled = RtsOptsAll;
        hs_init_ghc(&argc, &pargv, conf);
#else
        hs_init(&argc, &argv);
#endif
    }

    return toysat_ipasir_init();
}

IPASIR_API
void ipasir_release(void* solver)
{
    toysat_ipasir_release(solver);

    if (--initialized == 0) {
        hs_exit();
    }
}
