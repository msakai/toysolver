#include "HsFFI.h"
#ifdef __GLASGOW_HASKELL__
#include "Rts.h"
#endif
#include "cabal_macros.h"
#include "ipasir.h"

extern void *toysat_ipasir_init();
extern void toysat_ipasir_release(void * solver);

static _Bool initialized = 0;

IPASIR_API
const char *ipasir_signature()
{
    return "toysat-" VERSION_toysolver;
}

IPASIR_API
void *ipasir_init(void)
{
    if (!initialized) {
        int argc = 1;
        char *argv[] = { "toysat-ipasir", NULL };
        char **pargv = argv;

#ifdef __GLASGOW_HASKELL__
        RtsConfig conf = defaultRtsConfig;
        conf.rts_opts_enabled = RtsOptsAll;
        hs_init_ghc(&argc, &pargv, conf);
#else
        hs_init(&argc, &argv);
#endif

        initialized = 1;
    }

    return toysat_ipasir_init();
}

IPASIR_API
void ipasir_release(void* solver)
{
    toysat_ipasir_release(solver);

    // Note that we do not call hs_exit() here because GHC currently
    // does not support reinitializing the RTS after shutdown.
}
