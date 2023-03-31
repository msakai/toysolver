#include <windows.h>
#include <tlhelp32.h>

int GetNumThreads()
{
    DWORD   dwPID = GetCurrentProcessId();
    HANDLE  hSnapshot;
    INT     nThread   = 0;
    
    if ( (hSnapshot = CreateToolhelp32Snapshot(TH32CS_SNAPALL,dwPID)) != INVALID_HANDLE_VALUE ){
        THREADENTRY32  te32 = { sizeof(THREADENTRY32) };

        if ( Thread32First(hSnapshot,&te32) ){
            do {
                nThread++;
            } while ( Thread32Next(hSnapshot,&te32) );
        }
        CloseHandle( hSnapshot );
    }

    return nThread;
}
