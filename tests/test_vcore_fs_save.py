"""A save's file calls give the virtual core up while the host's file calls run (host/nn_fs.c).

OpenFile and ReadFile already gave it up (issue 1929); WriteFile, SetFileSize, FlushFile, CloseFile, CreateFile,
DeleteFile, CreateDirectory, DeleteDirectoryRecursively and RenameFile kept it. FlushFile is an fdatasync on Linux, and
OoT's save thread (gmd::SaveDataMgr) held its core through a save for about 20 s: the threads that wait for that core
ran only at vc_acquire's 2 s escapes, and one frame took 10.2 s. The actual functions are compiled with stand-ins that
count the host file calls they make and how many of them ran while the thread held its core:

- every host file call runs without the core, and the core is held again when the function returns, taken once: a
  write (a whole one, a short one), a size change, a flush, the close of a file opened for writing, a file made (and
  one that exists), deleted, a folder made (and one that exists), deleted (a folder, a link), a rename;
- the answers are the ones from before: PathAlreadyExists for a file or folder that exists although taking the core
  again sets the last error (vc_acquire's timed wait: ERROR_TIMEOUT), PathNotFound for a failed delete or rename or a
  mount that is not writable, OutOfRange for a short write;
- a file opened for reading is closed with the core held, as before (no extra wait for a core per file read);
- a thread that holds no core when it calls them takes none.

python -I -B tests/test_vcore_fs_save.py [--cxx clang++] [--source host/nn_fs.c]
"""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

RUN_ALL_ARGS = ["--cxx", "{cxx}"]

ROOT = Path(__file__).resolve().parents[1]

FUNCTIONS = (
    "HLE(_ZN2nn2fs9WriteFileENS0_10FileHandleElPKvmRKNS0_11WriteOptionE) {",
    "HLE(_ZN2nn2fs11SetFileSizeENS0_10FileHandleEl) {",
    "HLE(_ZN2nn2fs9FlushFileENS0_10FileHandleE) {",
    "HLE(_ZN2nn2fs9CloseFileENS0_10FileHandleE) {",
    "HLE(_ZN2nn2fs10CreateFileEPKcl) {",
    "HLE(_ZN2nn2fs10DeleteFileEPKc) {",
    "HLE(_ZN2nn2fs15CreateDirectoryEPKc) {",
    "HLE(_ZN2nn2fs26DeleteDirectoryRecursivelyEPKc) {",
    "HLE(_ZN2nn2fs10RenameFileEPKcS2_) {",
)


def block(source, marker):
    start = source.index(marker)
    end = source.index("{", start) + 1
    depth = 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return source[start:end]


HARNESS = r"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef void *HANDLE;
typedef unsigned long DWORD;
typedef int BOOL;
typedef long long LONGLONG;
typedef struct { LONGLONG QuadPart; } LARGE_INTEGER;
typedef struct { DWORD Offset, OffsetHigh; } OVERLAPPED;
#define TRUE 1
#define FALSE 0
#define INVALID_HANDLE_VALUE ((HANDLE)(intptr_t)-1)
#define INVALID_FILE_ATTRIBUTES ((DWORD)-1)
#define GENERIC_WRITE 0x40000000u
#define CREATE_NEW 1
#define FILE_BEGIN 0
#define FILE_ATTRIBUTE_DIRECTORY 0x10
#define FILE_ATTRIBUTE_NORMAL 0x80
#define FILE_ATTRIBUTE_REPARSE_POINT 0x400
#define MOVEFILE_REPLACE_EXISTING 1
#define ERROR_FILE_NOT_FOUND 2
#define ERROR_FILE_EXISTS 80
#define ERROR_ALREADY_EXISTS 183
#define ERROR_TIMEOUT 1460
typedef struct { uint64_t x[32]; } Ctx;
#define HLE(sym) void imp_##sym(Ctx *c)
#define ARG(n) (c->x[n])
#define RET(v) (c->x[0] = (uint64_t)(v))
#define GP(a) ((void *)(uintptr_t)(a))
#define HOS_FS_PATH 1024
#define R_PATH_NOT_FOUND 0x202
#define R_PATH_EXISTS 0x402
static const char *gstr(uint64_t a) { return (const char *)(uintptr_t)a; }
static int guest_ok = 1;
static void *hos_guest_range(uint64_t a, uint64_t n) { (void)n; return guest_ok ? GP(a) : NULL; }

/* the thread's virtual core, as hos_vcore_away / hos_vcore_back keep it (host/hos_thread.c); taking it again waits in
   vc_acquire on a condition variable, whose 1 ms timeouts set the last error */
static DWORD last_error;
static DWORD GetLastError(void) { return last_error; }
static int held, takes;
int hos_vcore_away(void) { if (!held) return 0; held = 0; return 1; }
void hos_vcore_back(void) { if (!held) held = 1, takes++, last_error = ERROR_TIMEOUT; }

/* the mount's path */
static int path_writable = 1;
static int host_path(const char *g, char *out, size_t cap, int *writable) {
    snprintf(out, cap, "%s", g);
    if (writable) *writable = path_writable;
    return 1;
}

/* the host's file calls: each one counted, and counted again when the thread holds its core through it; with fail set
   they fail with fail_error */
static int calls, with_core, fail, short_write;
static DWORD fail_error = ERROR_FILE_NOT_FOUND;
static BOOL host_call(void) {
    calls++;
    with_core += held;
    if (fail) { last_error = fail_error; return FALSE; }
    return TRUE;
}
static void make_dirs(const char *path) { (void)path; host_call(); }
static HANDLE CreateFileA(const char *p, DWORD a, DWORD s, void *sa, DWORD d, DWORD f, HANDLE t) {
    (void)p, (void)a, (void)s, (void)sa, (void)d, (void)f, (void)t;
    return host_call() ? (HANDLE)(intptr_t)0x1234 : INVALID_HANDLE_VALUE;
}
static BOOL WriteFile(HANDLE h, const void *buf, DWORD n, DWORD *put, OVERLAPPED *ov) {
    (void)h, (void)buf, (void)ov;
    const BOOL ok = host_call();
    *put = ok ? n - (DWORD)short_write : 0;
    return ok;
}
static BOOL SetFilePointerEx(HANDLE h, LARGE_INTEGER d, LARGE_INTEGER *at, DWORD how) {
    (void)h, (void)d, (void)at, (void)how;
    return host_call();
}
static BOOL SetEndOfFile(HANDLE h) { (void)h; return host_call(); }
static BOOL FlushFileBuffers(HANDLE h) { (void)h; return host_call(); }
static BOOL CloseHandle(HANDLE h) { (void)h; return host_call(); }
static BOOL DeleteFileA(const char *p) { (void)p; return host_call(); }
static BOOL RemoveDirectoryA(const char *p) { (void)p; return host_call(); }
static BOOL CreateDirectoryA(const char *p, void *sa) { (void)p, (void)sa; return host_call(); }
static DWORD attributes = FILE_ATTRIBUTE_DIRECTORY;
static DWORD GetFileAttributesA(const char *p) { (void)p; host_call(); return attributes; }
static BOOL MoveFileExA(const char *a, const char *b, DWORD how) { (void)a, (void)b, (void)how; return host_call(); }
static void delete_tree(const char *dir) { (void)dir; host_call(); }

/* the file handles: one, number 1 */
typedef struct { HANDLE h; int writable; char path[HOS_FS_PATH]; } Handle;
static Handle *table[2];
static int freed;
static Handle *get_handle(Ctx *c, uint64_t id) { (void)c; return table[id]; }
static void free_handle(uint64_t id) { table[id] = NULL; freed++; }
static uint64_t open_handle(int writable) {
    free(table[1]);
    table[1] = (Handle *)calloc(1, sizeof *table[1]);
    table[1]->h = (HANDLE)(intptr_t)0x1234;
    table[1]->writable = writable;
    freed = 0;
    return 1;
}

@FUNCTIONS@

static int bad;
static void check(int ok, const char *what) { if (!ok) { printf("FAIL: %s\n", what); bad = 1; } }
typedef void (*Hle)(Ctx *);
/* one call by a thread that holds a core (or not); answers its result (x0) */
static uint64_t call(Hle f, int core, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3) {
    Ctx c;
    memset(&c, 0, sizeof c);
    c.x[0] = a0, c.x[1] = a1, c.x[2] = a2, c.x[3] = a3;
    held = core, takes = 0, calls = with_core = 0, last_error = 0;
    f(&c);
    return c.x[0];
}
/* the call made n host file calls, none with the core, and holds the core again, taken once */
static void without_core(const char *what, int n) {
    char m[300];
    snprintf(m, sizeof m, "%s: %d host file calls (%d expected), %d of them with the core held (0 expected); "
             "the core held %d, taken %d times (1, 1)", what, calls, n, with_core, held, takes);
    check(calls == n && with_core == 0 && held == 1 && takes == 1, m);
}
#define U(p) ((uint64_t)(uintptr_t)(p))
#define WRITE imp__ZN2nn2fs9WriteFileENS0_10FileHandleElPKvmRKNS0_11WriteOptionE
#define SET_SIZE imp__ZN2nn2fs11SetFileSizeENS0_10FileHandleEl
#define FLUSH imp__ZN2nn2fs9FlushFileENS0_10FileHandleE
#define CLOSE imp__ZN2nn2fs9CloseFileENS0_10FileHandleE
#define CREATE imp__ZN2nn2fs10CreateFileEPKcl
#define DELETE imp__ZN2nn2fs10DeleteFileEPKc
#define MKDIR imp__ZN2nn2fs15CreateDirectoryEPKc
#define RMTREE imp__ZN2nn2fs26DeleteDirectoryRecursivelyEPKc
#define RENAME imp__ZN2nn2fs10RenameFileEPKcS2_
int main(void) {
    static char data[4096];
    const char *file = "save:/slot_00/progress.sav", *other = "save:/slot_00/progress.tmp", *dir = "save:/slot_00";
    uint64_t r;

    open_handle(1);
    r = call(WRITE, 1, 1, 0, U(data), sizeof data);
    check(r == 0, "WriteFile: written");
    without_core("WriteFile", 1);
    short_write = 1;
    r = call(WRITE, 1, 1, 0, U(data), sizeof data);
    check(r == 0x2EE202, "WriteFile: a short write is OutOfRange");
    without_core("WriteFile, a short write", 1);
    short_write = 0;
    guest_ok = 0;
    r = call(WRITE, 1, 1, 0, U(data), sizeof data);
    check(r == 0x2EE202 && calls == 0 && held == 1,
          "WriteFile: a buffer outside guest memory is not written, the core still held");
    guest_ok = 1;

    r = call(SET_SIZE, 1, 1, 130716, 0, 0);
    check(r == 0, "SetFileSize: done");
    without_core("SetFileSize", 2);

    r = call(FLUSH, 1, 1, 0, 0, 0);
    check(r == 0, "FlushFile: done");
    without_core("FlushFile (an fdatasync on Linux)", 1);

    r = call(CLOSE, 1, 1, 0, 0, 0);
    without_core("CloseFile of a file opened for writing", 1);
    check(freed == 1 && !table[1], "CloseFile: the handle is let go");
    open_handle(0);
    r = call(CLOSE, 1, 1, 0, 0, 0);
    check(calls == 1 && with_core == 1 && held == 1 && takes == 0 && freed == 1,
          "CloseFile of a file opened for reading: closed with the core held, as before");

    r = call(CREATE, 1, U(file), 130716, 0, 0);
    check(r == 0, "CreateFile: made");
    without_core("CreateFile", 5);
    fail = 1, fail_error = ERROR_FILE_EXISTS;
    r = call(CREATE, 1, U(file), 130716, 0, 0);
    check(r == R_PATH_EXISTS,
          "CreateFile of a file that exists: PathAlreadyExists (its error read before the core is taken again)");
    without_core("CreateFile of a file that exists", 2);
    fail = 0;
    path_writable = 0;
    r = call(CREATE, 1, U("rom:/a.bin"), 16, 0, 0);
    check(r == R_PATH_NOT_FOUND && calls == 0 && held == 1 && takes == 0,
          "CreateFile on a mount that is not writable: PathNotFound");
    path_writable = 1;

    r = call(DELETE, 1, U(file), 0, 0, 0);
    check(r == 0, "DeleteFile: deleted");
    without_core("DeleteFile", 1);
    fail = 1, fail_error = ERROR_FILE_NOT_FOUND;
    r = call(DELETE, 1, U(file), 0, 0, 0);
    check(r == R_PATH_NOT_FOUND, "DeleteFile of a file that is not there: PathNotFound");
    without_core("DeleteFile of a file that is not there", 1);
    fail = 0;

    r = call(MKDIR, 1, U(dir), 0, 0, 0);
    check(r == 0, "CreateDirectory: made");
    without_core("CreateDirectory", 2);
    fail = 1, fail_error = ERROR_ALREADY_EXISTS;
    r = call(MKDIR, 1, U(dir), 0, 0, 0);
    check(r == R_PATH_EXISTS,
          "CreateDirectory of a folder that exists: PathAlreadyExists (its error read before the core is taken again)");
    without_core("CreateDirectory of a folder that exists", 2);
    fail = 0;

    attributes = FILE_ATTRIBUTE_DIRECTORY;
    r = call(RMTREE, 1, U(dir), 0, 0, 0);
    check(r == 0, "DeleteDirectoryRecursively: deleted");
    without_core("DeleteDirectoryRecursively", 2);
    attributes = FILE_ATTRIBUTE_DIRECTORY | FILE_ATTRIBUTE_REPARSE_POINT;
    fail = 1;
    r = call(RMTREE, 1, U(dir), 0, 0, 0);
    check(r == 0, "DeleteDirectoryRecursively of a link: done");
    without_core("DeleteDirectoryRecursively of a link (DeleteFileA, then RemoveDirectoryA)", 3);
    fail = 0;
    attributes = FILE_ATTRIBUTE_DIRECTORY;

    r = call(RENAME, 1, U(other), U(file), 0, 0);
    check(r == 0, "RenameFile: renamed");
    without_core("RenameFile", 1);
    fail = 1;
    r = call(RENAME, 1, U(other), U(file), 0, 0);
    check(r == R_PATH_NOT_FOUND, "RenameFile that fails: PathNotFound");
    without_core("RenameFile that fails", 1);
    fail = 0;

    /* a thread that holds no core takes none */
    Hle all[] = {WRITE, SET_SIZE, FLUSH, CLOSE, CREATE, DELETE, MKDIR, RMTREE, RENAME};
    for (int i = 0; i < (int)(sizeof all / sizeof *all); i++) {
        open_handle(1);
        const uint64_t a0 = i < 4 ? 1 : U(file);
        call(all[i], 0, a0, i == 8 ? U(other) : 0, U(data), 16);
        char m[96];
        snprintf(m, sizeof m, "function %d by a thread that held no core: took none (took %d)", i, takes);
        check(held == 0 && takes == 0 && calls > 0, m);
    }
    if (!bad) puts("ok");
    return bad;
}
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cxx", default="clang++")
    parser.add_argument("--source", type=Path, default=ROOT / "host/nn_fs.c")
    args = parser.parse_args()
    src = args.source.read_text(encoding="utf-8")
    fixture = HARNESS.replace("@FUNCTIONS@", "\n".join(block(src, marker) for marker in FUNCTIONS))
    compiler = shutil.which(args.cxx)
    if not compiler:
        raise SystemExit("C++ compiler not found: " + args.cxx)
    with tempfile.TemporaryDirectory(prefix="vcore-fs-save-") as temporary:
        folder = Path(temporary)
        (folder / "fixture.cpp").write_text(fixture, encoding="utf-8")
        exe = folder / ("fixture.exe" if os.name == "nt" else "fixture")
        subprocess.run([compiler, "-std=c++17", "-O1", "-w", str(folder / "fixture.cpp"), "-o", str(exe)], check=True,
                       timeout=120)
        result = subprocess.run([str(exe)], capture_output=True, text=True, timeout=30)
        print(result.stdout, end="")
        if result.returncode or "ok" not in result.stdout.split():
            raise SystemExit("a save's file calls hold the virtual core through the host's file calls (host/nn_fs.c)")


if __name__ == "__main__":
    main()
