/**  durable.c
 *
 *  Syncs that reach the disk (durable.h).
 */

#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "durable.h"

bool av_sync_fd(int fd) {
#ifdef F_FULLFSYNC
    for (;;) {
        if (fcntl(fd, F_FULLFSYNC) == 0) return true;
        if (errno == EINTR) continue;
        /* a file system that does not do it falls back to fsync; any
         * other failure, an I/O error, is the sync's */
        if (errno != ENOTSUP && errno != ENOTTY && errno != EINVAL) return false;
        break;
    }
#endif
    for (;;) {
        if (fsync(fd) == 0) return true;
        if (errno != EINTR) return false;
    }
}

bool av_sync_dir(const char *dir) {
    int fd = open(dir, O_RDONLY);
    if (fd < 0) return false;
    bool ok = av_sync_fd(fd);
    if (close(fd) != 0) ok = false;
    return ok;
}

bool av_sync_parent(const char *path) {
    const char *slash = strrchr(path, '/');
    if (!slash) return av_sync_dir(".");
    if (slash == path) return av_sync_dir("/");
    size_t n = (size_t)(slash - path);
    char *dir = malloc(n + 1);
    if (!dir) return false;
    memcpy(dir, path, n);
    dir[n] = '\0';
    bool ok = av_sync_dir(dir);
    free(dir);
    return ok;
}
