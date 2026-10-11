/**  durable.h
 *
 *  Internal to the runtime: syncs that reach the disk.  On macOS fsync
 *  only hands the data to the drive, which may hold it in its cache past
 *  a power loss; F_FULLFSYNC asks the drive to write it to the media.
 *  Not part of the public interface.
 */

#ifndef DURABLE_H
#define DURABLE_H

#include <stdbool.h>

/*  fd's data and metadata, on the media: F_FULLFSYNC where there is one,
 *  falling back to fsync on a file system that does not support it (an
 *  I/O error is a failure); fsync elsewhere.  Retries on EINTR. */
bool av_sync_fd(int fd);

/*  A directory's entries (a create, a rename, an unlink), on the media. */
bool av_sync_dir(const char *dir);

/*  The directory holding path: its parent, or "." for a bare name. */
bool av_sync_parent(const char *path);

#endif /* DURABLE_H */
