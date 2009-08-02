/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2007
 *
 * File locking support as required by Haskell 98
 *
 * ---------------------------------------------------------------------------*/

#ifndef RTS_FILELOCK_H
#define RTS_FILELOCK_H

int  lockFile(int fd, dev_t dev, ino_t ino, int for_writing);
int  unlockFile(int fd);

#endif /* RTS_FILELOCK_H */