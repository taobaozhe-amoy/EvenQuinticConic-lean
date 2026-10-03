#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
/* Runtime compatibility only: use the permitted process-self alias for
   requests for this process's executable. No other path is rewritten. */
ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*original)(const char *, char *, size_t);
  if (!original) original = dlsym(RTLD_NEXT, "readlink");
  char own_exe[80];
  snprintf(own_exe, sizeof own_exe, "/proc/%d/exe", (int)getpid());
  return original(strcmp(path, own_exe) == 0 ? "/proc/self/exe" : path, buf, size);
}
