/*
 * Strip sequence of lines of their common prefix, if any.
 *
 * `rmprefix` reads lines on standard input, and prints them on
 * standard output in the same order, but with their common prefix
 * removed.  This prefix may be empty, in which case output will be
 * the same as input.  No error checking is done.
 *
 * Usage: `rmprefix`.  No command line options are accepted.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

size_t min(size_t x, size_t y) {
  return x < y ? x : y;
}

size_t prefixlen(char* s1, char* s2) {
  size_t ret = 0;
  for (;*s1 && *s2 && *s1 == *s2; ret++) {
    s1++; s2++;
  }
  return ret;
}

char* fgetline(FILE* file) {
  size_t bufsiz = 80, len = 0;
  char* buf = malloc(bufsiz);
  char* p = buf;

  for (;;) {
    int c = fgetc(file);
    if(c == EOF)
      break;

    if (++len == bufsiz) {
      char* newbuf = realloc(buf, bufsiz *= 2);

      p = newbuf + (p - buf);
      buf = newbuf;
    }
    if ((*p++ = c) == '\n')
      break;
  }
  *p = '\0';
  return buf;
}

int main() {
  size_t lines_sz = 100;
  char** lines = malloc(lines_sz*sizeof(char*));
  char** nextline = lines;

  size_t prefix = 0;
  char* lastline = NULL;
  char* line = fgetline(stdin);

  if (line == NULL) {
    return 0;
  }

  lastline = *nextline++ = line;
  prefix = strlen(line);
  for (;;) {
    line = fgetline(stdin);
    if (line == NULL || line[0] == '\0') {
      break;
    }
    if (lines_sz == (size_t)(nextline-lines)) {
      char** newlines = realloc(lines, (lines_sz*=2)*sizeof(char*));

      nextline = newlines + (nextline-lines);
      lines = newlines;
    }

    *nextline++ = line;
    
    prefix = min(prefixlen(lastline, line), prefix);
    lastline = line;
  }
  for (; lines != nextline; lines++) {
    fputs((*lines)+prefix, stdout);
  }

  return 0;
}
