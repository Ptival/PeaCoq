#include <stdio.h>

int
main(void) {
  int a;
  a = 0 ? (3>2 ? 23
               : (2>5 ? (7<6 ? 34 : 48)
                      : 64))
        : 1;
  printf("%d\n", a);
}
