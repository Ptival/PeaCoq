#include <stdio.h>

double
fp_prev(double x) {
  double y;
  y = x / 2;
  while(((x + y) / 2 != x) && ((x + y) / 2 != y)) {
    y = (x + y) / 2;
  }
  return y;
}

int
main(void) {
  printf("%f\n", fp_prev(1.0));
  printf("%0.25f\n", fp_prev(1.0));
}
