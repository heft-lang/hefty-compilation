#include "runtime.h"

int64_t read_int(void) {
	int64_t x;
	scanf("%" SCNd64, &x);
	return x;
}