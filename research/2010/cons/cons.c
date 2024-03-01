#include <stdlib.h>
#include "cons.h"

static inline N maxbits() {
	return (sizeof(N) << 3) - 4;
}

static inline N nlog2(N x) {
	N l = 0;
	while (x > 0) {
		x = x >> 1;
		++l;
	}
	return l;
}

inline N tag(N x) {
	return (x << 1) | 1;
}

inline N unTag(N x) {
	return (x >> 1);
}

inline int hasTag(N x) {
	return x & 1;
}

inline N consN(N x, N y) {
	return ((y << 1) + 1) << x;
}

inline N hdN(N z) {
	N x = 0;
	while (!(z & 1)) {
		z >>= 1;
		++x;
	}
	return x;
}

inline N tlN(N z) {
	while (!(z & 1)) {
		z >>= 1;
	}
	return (z - 1) >> 1;
}

inline N consT(N x, N y) {
	T t = (T) (malloc(sizeof(struct T)));
	t->hd = x;
	t->tl = y;
	return (N) t;
}

/* API */

inline N nil() {
	return tag(0);
}

int isNil(N x) {
	return hasTag(x) && (0 == unTag(x));
}

inline N cons(N x, N y) {
	if (hasTag(y) && hasTag(x)) {
		N a = unTag(x);
		N b = unTag(y);
		if (a + nlog2(b) < maxbits()) {
			N c = consN(a, b);
			c = tag(c);
			return c;
		}
	}
	return consT(x, y);
}

inline N hd(N z) {
	if (hasTag(z))
		return tag(hdN(unTag(z)));
	return ((T) z)->hd;
}

inline N tl(N z) {
	if (hasTag(z))
		return tag(tlN(unTag(z)));
	return ((T) z)->tl;
}

inline N ite(N x, N y, N z) {
	return isNil(x) ? z : y;
}

inline N incHd(N x) {
	return cons(succ(hd(x)), tl(x));
}

inline N decHd(N x) {
	return cons(pred(hd(x)), tl(x));
}

inline N succ(N x) {
	if (hasTag(x)) {
		N a = unTag(x) + 1;
		if (a < (1 << maxbits()))
			return tag(a);
	}
	N h = hd(x);
	N t = tl(x);
	if (isNil(h))
		return incHd(succ(t));
	return cons(nil(), decHd(x));
}

N pred(N x) {
	if (hasTag(x)) {
		N a = unTag(x) - 1;
		if (a > 0)
			return tag(a);
		else
			return x; // should be an error warning here !!!
	}

	if (isNil(hd(x)))
		return incHd(tl(x));
	return cons(nil(), pred(decHd(x)));
}

