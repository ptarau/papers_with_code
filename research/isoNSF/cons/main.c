#include <stdlib.h>
#include <stdio.h>
#include "cons.h"

void tprint(N x);

void tprint(N x) {
	if (hasTag(x)) {
		printf("%lu", unTag(x));
	} else {
		printf("c(");
		tprint(hd(x));
		printf(",");
		tprint(tl(x));
		printf(")");
	}
}

void parprint(N x) {
	if (isNil(x)) {
		printf("E");
	} else {
		printf("(");
		parprint(hd(x));
		printf(":->");
		parprint(tl(x));
		printf(")");
	}
}

void p(char *s, N x) {
	printf("%s %lu\n", s, x);
}

void pp(char *s, N x) {
	printf("%s ", s);
	tprint(x);
	printf("\n");
}

void ppp(char *s, N x) {
	printf("%s ", s);
	parprint(x);
	printf("\n");
}

int main() {

	N x, y, z; //,a,b,c;

	y = tag(33);
	pp("4:", succ(y));
	pp("2:", pred(y));

	x = tag(30);
	z = cons(x, cons(x, y));
	pp("z", z);
	ppp("z", z);
	pp("z+1", succ(z));
	pp("z-1", pred(z));
	/*
	 p("wordsize",sizeof(N));
	 p("ptrsize",sizeof(&n));
	 p("alignment on words",(N)(&n));
	 p("doublesize",sizeof(double));
	 p("wordbits",wordbits());

	 x=tag(62);
	 y=tag(33);
	 z=cons(tag(6),cons(x,y));
	 z=cons(z,z);
	 p("tagged cons",z);
	 pp("cons = ",z);
	 ppp("par x = ",nil());
	 ppp("par y = ",tag(1));
	 ppp("par cons x y = ",cons(nil(),tag(1)));
	 p("--------",0);

	 x=hd(z);
	 pp("hd = ",x);
	 y=tl(z);
	 pp("tl = ",y);

	 p("hasTag",hasTag(4390929));
	 p("hasNoTag",hasTag(8*99));
	 a=nlog2(35);
	 p("log2 = ",a);
	 b=51;
	 c=unTag(tag(b));
	 p("b",b);
	 p("c",c);
	 */

	return 0;
}
