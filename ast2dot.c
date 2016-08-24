#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define VEC_TYPE int
#include "vec.c"

static int node = 1;
static struct vec_int stack;

void error(void)
{
	printf("\tnERROR [shape=egg,label=\"???\",color=\"1 0 0\"];\n");
	printf("\tn%d -> nERROR;\n", stack.v[stack.n-1]);
	printf("}");
	exit(10);
}

void push(char* label)
{
	if (label[0] == '\'')
		printf("\tn%d [shape=ellipse,label=\"%s\"];\n", node, label);
	else
		printf("\tn%d [shape=box,label=\"%s\"];\n", node, label);

	printf("\tn%d -> n%d;\n", stack.v[stack.n-1], node);
	vec_int_push(&stack, node++);
}

int main(void)
{
	char s[100];

	stack = vec_int_make(10);

	printf("digraph G {\n\tgraph [ordering=out];\n");

	s[0]='\0';
	if (scanf("%99[a-zA-Z0-9_][", s) < 1) return 1;

	vec_int_push(&stack, 0);
	printf("\n\tn0 [shape=box,label=\"%s\"];\n", s);

	while(1) {
		int k, l=0;
		s[0]='\0';

		k=scanf("%99[a-zA-Z0-9_][", s);
		if (k == EOF) {
			if (stack.n == 0)
				break;
			else
				error();
		}
		if (k > 0) {
			push(s);
			continue;
		}

		k = scanf("'%98[^']'", s+1);
		if (k == EOF) error();
		if (k > 0) { /*TODO: accept tokens of any length*/
			s[0]='\'';
			strcat(s, "\'");
			push(s);
			vec_int_pop(&stack);
			continue;
		}

		k = scanf("]%n", &l);
		if (k == EOF) error();
		if (l == 0) {
			if (stack.n == 0)
				break;
		} else if (l == 1) {
			if (stack.n == 0)
				return 2;
			vec_int_pop(&stack);
			continue;
		}

		return 3;
	}

	printf("}");
	return 0;
}
