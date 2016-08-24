#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <errno.h>
#include "util.h"

#define MIN(a, b) ((a)<(b) ? (a) : (b))

typedef enum {
	false,
	true
} bool;

struct str {
	char* p;
	size_t n;
};

struct str_view {
	char* p;
	size_t n;
};

struct str_view str_view(char* p, size_t n)
{
	struct str_view sv;
	sv.p = p;
	sv.n = n;
	return sv;
}

bool str_view_eq(struct str_view s1, struct str_view s2)
{
	return s1.n == s2.n && strncmp(s1.p, s2.p, s1.n) == 0;
}

bool str_view_is(struct str_view sv, char* s)
{
	return sv.n == strlen(s) && strncmp(sv.p, s, sv.n) == 0;
}

struct str_view str_view_str(struct str s)
{
	struct str_view sv;
	sv.p = s.p;
	sv.n = s.n;
	return sv;
}

struct str read_all(char* filename)
{
	struct str result;
	long len;
	FILE* f = fopen(filename, "rb");
	if (!f) goto err;

	fseek(f, 0, SEEK_END);
	len = ftell(f);
	if (len < 0) goto err;

	result.n = (size_t) len;
	fseek(f, 0, SEEK_SET);
	
	result.p = malloc(result.n+1);
	fread(result.p, 1, result.n, f);
	result.p[result.n] = '\0';

	fclose(f);
	return result;
err:
	fclose(f);
	result.p = NULL;
	result.n = 0;
	return result;
}

enum token_t
{
	TOK_LPAREN,    /*  (            */
	TOK_RPAREN,    /*  )            */
	TOK_LBRACKET,  /*  [            */
	TOK_RBRACKET,  /*  ]            */
	TOK_LBRACE,    /*  {            */
	TOK_RBRACE,    /*  }            */
	TOK_COLON,     /*  :            */
	TOK_COLON2,    /*  ::           */
	TOK_BANG,      /*  !            */
	TOK_BANGEQ,    /*  !=           */
	TOK_EQ,        /*  =            */
	TOK_EQ2,       /*  ==           */
	TOK_LESS,      /*  <            */
	TOK_LEQ,       /*  <=           */
	TOK_MORE,      /*  >            */
	TOK_MEQ,       /*  >=           */
	TOK_PLUS,      /*  +            */
	TOK_MINUS,     /*  -            */
	TOK_MINUS3,    /*  ---          */
	TOK_ARROW,     /*  ->           */
	TOK_STAR,      /*  *            */
	TOK_SLASH,     /*  /            */
	TOK_DOT,       /*  .            */
	TOK_DOT2,      /*  ..           */
	TOK_COMMA,     /*  ,            */
	TOK_SEMI,      /*  ;            */
	TOK_AND,       /*  &            */
	TOK_AND2,      /*  &&           */
	TOK_PIPE2,     /*  ||           */
	TOK_DIRECTIVE, /*  #stuff       */
	TOK_INT,       /*  123          */
	TOK_FLOAT,     /*  123.45       */
	TOK_STRING,    /*  "abc"        */
	TOK_ID,        /*  identifier   */
	TOK_EOF,       /*  end-of-file  */
	TOK__N
};

char* token_t_names[] = {"LPAREN","RPAREN","LBRACKET","RBRACKET","LBRACE","RBRACE","COLON","COLON2","BANG","BANGEQ","EQ","EQ2","LESS","LEQ","MORE","MEQ","PLUS","MINUS","MINUS3","ARROW","STAR","SLASH","DOT","DOT2","COMMA","SEMI","AND","AND2","PIPE2","DIRECTIVE","INT","FLOAT","STRING","ID","EOF"};

GS_ASSERT(sizeof(token_t_names) == TOK__N*sizeof(token_t_names[0]));

struct token {
	enum token_t type;
	struct str_view text;
};

#define VEC_TYPE struct token
#define VEC_TYPE_NAME token
#include "vec.c"

struct token token_of(enum token_t type, struct str_view text)
{
	struct token t;
	t.type = type;
	t.text = text;
	return t;
}

bool lex(struct str_view s, struct vec_token* v)
{
	#define ADD(Type, Len) vec_token_push(v, token_of(TOK_##Type, str_view(p, Len)))

	char* p = s.p;
	size_t k;
	
	while (*p) {
		while (isspace(*p)) p++;
		if (!*p) break;
		
		switch (*p) {
			case '(': ADD(LPAREN, 1); break;
			case ')': ADD(RPAREN, 1); break;
			case '[': ADD(LBRACKET, 1); break;
			case ']': ADD(RBRACKET, 1); break;
			case '{': ADD(LBRACE, 1); break;
			case '}': ADD(RBRACE, 1); break;
			case ':':
				if (p[1] == ':') ADD(COLON2, 2);
				else             ADD(COLON, 1);
				break;
			case '!':
				if (p[1] == '=') ADD(BANGEQ, 2);
				else             ADD(BANG, 1);
			case '=':
				if (p[1] == '=') ADD(EQ2, 2);
				else             ADD(EQ, 1);
				break;
			case '<':
				if (p[1] == '=') ADD(LEQ, 2);
				else             ADD(LESS, 1);
				break;
			case '>':
				if (p[1] == '=') ADD(MEQ, 2);
				else             ADD(MORE, 1);
				break;
			case '+': ADD(PLUS, 1); break;
			case '-':
				if (p[1] == '>')                     ADD(ARROW, 2);
				else if (p[1] == '-' && p[2] == '-') ADD(MINUS3, 3);
				else                                 ADD(MINUS, 1);
				break;
			case '*': ADD(STAR, 1); break;
			case '/':
				if (p[1] == '/') {
					while (*p != '\n' && *p != '\0') p++;
					continue;
				} else if (p[1] == '*') {
					int nest_level = 1;
					
					k = 2;
					while (p[k] != '\0') {
						if (p[k] == '/' && p[k+1] == '*') {
							nest_level++;
							k++;
						} else if (p[k] == '*' && p[k+1] == '/') {
							nest_level--;
							k++;
							if (nest_level == 0) {
								k++;
								break;
							}
						}
						k++;
					}
					
					if (nest_level != 0)
						return false; /* TODO: better diags */
					
					p += k;
					continue;
				} else
					ADD(SLASH, 1);
				break;
			case '.':
				if (p[1] == '.') ADD(DOT2, 2);
				else             ADD(DOT, 1);
				break;
			case ',': ADD(COMMA, 1); break;
			case ';': ADD(SEMI, 1); break;
			case '&':
				if (p[1] == '&') ADD(AND2, 2);
				else             ADD(AND, 1);
				break;
			case '|':
				if (p[1] != '|')
					return false; /* TODO: better diags */
				ADD(PIPE2, 2);
				break;
			case '#':
				if (p[1] != '_' && !isalpha(p[1]))
					return false; /* TODO: better diags */
				
				k = 2;
				while (p[k] == '_' || isalnum(p[k])) k++;
				
				ADD(DIRECTIVE, k);
				break;
			case '"':
				k = 1;
				while (p[k] != '\0' && (p[k] != '"' || p[k-1] == '\\')) k++;
				
				ADD(STRING, k+1);
				break;
			default:
				if (isdigit(*p)) {
					k = 1;
					while (isdigit(p[k])) k++;
					
					if (p[k] == '.' && isdigit(p[k+1])) {
						k++;
						while (isdigit(p[k])) k++;
						
						ADD(FLOAT, k);
					} else
						ADD(INT, k);
				} else if (*p == '_' || isalpha(*p)) {
					k = 1;
					while (p[k] == '_' || isalnum(p[k])) k++;
					
					ADD(ID, k);
				} else
					return false; /* TODO: better diags */
				break;
		}
		
		p += v->v[v->n-1].text.n;
	}
	
	vec_token_push(v, token_of(TOK_EOF, str_view(s.p+s.n, 0)));

	vec_token_shrink(v);

	return true;
	#undef ADD
}

enum ast_node_t {
	AN_NONE=-1,    /* missing optional element                   */
	AN_RUN_EXPR,   /* #run func()                                */
	AN_INT_LIT,    /* 123                                        */
	AN_FLOAT_LIT,  /* 123.45                                     */
	AN_STR_LIT,    /* "abc"                                      */
	AN_FUNC_LIT,   /* (x: int) -> float { foo(); return bar(); } */
	AN_STRUCT_LIT, /*                                            */
	AN_ID,         /* foo                                        */
	AN_OP1,        /* -x                                         */
	AN_OP2,        /* x + y                                      */
	AN_OP1N,       /* func(x, y)                                 */
	AN_VAR_DECL,   /* foo : Bar = baz;                           */
	AN__N
};

char* ast_node_t_names[] = {"RUN_EXPR", "INT", "FLOAT", "STR", "FUNC", "STRUCT", "ID", "OP1", "OP2", "CALL", "VAR_DECL"};

GS_ASSERT(sizeof(ast_node_t_names) == AN__N*sizeof(ast_node_t_names[0]));

enum op_t {
	OP_NONE=-1,
	OP_CALL,
	OP_INDEX,
	OP_DOT,
	OP_NEG,
	OP_NOT,
	OP_DEREF,
	OP_ADDR,
	OP_TIMES,
	OP_DIV,
	OP_MOD,
	OP_ADD,
	OP_SUB,
	OP_LESS,
	OP_LEQ ,
	OP_MORE,
	OP_MEQ,
	OP_EQ,
	OP_NEQ,
	OP_AND,
	OP_OR,
	OP__SENTINEL, /* fake operator used in ast construction */
	OP__N
};

char* op_t_names[] = {"CALL", "INDEX", "DOT", "NEG", "NOT", "DEREF", "ADDR", "TIMES", "DIV", "MOD", "ADD", "SUB", "LESS", "LEQ", "MORE", "MEQ", "EQ", "NEQ", "AND", "OR", "_SENTINEL"};

GS_ASSERT(sizeof(op_t_names) == OP__N*sizeof(op_t_names[0]));

int op_t_precedence[] = {8, 8, 8, 7, 7, 7, 7, 6, 6, 6, 5, 5, 4, 4, 4, 4, 3, 3, 2, 1, -1};

GS_ASSERT(sizeof(op_t_precedence) == OP__N*sizeof(op_t_precedence[0]));

struct ast_node;

#define VEC_TYPE struct ast_node*
#define VEC_TYPE_NAME past_node
#include "vec.c"

#define MAP_TYPE struct ast_node*
#define MAP_TYPE_NAME past_node
#include "map.c"

#define MAP_TYPE struct ast_node**
#define MAP_TYPE_NAME ppast_node
#include "map.c"

struct ast_op1 {
	enum op_t type;
	struct ast_node* child;
};

struct ast_op2 {
	enum op_t type;
	struct ast_node* left;
	struct ast_node* right;
};

struct ast_op1n {
	enum op_t type;
	struct ast_node* left;
	struct vec_past_node rights;
};

struct ast_node {
	enum ast_node_t type;
	union _ {
		uint64_t int_lit;
		double float_lit;
		struct str_view str_lit;
		struct str_view id;	
		struct ast_op1 op1;
		struct ast_op2 op2;
		struct ast_op1n op1n;
		/* TODO */
	} _;
};

void free_ast_node(struct ast_node* node)
{
	if (node == NULL) return;

	if (node->type == AN_OP1)
		free_ast_node(node->_.op1.child);
	else if (node->type == AN_OP2) {
		free_ast_node(node->_.op2.left);
		free_ast_node(node->_.op2.right);
	}

	free(node);
}

struct input {
	char* text;

	struct token* tok;
	size_t tok_n;

	size_t cur;
};

enum op_t tok_to_op1(enum token_t t)
{
	switch (t) {
		case TOK_MINUS:  return OP_NEG;
		case TOK_BANG:   return OP_NOT;
		case TOK_STAR:   return OP_DEREF;
		case TOK_AND:    return OP_ADDR;
		default:         return OP_NONE;
	}
}

enum op_t tok_to_op2(enum token_t t)
{
	switch (t) {
		case TOK_BANGEQ: return OP_NEQ;
		case TOK_EQ2:    return OP_EQ;
		case TOK_LESS:   return OP_LESS;
		case TOK_LEQ:    return OP_LEQ;
		case TOK_MORE:   return OP_MORE;
		case TOK_MEQ:    return OP_MEQ;
		case TOK_PLUS:   return OP_ADD;
		case TOK_MINUS:  return OP_SUB;
		case TOK_STAR:   return OP_TIMES;
		case TOK_SLASH:  return OP_DIV;
		case TOK_DOT:    return OP_DOT;
		case TOK_AND2:   return OP_AND;
		case TOK_PIPE2:  return OP_OR;
		default:         return OP_NONE;
	}
}

bool parse_uint64_t(struct str_view text, uint64_t* result)
{
	size_t i;
	uint64_t r;

	if (text.n == 0) return false;
	if (text.n > 20) return false;
	if (text.n == 20 && strncmp("18446744073709551615", text.p, text.n) < 0) return false;
	
	r = 0;
	for (i=0; i<text.n; i++) {
		if (!isdigit(text.p[i]))
			return false;
		r = r*10 + (size_t)(text.p[i] - '0');
	}

	*result = r;
	return true;
}

bool parse_double(struct str_view text, double* result)
{
	double r;
	bool success;
	char* tmp;
       
	tmp = malloc(text.n+1);
	strncpy(tmp, text.p, text.n);
	tmp[text.n] = '\0';

	errno = 0;
	r = strtod(tmp, NULL);
	success = !errno;

	free(tmp);

	if (success)
		*result = r;

	return success;
}

struct ast_node* parse_expr(struct input* input);
void print_ast(struct ast_node* an);

struct ast_node* parse_term(struct input* input, struct map_past_node* parent)
{
	struct ast_node* an = malloc(sizeof(struct ast_node));
	struct token* t = &input->tok[input->cur++];
	enum op_t op;

	if (t->type == TOK_INT) {
		an->type = AN_INT_LIT;
		if (!parse_uint64_t(t->text, &an->_.int_lit))
			goto err;
	} else if (t->type == TOK_FLOAT) {
		an->type = AN_FLOAT_LIT;
		if (!parse_double(t->text, &an->_.float_lit))
			goto err;
	} else if (t->type == TOK_STRING) {
		an->type = AN_STR_LIT;
		an->_.str_lit = str_view(t->text.p+1, t->text.n-2);
	} else if (t->type == TOK_ID) {
		an->type = AN_ID;
		an->_.id = t->text;
	} else if ((op = tok_to_op1(t->type)) != OP_NONE) {
		an->type = AN_OP1;
		an->_.op1.type = op;
		an->_.op1.child = parse_term(input, parent);
		map_past_node_add(parent, an->_.op1.child, an);
	} else if (t->type == TOK_LPAREN) {
		an = parse_expr(input);
		if (input->tok[input->cur++].type != TOK_RPAREN)
			goto err;
	} else goto err;

	return an;
err:
	free_ast_node(an);
	return NULL; /* TODO: better diags */
}

struct ast_node* parse_expr(struct input* input)
{
#	define t (input->tok[input->cur])

	/* TODO optimization: use a map that doesn't allocate constantly, share it between calls */
	struct map_past_node parent = map_past_node_make();
	struct map_ppast_node slot = map_ppast_node_make();
	struct ast_node* cur_term;
	struct ast_node* root;
	struct ast_node** cur_slot;
	struct ast_node** ppar;
	enum op_t op;

	root = malloc(sizeof(struct ast_node));
	root->type = AN_OP1;
	root->_.op1.type = OP__SENTINEL;
	cur_slot = &root->_.op1.child;
	cur_term = root;

	map_ppast_node_add(&slot, root, &root);

	while (true) {
		/* unary prefix operators */
		if ((op = tok_to_op1(t.type)) != OP_NONE) {
			input->cur++;
			*cur_slot = malloc(sizeof(struct ast_node));
			map_past_node_add(&parent, *cur_slot, cur_term);
			map_ppast_node_add(&slot, *cur_slot, cur_slot);
			cur_term = *cur_slot;
			cur_term->type = AN_OP1;
			cur_term->_.op1.type = op;
			cur_slot = &cur_term->_.op1.child;
			continue;
		}

		/* term (literal, identifier, or subexpression) */
		if (t.type == TOK_LPAREN) {
			input->cur++;
			*cur_slot = parse_expr(input);
			if (*cur_slot == NULL)
				goto err; /* TODO: better diags */
			map_past_node_add(&parent, *cur_slot, cur_term);
			map_ppast_node_add(&slot, *cur_slot, cur_slot);
			cur_term = *cur_slot;

			if (t.type != TOK_RPAREN)
				goto err; /* TODO: better diags */
		} else {
			*cur_slot = malloc(sizeof(struct ast_node));
			map_past_node_add(&parent, *cur_slot, cur_term);
			map_ppast_node_add(&slot, *cur_slot, cur_slot);
			cur_term = *cur_slot;

			if (t.type == TOK_ID) {
				cur_term->type = AN_ID;
				cur_term->_.id = t.text;
			} else if (t.type == TOK_INT) {
				cur_term->type = AN_INT_LIT;
				if (!parse_uint64_t(t.text, &cur_term->_.int_lit))
					goto err; /* TODO: better diags */
			} else if (t.type == TOK_FLOAT) {
				cur_term->type = AN_FLOAT_LIT;
				if (!parse_double(t.text, &cur_term->_.float_lit))
					goto err; /* TODO: better diags */
			} else if (t.type == TOK_STRING) {
				cur_term->type = AN_STR_LIT;
				cur_term->_.str_lit = str_view(t.text.p+1, t.text.n-2);
			} else { /* TODO: func literals */
				goto err; /* TODO: better diags */
			}
		}
		input->cur++;

		/* operators with superunary precedence (call, subscript, dot) */
		while (true) {
			struct ast_node* an = malloc(sizeof(struct ast_node));

			if (t.type == TOK_LPAREN) {
				input->cur++;

				while ((ppar = map_past_node_get(&parent, cur_term))) {
					if (op_t_precedence[(**ppar)._.op1.type] < op_t_precedence[OP_CALL]) break;
					cur_term = *ppar;
				}

				an->type = AN_OP1N;
				an->_.op1n.type = OP_CALL;
				an->_.op1n.left = cur_term;
				an->_.op1n.rights = vec_past_node_make(10);
				
				if (ppar) map_past_node_add(&parent, an, *ppar);
				map_past_node_add(&parent, cur_term, an);

				cur_slot = *map_ppast_node_get(&slot, cur_term);
				*cur_slot = an;
				map_ppast_node_add(&slot, *cur_slot, cur_slot);

				while (t.type != TOK_RPAREN) {
					cur_term = parse_expr(input);
					if (cur_term == NULL)
						goto err; /* TODO: better diags */

					vec_past_node_push(&an->_.op1n.rights, cur_term);

					/* map_ppast_node_add(&slot, cur_term, &an->_.op1n.rights.v[an->_.op1n.rights.n-1]); */

					if (t.type == TOK_COMMA)
						input->cur++;
				}

				cur_term = an;
			} else if (t.type == TOK_LBRACKET) {
				input->cur++;

				while ((ppar = map_past_node_get(&parent, cur_term))) {
					if (op_t_precedence[(**ppar)._.op1.type] < op_t_precedence[OP_INDEX]) break;
					cur_term = *ppar;
				}

				an->type = AN_OP2;
				an->_.op2.type = OP_INDEX;
				an->_.op2.left = cur_term;
				
				if (ppar) map_past_node_add(&parent, an, *ppar);
				map_past_node_add(&parent, cur_term, an);

				cur_slot = *map_ppast_node_get(&slot, cur_term);
				*cur_slot = an;
				map_ppast_node_add(&slot, *cur_slot, cur_slot);

				an->_.op2.right = parse_expr(input);
				if (an->_.op2.right == NULL)
					goto err; /* TODO: better diags */

				if (t.type != TOK_RBRACKET)
					goto err; /* TODO: better diags */
			} else if (t.type == TOK_DOT) {
				while ((ppar = map_past_node_get(&parent, cur_term))) {
					if (op_t_precedence[(**ppar)._.op1.type] < op_t_precedence[OP_DOT]) break;
					cur_term = *ppar;
				}

				an->type = AN_OP2;
				an->_.op2.type = OP_DOT;
				an->_.op2.left = cur_term;

				if (ppar) map_past_node_add(&parent, an, *ppar);
				map_past_node_add(&parent, cur_term, an);

				cur_slot = *map_ppast_node_get(&slot, cur_term);
				*cur_slot = an;
				map_ppast_node_add(&slot, *cur_slot, cur_slot);

				cur_term = an;
				cur_slot = &an->_.op2.right;

				input->cur++;
				if (t.type != TOK_ID)
					goto err; /* TODO: better diags */
				
				an = malloc(sizeof(struct ast_node));
				an->type = AN_ID;
				an->_.id = t.text;

				map_past_node_add(&parent, an, cur_term);
				*cur_slot = an;
			} else {
				free(an); /* the just allocated one */
				break;
			}

			input->cur++;
		}

		/* binary operators with subunary precedence */
		{
			struct ast_node* an;

			op = tok_to_op2(t.type);
			if (op == OP_NONE)
				break;
			
			input->cur++;

			while ((ppar = map_past_node_get(&parent, cur_term))) {
				if (op_t_precedence[(**ppar)._.op1.type] < op_t_precedence[op]) break;
				cur_term = *ppar;
			}

			an = malloc(sizeof(struct ast_node));
			an->type = AN_OP2;
			an->_.op2.type = op;
			an->_.op2.left = cur_term;

			if (ppar) map_past_node_add(&parent, an, *ppar);
			map_past_node_add(&parent, cur_term, an);

			cur_slot = *map_ppast_node_get(&slot, cur_term);
			*cur_slot = an;
			map_ppast_node_add(&slot, *cur_slot, cur_slot);

			cur_term = an;
			cur_slot = &an->_.op2.right;

			/* print_ast(cur_term);printf("\n"); */
		}
	}

	/*{
		size_t i, j;
		for (i=0; i<parent.buckets_n; i++) {
			if (parent.buckets[i].n > 0) {
				printf("Parent for  ");
				print_ast(parent.buckets[i].inline_obj.key);
				printf("  is  ");
				print_ast(parent.buckets[i].inline_obj.val);
				printf("\n");
			}
			for (j=0; j+1<parent.buckets[i].n; j++) {
				printf("Parent for  ");
				print_ast(parent.buckets[i].dynamic_obj[j].key);
				printf("  is  ");
				print_ast(parent.buckets[i].dynamic_obj[j].val);
				printf("\n");
			}
		}

	}*/

	{
		struct ast_node* an = root->_.op1.child;
		free(root);
		root = an;
	}

	map_ppast_node_destroy(&slot);
	map_past_node_destroy(&parent);
	return root;

err:
	/* TODO */
	return NULL;

#	undef t
}

void print_ast(struct ast_node* an)
{
	if (an == NULL)
		printf("NULL[]");
	else if (an->type == AN_INT_LIT)
		printf("INT_%u[]", (uint32_t) an->_.int_lit);
	else if (an->type == AN_FLOAT_LIT)
		printf("FLOAT_%f[]", an->_.float_lit);
	else if (an->type == AN_ID)
		printf("ID_%.*s[]", (int) an->_.id.n, an->_.id.p);
	else if (an->type == AN_OP1) {
		printf("OP1_%s[", op_t_names[an->_.op1.type]);
		print_ast(an->_.op1.child);
		printf("]");
	} else if (an->type == AN_OP2) {
		printf("OP2_%s[", op_t_names[an->_.op2.type]);
		print_ast(an->_.op2.left);
		print_ast(an->_.op2.right);
		printf("]");
	} else if (an->type == AN_OP1N) {
		size_t i;
		printf("OP1N_%s[", op_t_names[an->_.op1n.type]);
		print_ast(an->_.op1n.left);
		for (i=0; i<an->_.op1n.rights.n; i++)
			print_ast(an->_.op1n.rights.v[i]);
		printf("]");
	} else {
		printf("TODO[]");
		/* TODO */
	}
}

int main(int argc, char** argv)
{
	/*size_t i;*/
	struct str text;
	struct vec_token tokens = vec_token_make(20);
	struct ast_node* ast;
	struct input input;

	if (argc != 2) {
		fputs("Must provide exactly one filename as argument.\n", stderr);
		return 1;
	}

	text = read_all(argv[1]);
	if (text.p == NULL) {
		fputs("Error reading file.\n", stderr);
		return 1;
	}

	if (!lex(str_view_str(text), &tokens)) {
		fputs("Lexing failed.\n", stderr);
		return 1;
	}

	/* for (i=0; i<tokens.n; i++)
		printf("%-20s %.*s\n", token_t_names[tokens.v[i].type], (int) tokens.v[i].text.n, tokens.v[i].text.p); */
	
	input.tok = tokens.v;
	input.tok_n = tokens.n;
	input.cur = 0;
	input.text = text.p;

	ast = parse_expr(&input);
	if (ast == NULL) {
		fputs("Parsing failed.\n", stderr);
		return 1;
	}

	print_ast(ast);
	puts("");

	vec_token_destroy(&tokens);
	return 0;
}
