#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <errno.h>
#include "util.h"
#include "bits.c"

#define VEC_TYPE void*
#define VEC_TYPE_NAME pvoid
#include "vec.c"

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
	TOK_DOT3,      /*  ...          */
	TOK_COMMA,     /*  ,            */
	TOK_SEMI,      /*  ;            */
	TOK_AND,       /*  &            */
	TOK_AND2,      /*  &&           */
	TOK_PIPE2,     /*  ||           */
	TOK_HASH,      /*  #            */
	TOK_AT,        /*  @            */
	TOK_INT,       /*  123          */
	TOK_FLOAT,     /*  123.45       */
	TOK_STRING,    /*  "abc"        */
	TOK_ID,        /*  identifier   */
	TOK_EOF,       /*  end-of-file  */
	TOK__N
};

char* token_t_names[] = {"LPAREN","RPAREN","LBRACKET","RBRACKET","LBRACE","RBRACE","COLON","BANG","BANGEQ","EQ","EQ2","LESS","LEQ","MORE","MEQ","PLUS","MINUS","MINUS3","ARROW","STAR","SLASH","DOT","DOT2","DOT3","COMMA","SEMI","AND","AND2","PIPE2","HASH", "AT","INT","FLOAT","STRING","ID","EOF"};

GS_ASSERT(sizeof(token_t_names) == TOK__N*sizeof(token_t_names[0]));

size_t token_t_len[] = {1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, SZ_MAX, SZ_MAX, SZ_MAX, SZ_MAX, 0};

GS_ASSERT(sizeof(token_t_len) == TOK__N*sizeof(token_t_len[0]));

struct token {
	enum token_t type;
	struct str_view text;
};

#define VEC_TYPE struct token
#define VEC_TYPE_NAME token
#include "vec.c"

#define VEC_TYPE struct token*
#define VEC_TYPE_NAME ptoken
#include "vec.c"

#define MAP_TYPE struct token*
#define MAP_TYPE_NAME ptoken
#include "map.c"

struct token token_of(enum token_t type, struct str_view text)
{
	struct token t;
	t.type = type;
	t.text = text;
	return t;
}

struct input {
	struct str_view text;

	struct token* tok;
	size_t tok_n;

	struct token* cur;

	struct map_ptoken* paren_pairs;
};

enum diag_t {
	DIAG_ERR,
	DIAG_WARN
};

struct diag {
	enum diag_t level;
	struct str_view text;
	char* p;
	char* msg;
};

#define VEC_TYPE struct diag
#define VEC_TYPE_NAME diag
#include "vec.c"

struct vec_diag diag_stack;

void diag(enum diag_t level, struct str_view text, char* p, char* msg)
{
	struct diag d;
	d.level = level;
	d.text = text;
	d.p = p;
	d.msg = msg;
	vec_diag_push(&diag_stack, d);
}

#define DIAG(Level, Msg) diag(DIAG_##Level, input->text, input->cur->text.p, Msg)

#define DIAGHARD(Result, Level, Msg) do { DIAG(Level, Msg); RET(Result); } while(0)
#define DIAGSOFT(Result, Level, Msg) do { DIAG(Level, Msg); result = Result; } while(0)

void print_diag(struct diag* d)
{
	char* l,* r;

	fprintf(stderr, d->level == DIAG_ERR ? "ERROR " : "WARNING ");
	fprintf(stderr, "@ %lu : %s\n", (unsigned long) (d->p - d->text.p), d->msg);
	
	if (d->p == NULL) return;

	l = r = d->p;
	while (l >= d->text.p && *l != '\n') l--;
	while (r < d->text.p+d->text.n && *r != '\n') r++;

	l++;

	fprintf(stderr, "\t%.*s\n", (int) (r-l), l);
	fprintf(stderr, "\t%*c\n", (int) (d->p - l + 1), '^');
}

bool lex(struct str_view text, struct vec_token* v, struct map_ptoken* paren_pairs)
{
#	define add(Kind)       vec_token_push(v, token_of(TOK_##Kind, str_view(p, token_t_len[TOK_##Kind])))
#	define addl(Kind, Len) vec_token_push(v, token_of(TOK_##Kind, str_view(p, Len)))

	bool result = true;
	char* p = text.p; /* TODO: respect s.n */
	size_t k;
	struct vec_ptoken paren_stack = vec_ptoken_make(10);
	
	while (*p) {
		while (isspace(*p)) p++;
		if (!*p) break;
		
		switch (*p) {
			case '(':
				add(LPAREN);
				vec_ptoken_push(&paren_stack, &v->v[v->n-1]);
				break;
			case ')':
				add(RPAREN);
				if (paren_stack.n == 0) {
					diag(DIAG_ERR, text, p, "Closing parenthesis has no opening pair.");
					result = false;
				} else {
					struct token* pair = vec_ptoken_pop(&paren_stack);
					map_ptoken_add(paren_pairs, &v->v[v->n-1], pair);
					map_ptoken_add(paren_pairs, pair, &v->v[v->n-1]);
					/* TODO: should we only add needed pairs (ones followed by '->' or '{') ? */
				}
				break;
			case '[': add(LBRACKET); break;
			case ']': add(RBRACKET); break;
			case '{': add(LBRACE); break;
			case '}': add(RBRACE); break;
			case ':': add(COLON); break;
			case '!':
				if (p[1] == '=') add(BANGEQ);
				else             add(BANG);
			case '=':
				if (p[1] == '=') add(EQ2);
				else             add(EQ);
				break;
			case '<':
				if (p[1] == '=') add(LEQ);
				else             add(LESS);
				break;
			case '>':
				if (p[1] == '=') add(MEQ);
				else             add(MORE);
				break;
			case '+': add(PLUS); break;
			case '-':
				if (p[1] == '>')                     add(ARROW);
				else if (p[1] == '-' && p[2] == '-') add(MINUS3);
				else                                 add(MINUS);
				break;
			case '*': add(STAR); break;
			case '/':
				if (p[1] == '/') {
					while (*p != '\n' && *p != '\0') p++;
					continue;
				} else if (p[1] == '*') {
					struct vec_pvoid nesting = vec_pvoid_make(10);
					vec_pvoid_push(&nesting, p);
					
					k = 2;
					while (p[k] != '\0') {
						if (p[k] == '/' && p[k+1] == '*') {
							vec_pvoid_push(&nesting, &p[k]);
							k++;
						} else if (p[k] == '*' && p[k+1] == '/') {
							vec_pvoid_pop(&nesting);
							k++;
							if (nesting.n == 0) {
								k++;
								break;
							}
						}
						k++;
					}
					
					if (nesting.n != 0) {
						size_t i;
						for (i=0; i<nesting.n; i++)
							diag(DIAG_ERR, text, nesting.v[i], "Unclosed block comment.");
						vec_pvoid_destroy(&nesting);
						RET(false);
					}
					
					vec_pvoid_destroy(&nesting);

					p += k;
					continue;
				} else
					add(SLASH);
				break;
			case '.':
				if (p[1] == '.')
					if (p[2] == '.') add(DOT3);
					else             add(DOT2);
				else                     add(DOT);
				break;
			case ',': add(COMMA); break;
			case ';': add(SEMI); break;
			case '&':
				if (p[1] == '&') add(AND2);
				else             add(AND);
				break;
			case '|':
				if (p[1] != '|') {
					diag(DIAG_ERR, text, p+1, "Expected another '|' character.");
					result = false;
				}
						
				add(PIPE2);
				break;
			case '#': add(HASH); break;
			case '@': add(AT); break;
			case '"':
				k = 1;
				while (p[k] != '\0' && (p[k] != '"' || p[k-1] == '\\')) k++;
				
				addl(STRING, k+1);
				break;
			default:
				if (isdigit(*p)) {
					k = 1;
					while (isdigit(p[k])) k++;
					
					if (p[k] == '.' && isdigit(p[k+1])) {
						k++;
						while (isdigit(p[k])) k++;
						
						addl(FLOAT, k);
					} else
						addl(INT, k);
				} else if (*p == '_' || isalpha(*p)) {
					k = 1;
					while (p[k] == '_' || isalnum(p[k])) k++;
					
					addl(ID, k);
				} else {
					diag(DIAG_ERR, text, p, "Unexpected character.");
					result = false;
				}
				break;
		}
		
		p += v->v[v->n-1].text.n;
	}
	
	vec_token_push(v, token_of(TOK_EOF, str_view(text.p+text.n, 0)));
	vec_token_shrink(v);
end:
	return result;

#	undef add
#	undef addl
}

enum ast_node_t {
	AN_NONE=-1,    /* missing optional element                   */
	AN_RUN_EXPR,   /* #run func()                                */
	AN_INT_LIT,    /* 123                                        */
	AN_FLOAT_LIT,  /* 123.45                                     */
	AN_STR_LIT,    /* "abc"                                      */
	AN_FUNC_LIT,   /* (x: int) -> float { foo(); return bar(); } */
	AN_PARAM,      /* x: int                                     */
	AN_STRUCT_LIT, /*                                            */
	AN_ID,         /* foo                                        */
	AN_OP1,        /* -x                                         */
	AN_OP2,        /* x + y                                      */
	AN_OP1N,       /* func(x, y)                                 */
	AN_DECL,       /* foo : Bar = baz;  foo : Bar : baz;         */
	AN__N
};

char* ast_node_t_names[] = {"RUN_EXPR", "INT", "FLOAT", "STR", "FUNC", "PARAM", "STRUCT", "ID", "OP1", "OP2", "CALL", "VAR_DECL"};

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

struct ast_decl {
	bool is_const;
	struct str_view name;
	struct str_view type;
	struct ast_node* init;
};

struct ast_param {
	struct str_view name;
	struct str_view type;
};

struct ast_func {
	struct vec_past_node params;
	struct str_view ret_type;
	struct ast_node* body;
	/* TODO: modifiers */
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
		struct ast_decl decl;
		struct ast_func func;
		struct ast_param param;
		/* TODO */
	} _;
};

void free_ast_node(struct ast_node* node)
{
	size_t i;

	if (node == NULL) return;

	if (node->type == AN_OP1)
		free_ast_node(node->_.op1.child);
	else if (node->type == AN_OP2) {
		free_ast_node(node->_.op2.left);
		free_ast_node(node->_.op2.right);
	} else if (node->type == AN_OP1N) {
		free_ast_node(node->_.op1n.left);
		for (i=0; i<node->_.op1n.rights.n; i++)
			free_ast_node(node->_.op1n.rights.v[i]);
		vec_past_node_destroy(&node->_.op1n.rights);
	} else if (node->type == AN_DECL) {
		free_ast_node(node->_.decl.init);
	} else if (node->type == AN_FUNC_LIT) {
		for (i=0; i<node->_.func.params.n; i++)
			free_ast_node(node->_.func.params.v[i]);
		vec_past_node_destroy(&node->_.func.params);
		free_ast_node(node->_.func.body);
	} else if (node->type != AN_NONE &&
	           node->type != AN_INT_LIT &&
		   node->type != AN_FLOAT_LIT &&
		   node->type != AN_STR_LIT &&
		   node->type != AN_ID &&
		   node->type != AN_PARAM)
		assertl(false);

	free(node);
}

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

struct ast_node* parse_expr(struct input* input)
{
#	define t (*input->cur)

	/* TODO optimization: use a map that doesn't allocate constantly, share it between calls */
	struct input orig_input = *input;
	struct ast_node* result;
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

	result = root;

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
				DIAGHARD(NULL, ERR, "Expected valid expression in the parentheses.");

			map_past_node_add(&parent, *cur_slot, cur_term);
			map_ppast_node_add(&slot, *cur_slot, cur_slot);
			cur_term = *cur_slot;

			if (t.type != TOK_RPAREN)
				DIAGHARD(NULL, ERR, "Expected ')' after subexpression.");
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
					DIAGSOFT(NULL, ERR, "Not a valid integer literal (too big?).");
			} else if (t.type == TOK_FLOAT) {
				cur_term->type = AN_FLOAT_LIT;
				if (!parse_double(t.text, &cur_term->_.float_lit))
					DIAGSOFT(NULL, ERR, "Not a valid floating-point literal.");
			} else if (t.type == TOK_STRING) {
				cur_term->type = AN_STR_LIT;
				cur_term->_.str_lit = str_view(t.text.p+1, t.text.n-2);
			} else { /* TODO: func literals */
				cur_term->type = AN_NONE;
				DIAGHARD(NULL, ERR, "Expected subexpression between '(' and ')', identifier, or literal.");
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
						DIAGHARD(NULL, ERR, "Expected valid expression as call argument.");

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
					DIAGHARD(NULL, ERR, "Expected valid expression as index.");

				if (t.type != TOK_RBRACKET)
					DIAGHARD(NULL, ERR, "Expected ']'.");
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
					DIAGHARD(NULL, ERR, "Operator '.' must be followed by identifier.");
				
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
			an->_.op2.right = NULL;

			if (ppar) map_past_node_add(&parent, an, *ppar);
			map_past_node_add(&parent, cur_term, an);

			cur_slot = *map_ppast_node_get(&slot, cur_term);
			*cur_slot = an;
			map_ppast_node_add(&slot, *cur_slot, cur_slot);

			cur_term = an;
			cur_slot = &an->_.op2.right;
		}
	}

end:
	if (result) {
		result = root->_.op1.child;
		free(root);
	} else {
		free_ast_node(root);
		*input = orig_input;
	}

	map_ppast_node_destroy(&slot);
	map_past_node_destroy(&parent);
	return result;

#	undef t
}

struct ast_node* parse_code_block(struct input* input)
{
	struct ast_node* an = malloc(sizeof(struct ast_node));
	struct ast_node* result = an;

	an->type = AN_NONE; /* TODO */

	if (input->cur->type != TOK_LBRACE)
		DIAGHARD(NULL, ERR, "Expected '{'.");

	input->cur++;

	/* TODO */

	if (input->cur->type != TOK_RBRACE)
		DIAGHARD(NULL, ERR, "Expected '}'.");
end:
	if (result == NULL)
		free_ast_node(an);
	return result;
}

struct ast_node* parse_func_literal(struct input* input)
{
	struct ast_node* an = malloc(sizeof(struct ast_node));
	struct ast_node* result = an;
	struct ast_node* param = NULL;

	an->type = AN_FUNC_LIT;
	an->_.func.params = vec_past_node_make(1);
	an->_.func.body = NULL;

	if (input->cur->type != TOK_LPAREN)
		DIAGHARD(NULL, ERR, "Expected parenthesized parameter list at beginning of function literal.");

	input->cur++;

	while (input->cur->type != TOK_RPAREN) {
		param = malloc(sizeof(struct ast_node));
		param->type = AN_PARAM;

		if (input->cur->type != TOK_ID)
			DIAGHARD(NULL, ERR, "Expected parameter name.");

		param->_.param.name = input->cur->text;

		input->cur++;
		if (input->cur->type != TOK_COLON)
			DIAGHARD(NULL, ERR, "Expected colon.");

		input->cur++;
		
		if (input->cur->type != TOK_ID)
			DIAGHARD(NULL, ERR, "Expected parameter type name.");

		param->_.param.type = input->cur->text;

		vec_past_node_push(&an->_.func.params, param);
		input->cur++;

		if (input->cur->type == TOK_COMMA)
			input->cur++;
	}
	param = NULL;
	input->cur++;

	if (input->cur->type != TOK_ARROW) {
		/* TODO: allow implicit return type? */
		DIAGHARD(NULL, ERR, "Expected '->' and return type after parameter list.");
	}
	input->cur++;

	if (input->cur->type != TOK_ID)
		DIAGHARD(NULL, ERR, "Expected '->' and return type after parameter list.");

	an->_.func.ret_type = input->cur->text;
	input->cur++;

	/* TODO: modifiers */

	if (input->cur->type != TOK_LBRACE)
		DIAGHARD(NULL, ERR, "Expected function body between braces.");

	an->_.func.body = parse_code_block(input);
	if (an->_.func.body == NULL)
		RET(NULL);

end:
	if (result == NULL) {
		free(param);
		free_ast_node(an);
	}
	return result;
}

struct ast_node* parse_decl(struct input* input)
{
#	define t (*input->cur)

	struct ast_node* an = malloc(sizeof(struct ast_node));
	struct ast_node* result = an;
	
	an->type = AN_DECL;
	an->_.decl.type = str_view(NULL, 0);
	an->_.decl.init = NULL;

	if (t.type != TOK_ID)
		DIAGHARD(NULL, ERR, "Expected identifier.");

	an->_.decl.name = t.text;

	input->cur++;
	if (t.type != TOK_COLON)
		DIAGHARD(NULL, ERR, "Expected ':'.");

	input->cur++;
	if (t.type == TOK_ID) {
		an->_.decl.type = t.text;
		input->cur++;
	}

	if (t.type == TOK_EQ || t.type == TOK_COLON) {
		an->_.decl.is_const = t.type==TOK_COLON;
		input->cur++;

		/* TODO: allow function literals in expressions, not just as self-standing initializers */
		if (t.type == TOK_LPAREN) {
			struct token** pair = map_ptoken_get(input->paren_pairs, &t);
			assertl(pair != NULL);

			if ((*pair)[1].type == TOK_ARROW || (*pair)[1].type == TOK_LBRACE) {
				an->_.decl.init = parse_func_literal(input /* TODO */);
				if (an->_.decl.init == NULL)
					DIAGHARD(NULL, ERR, "Expected valid function literal.");
			}
		}

		if (an->_.decl.init == NULL) {
			an->_.decl.init = parse_expr(input);
			if (an->_.decl.init == NULL)
				DIAGHARD(NULL, ERR, "Expected valid expression as initializer.");
		}
	} else {
		if (an->_.decl.type.n == 0)
			DIAGHARD(NULL, ERR, "Expected ':' or '='.");
	}

end:
	if (result == NULL) free_ast_node(an);
	return result;

#	undef t
}

void print_ast(struct ast_node* an)
{
	size_t i;

	if (an == NULL)
		printf("'NULL'");
	else if (an->type == AN_NONE)
		printf("'NONE'");
	else if (an->type == AN_INT_LIT)
		printf("'INT: %u'", (uint32_t) an->_.int_lit);
	else if (an->type == AN_FLOAT_LIT)
		printf("'FLOAT: %f'", an->_.float_lit);
	else if (an->type == AN_ID)
		printf("'ID: %.*s'", (int) an->_.id.n, an->_.id.p);
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
		printf("OP1N_%s[", op_t_names[an->_.op1n.type]);
		print_ast(an->_.op1n.left);
		for (i=0; i<an->_.op1n.rights.n; i++)
			print_ast(an->_.op1n.rights.v[i]);
		printf("]");
	} else if (an->type == AN_DECL) {
		printf("DECL_%s", an->_.decl.is_const ? "CONST" : "VAR");
		printf("['%.*s'", (int) an->_.decl.name.n, an->_.decl.name.p);
	
		if (an->_.decl.type.n > 0)
			printf("'%.*s'", (int) an->_.decl.type.n, an->_.decl.type.p);
		else
			printf("'<auto>'");

		if (an->_.decl.init) print_ast(an->_.decl.init);
		printf("]");
	} else if (an->type == AN_FUNC_LIT) {
		printf("FUNC['%.*s'", (int) an->_.func.ret_type.n, an->_.func.ret_type.p);
		for (i=0; i<an->_.func.params.n; i++)
			print_ast(an->_.func.params.v[i]);
		print_ast(an->_.func.body);
		printf("]");
	} else if (an->type == AN_PARAM) {
		printf("PARAM['%.*s''%.*s']", (int) an->_.param.name.n, an->_.param.name.p,
		                              (int) an->_.param.type.n, an->_.param.type.p);
	} else {
		printf("TODO[]");
		/* TODO */
	}
}

#define VEC_TYPE uint64_t
#define VEC_TYPE_NAME u64
#include "vec.c"

enum instruction
{
	IN_NOP,
	IN_DIE,
	IN_MVI, /* to, fromptr */
	IN_MOV, /* to, from    */
	IN_ADD, /* to, from    */
	IN_SUB, /* to, from    */
	IN_MUL, /* to, from    */
	IN_DIV, /* to, from    */
	IN_MOD, /* to, from    */
	IN_CMP, /* left, right (result goes into reg 0) */
	IN_IN,  /* to, from    */
	IN_OUT, /* to, from    */
	IN_JMP, /* to          */
	IN_JZ,  /* reg, to     */
	IN__N
};

uint64_t alloc_reg(struct vec_u64* regmap /*array of bits, 0=used, 1=free*/)
{
	size_t i;
	for (i=0; i<regmap->n; i++) {
		unsigned k = bit_ffs(regmap->v[i]);
		if (k) {
			k--; /* ffs(2**n)==n+1 */
			regmap->v[i] &= ~(1 << k);
			return i*64 + k;
		}
	}
	vec_u64_push(regmap, (uint64_t) ~1);
	return (regmap->n - 1) * 64;
}

void free_reg(struct vec_u64* regmap, uint64_t reg)
{
	uint64_t i=reg/64, k=reg%64;
	assertl((regmap->v[i] & (1<<k)) == 0);
	regmap->v[i] |= (1<<k);
}

void run_vm(uint64_t* code, uint64_t* regs)
{
	uint64_t* p = code;
	while(1) {
		switch(*p) {
			case IN_NOP: p++; break;
			case IN_DIE: return;
			case IN_MVI: regs[p[1]]  = regs[regs[p[2]]]; p += 3; break;
			case IN_MOV: regs[p[1]]  = regs[p[2]]; p += 3; break;
			case IN_ADD: regs[p[1]] += regs[p[2]]; p += 3; break;
			case IN_SUB: regs[p[1]] -= regs[p[2]]; p += 3; break;
			case IN_MUL: regs[p[1]] *= regs[p[2]]; p += 3; break;
			case IN_DIV: regs[p[1]] /= regs[p[2]]; p += 3; break;
			case IN_MOD: regs[p[1]] %= regs[p[2]]; p += 3; break;
			case IN_CMP:
				regs[0] = (uint64_t)(((regs[p[1]] < regs[p[2]]) << 1) | (regs[p[1]] > regs[p[2]]));
				p += 3;
				break;
			case IN_IN:
				assertl(p[2] == 0); /*only port 0 for now*/
				printf("> ");
				assertl(scanf(" %ld", &regs[p[1]]) == 1);
				p += 3;
				break;
			case IN_OUT:
				assertl(p[1] == 0); /*only port 0 for now*/
				printf("%ld\n", regs[p[2]]);
				p += 3;
				break;
			case IN_JMP:
				p = code + p[1];
				break;
			case IN_JZ:
				if (regs[p[1]] == 0)
					p = code + p[2];
				else
					p += 3;
				break;
			default:
				assertl(false);
				return; /* TODO: signal an error */
		}
	}
}

int main(int argc, char** argv)
{
	size_t i;
	int result = 0;
	bool lex_success;
	struct str text;
	struct vec_token tokens = vec_token_make(20);
	struct map_ptoken paren_pairs = map_ptoken_make();
	struct ast_node* ast=NULL;
	struct input input;

	diag_stack = vec_diag_make(1);

	if (argc != 2) {
		fputs("Must provide exactly one filename as argument.\n", stderr);
		RET(1);
	}

	text = read_all(argv[1]);
	if (text.p == NULL) {
		fputs("Error reading file.\n", stderr);
		RET(1);
	}

	lex_success = lex(str_view_str(text), &tokens, &paren_pairs);

	for (i=0; i<diag_stack.n; i++)
		print_diag(&diag_stack.v[i]);
	diag_stack.n = 0;

	if (!lex_success) {
		fputs("Lexing failed.\n", stderr);
		RET(1);
	}

	/* for (i=0; i<tokens.n; i++)
		printf("%-20s %.*s\n", token_t_names[tokens.v[i].type], (int) tokens.v[i].text.n, tokens.v[i].text.p); */
	
	input.tok = tokens.v;
	input.tok_n = tokens.n;
	input.cur = tokens.v;
	input.paren_pairs = &paren_pairs;
	input.text = str_view_str(text);

	ast = parse_expr(&input);
	
	for (i=0; i<diag_stack.n; i++)
		print_diag(&diag_stack.v[i]);
	diag_stack.n = 0;

	if (ast == NULL) {
		fputs("Parsing failed.\n", stderr);
		RET(1);
	}

	print_ast(ast);
	puts("");

	/* temporary vm test */
	{
		uint64_t regs[10] = {10, 20, 0};
		uint64_t code[] = {
			IN_IN, 5, 0,
			IN_NOP,
			IN_IN, 6, 0,
			IN_ADD, 6, 5,
			IN_OUT, 0, 6,
			IN_DIE
		};
		
		for (i=0; i<10; i++) printf("%2ld ", regs[i]); printf("\n");
		run_vm(code, regs);
		for (i=0; i<10; i++) printf("%2ld ", regs[i]); printf("\n");
	}

end:
	free_ast_node(ast);
	map_ptoken_destroy(&paren_pairs);
	vec_token_destroy(&tokens);
	free(text.p);
	vec_diag_destroy(&diag_stack);
	return result;
}
