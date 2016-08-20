#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
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
	FILE* f = fopen(filename, "rb");
	if (!f) {
		result.p = NULL;
		result.n = 0;
		return result;
	}

	fseek(f, 0, SEEK_END);
	result.n = ftell(f);
	fseek(f, 0, SEEK_SET);
	
	result.p = malloc(result.n+1);
	fread(result.p, 1, result.n, f);
	return result;
}

enum TToken
{
	TOK_LPAREN,    /*  (            */
	TOK_RPAREN,    /*  )            */
	TOK_LBRACKET,  /*  [            */
	TOK_RBRACKET,  /*  ]            */
	TOK_LBRACE,    /*  {            */
	TOK_RBRACE,    /*  }            */
	TOK_COLON,     /*  :            */
	TOK_COLON2,    /*  ::           */
	TOK_EQ,        /*  =            */
	TOK_EQ2,       /*  ==           */
	TOK_LESS,      /*  <            */
	TOK_LEQ,       /*  <=           */
	TOK_MORE,      /*  >            */
	TOK_MEQ,       /*  >=           */
	TOK_PLUS,      /*  +            */
	TOK_MINUS,     /*  -            */
	TOK_MINUS2,    /*  --           */
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

char* TTokenNames[] = {"LPAREN","RPAREN","LBRACKET","RBRACKET","LBRACE","RBRACE","COLON","COLON2","EQ","EQ2","LESS","LEQ","MORE","MEQ","PLUS","MINUS","MINUS2","MINUS3","ARROW","STAR","SLASH","DOT","DOT2","COMMA","SEMI","AND","AND2","PIPE2","DIRECTIVE","INT","FLOAT","STRING","ID","EOF"};

GS_ASSERT(sizeof(TTokenNames) == TOK__N*sizeof(char*));

struct token {
	enum TToken type;
	struct str_view text;
};

#define VEC_TYPE struct token
#define VEC_TYPE_NAME token
#include "vec.c"

struct token token_of(enum TToken type, struct str_view text)
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
				if (p[1] == '>') ADD(ARROW, 2);
				else if (p[1] == '-')
					if (p[2] == '-') ADD(MINUS3, 3);
					else             ADD(MINUS2, 2);
				else             ADD(MINUS, 1);
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

int main(int argc, char** argv)
{
	size_t i;
	struct str text;
	struct vec_token tokens = vec_token_make(20);

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

	for (i=0; i<tokens.n; i++)
		printf("%-20s %.*s\n", TTokenNames[tokens.v[i].type], (int) tokens.v[i].text.n, tokens.v[i].text.p);
	
	vec_token_destroy(&tokens);
	return 0;
}
