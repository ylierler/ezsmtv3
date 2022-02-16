#ifndef ASP_PARSER_H
#define ASP_PARSER_H

#include <stdio.h>

#define PARSER_VERSION "1.8.11"

#ifdef __cplusplus
extern "C" {
#endif

struct item
{
	char *relation;		/* atom's relation or term's function */
	int arity;		/* arity, i.e. number of arguments */
	int is_variable;
	int is_term;
#	  define IS_ATOM 0
#	  define IS_TERM 1
	int is_infix;
	int is_parenthesis;	/* the term is a parenthesizing term, e.g. '(' and '[' */
	  char arglist_end;	/* if is_parenthesis is true, this is the character that ends the term (field relation starts it) */
	int skip_parentheses;	/* do not put parentheses around the arguments of the item */
	int default_negation;
	int strong_negation;

	struct item **args;	/* arguments (length given by arity) */
};

struct rule
{	int type;
#	  define RULE_REGULAR 0
#	  define RULE_SOFT_CONSTRAINT 1
#	  define RULE_SYSTEM_DIRECTIVE 2
#	  define RULE_CR_RULE 3

	struct item *name;

	int head_size;
	struct item **head;

	int body_size;
	struct item **body;

	char *domain_decl;	/* STRING containing the domain declarations determined from the
				 * sorts. The atoms in the string are comma separated. NO PERIOD
				 * is at the end. Example: "p(X),q(Y),r(s(Z,W)),p(Z),q(W)"
				 * If there are no auto-generated domain declarations, the string
				 * is empty.
				 */

	char *system_directive;	/* use to store LITERALLY the system directive, if the rule is of that type */
};

struct node
{	struct rule *data;	/* node's rule. If NULL, this is the HEAD of the list */

	struct node *next;	/* next node or NULL */
};

/*
 * Syntax recognized
 * =================
 * ExtLit ::= not Lit | Lit
 * Lit ::= InfixAtom | ConstraintLiteral | BasicLit
 * BasicLit ::= -Atom | Atom
 * Atom ::= RelationSymbol | RelationSymbol(CommaList)
 * InfixAtom ::= E OP InfixAtom | E OP E
 * ConstraintLiteral ::= E { String } E | { String } E | E { String }
 * CommaList ::= ExprList | ExprList, CommaList
 * ExprList ::= BigE .. BigE | SemicolonList
 * SemicolonList ::= BigE | BigE; SemicolonList
 * SemicolonExprList ::=  BigE ; ExprList
 *
 *  BigE ::= E OP E | E
 *  E ::= T | T + E | T - E
 *  T ::= F | F * T | F / T | F mod T | F #mod T
 *  F ::= ( E ) | Term
 *
 * Term ::= Variable | Number | FunctionSymbol | FunctionSymbol(CommaList) | FunctionSymbol{String} | [ CommaList ]
 *
 */


/* Library functions */
extern void set_debug_parse(int truth); // false by default

extern char *parser_version(void);

extern struct node *parse_program(int n_files,char *files[]);

extern struct item *makeitem(int arity);
extern struct item *maketerm(int arity);

extern void add_domains_to_rule(struct rule *r);
extern void add_domains_to_program(struct node *program);

extern void debug_show_rule(struct rule *r);
extern void debug_show_program(struct node *program);

extern void output_atom_to_file(struct item *a,FILE *fp);
extern void output_atom(struct item *a);
extern void output_rule_to_file(struct rule *r,FILE *fp);
extern void output_program_to_file(struct node *program,FILE *fp);
extern void output_rule(struct rule *r);
extern void output_program(struct node *program);

#ifdef __cplusplus
}
#endif

#endif /* ASP_PARSER */

