#ifndef EZCSP_LEXGLOBAL_H
#define EZCSP_LEXGLOBAL_H

#ifndef YYSTYPE
typedef union {
  char *str;
} yystype;
# define YYSTYPE yystype
# define YYSTYPE_IS_TRIVIAL 1
#endif


extern YYSTYPE yylval;

#endif /* EZCSP_LEXGLOBAL_H */

