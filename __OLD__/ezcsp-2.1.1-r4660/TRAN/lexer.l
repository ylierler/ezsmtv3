%{
#include "lexglobal.h" 
#include "parser.h"
#include <string.h>
#include <math.h>

int line = 1, col = 1;

YYSTYPE yylval; 


%}

%%


-?[0-9]+|-?[0-9]*\.[0-9]+    {                      col += (int) strlen(yytext); 
                                                yylval.str = strdup(yytext); 
                                                return NUM; }
"\'"-?[0-9]+"\'"|"\'"-?[0-9]*\.[0-9]+"\'"    {                      col += (int) strlen(yytext)-2; 
                                                yylval.str = strdup(&yytext[1]);
						yylval.str[(int) strlen(yylval.str)-1]='\0';
                                                return NUM; }
[ \t]   { col += (int) strlen(yytext); }               /* ignore but count white space */
[A-Za-z][A-Za-z0-9_]*     {                      col += (int) strlen(yytext); 
                                                yylval.str = strdup(yytext); 
                                                return ID; }

"\""[^"]*"\""     {                      col += (int) strlen(yytext); 
                                                yylval.str = strdup(yytext); 
                                                return ID; }


"("           {  col += (int) strlen(yytext); yylval.str = strdup(yytext); return LPAREN; }
")"           {  col += (int) strlen(yytext); yylval.str = strdup(yytext); return RPAREN; }
","           {  col += (int) strlen(yytext); yylval.str = strdup(yytext); return COMMA; }
"."           {  col += (int) strlen(yytext); yylval.str = strdup(yytext); return PERIOD; }
"-"           {  col += (int) strlen(yytext); yylval.str = strdup(yytext); return MINUS; }

"%".*\n   { col += (int) strlen(yytext); }               /* ignore but count white space */

"#".*\n   { col += (int) strlen(yytext); }               /* directives: ignore but count white space */

\n      { col = 0; ++line; }

.       { col += (int) strlen(yytext); return yytext[0]; }
%%
/**
 * reset the line and column count
 *
 *
 */
void reset_lexer(void)
{

  line = 1;
  col  = 1;

}

/**
 * yyerror() is invoked when the lexer or the parser encounter
 * an error. The error message is passed via *s
 *
 *
 */
void yyerror(char *s)
{
  fprintf(stderr,"error: %s at line: %d col: %d\n",s,line,col);

}

int yywrap(void)
{
  return 1;
}
