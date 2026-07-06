%{
open Ast
%}

%token CONST INT VOID IF ELSE WHILE BREAK CONTINUE RETURN
%token <string> IDENT
%token <int> NUMBER
%token LPAREN RPAREN LBRACE RBRACE SEMICOLON COMMA
%token ASSIGN
%token PLUS MINUS STAR SLASH PERCENT BANG
%token LT GT LE GE EQ NE
%token AND_AND OR_OR
%token EOF

%left OR_OR
%left AND_AND
%left EQ NE
%left LT GT LE GE
%left PLUS MINUS
%left STAR SLASH PERCENT
%right UPLUS UMINUS BANG

%start <Ast.program> program

%%

program:
  | funcs = list(func); EOF { funcs }

func:
  | INT; name = IDENT; LPAREN; RPAREN; LBRACE; body = list(stmt); RBRACE
    { { return_type = TInt; name; body } }
  | VOID; name = IDENT; LPAREN; RPAREN; LBRACE; body = list(stmt); RBRACE
    { { return_type = TVoid; name; body } }

stmt:
  | RETURN; value = option(expr); SEMICOLON { Return value }

expr:
  | n = NUMBER { Int n }
  | name = IDENT { Var name }
  | name = IDENT; LPAREN; args = separated_list(COMMA, expr); RPAREN { Call (name, args) }
  | LPAREN; e = expr; RPAREN { e }
  | PLUS; e = expr %prec UPLUS { Unary (Pos, e) }
  | MINUS; e = expr %prec UMINUS { Unary (Neg, e) }
  | BANG; e = expr { Unary (LNot, e) }
  | lhs = expr; PLUS; rhs = expr { Binary (Add, lhs, rhs) }
  | lhs = expr; MINUS; rhs = expr { Binary (Sub, lhs, rhs) }
  | lhs = expr; STAR; rhs = expr { Binary (Mul, lhs, rhs) }
  | lhs = expr; SLASH; rhs = expr { Binary (Div, lhs, rhs) }
  | lhs = expr; PERCENT; rhs = expr { Binary (Mod, lhs, rhs) }
  | lhs = expr; LT; rhs = expr { Binary (Lt, lhs, rhs) }
  | lhs = expr; GT; rhs = expr { Binary (Gt, lhs, rhs) }
  | lhs = expr; LE; rhs = expr { Binary (Le, lhs, rhs) }
  | lhs = expr; GE; rhs = expr { Binary (Ge, lhs, rhs) }
  | lhs = expr; EQ; rhs = expr { Binary (Eq, lhs, rhs) }
  | lhs = expr; NE; rhs = expr { Binary (Ne, lhs, rhs) }
  | lhs = expr; AND_AND; rhs = expr { Binary (LAnd, lhs, rhs) }
  | lhs = expr; OR_OR; rhs = expr { Binary (LOr, lhs, rhs) }
