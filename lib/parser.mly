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
%nonassoc IF_WITHOUT_ELSE
%nonassoc ELSE

%start <Ast.program> program

%%

program:
  | items = list(comp_item); EOF { items }

comp_item:
  | d = const_decl { GlobalDecl d }
  | INT; item = int_comp_item { item }
  | f = void_func { FuncDef f }

int_comp_item:
  | name = IDENT; SEMICOLON { GlobalDecl (VarDecl (name, None)) }
  | name = IDENT; ASSIGN; value = expr; SEMICOLON
    { GlobalDecl (VarDecl (name, Some value)) }
  | name = IDENT; LPAREN; params = separated_list(COMMA, param); RPAREN; LBRACE; body = list(stmt); RBRACE
    { FuncDef { return_type = TInt; name; params; body } }

void_func:
  | VOID; name = IDENT; LPAREN; params = separated_list(COMMA, param); RPAREN; LBRACE; body = list(stmt); RBRACE
    { { return_type = TVoid; name; params; body } }

const_decl:
  | CONST; INT; name = IDENT; ASSIGN; value = expr; SEMICOLON
    { ConstDecl (name, value) }

decl:
  | d = const_decl { d }
  | INT; name = IDENT; SEMICOLON { VarDecl (name, None) }
  | INT; name = IDENT; ASSIGN; value = expr; SEMICOLON { VarDecl (name, Some value) }

param:
  | INT; name = IDENT { { param_type = TInt; param_name = name } }

stmt:
  | LBRACE; body = list(stmt); RBRACE { Block body }
  | SEMICOLON { Empty }
  | d = decl { DeclStmt d }
  | name = IDENT; ASSIGN; value = expr; SEMICOLON { Assign (name, value) }
  | value = expr; SEMICOLON { ExprStmt value }
  | IF; LPAREN; cond = expr; RPAREN; then_branch = stmt %prec IF_WITHOUT_ELSE
    { If (cond, then_branch, None) }
  | IF; LPAREN; cond = expr; RPAREN; then_branch = stmt; ELSE; else_branch = stmt
    { If (cond, then_branch, Some else_branch) }
  | WHILE; LPAREN; cond = expr; RPAREN; body = stmt { While (cond, body) }
  | BREAK; SEMICOLON { Break }
  | CONTINUE; SEMICOLON { Continue }
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
