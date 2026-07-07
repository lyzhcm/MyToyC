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

%nonassoc IF_WITHOUT_ELSE
%nonassoc ELSE

%start <Ast.program> program

%%

program:
  | items = nonempty_list(comp_item); EOF { items }

comp_item:
  | d = const_decl { GlobalDecl d }
  | INT; item = int_comp_item { item }
  | f = void_func { FuncDef f }

int_comp_item:
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
  | e = lor_expr { e }

lor_expr:
  | e = land_expr { e }
  | lhs = lor_expr; OR_OR; rhs = land_expr { Binary (LOr, lhs, rhs) }

land_expr:
  | e = rel_expr { e }
  | lhs = land_expr; AND_AND; rhs = rel_expr { Binary (LAnd, lhs, rhs) }

rel_expr:
  | e = add_expr { e }
  | lhs = rel_expr; LT; rhs = add_expr { Binary (Lt, lhs, rhs) }
  | lhs = rel_expr; GT; rhs = add_expr { Binary (Gt, lhs, rhs) }
  | lhs = rel_expr; LE; rhs = add_expr { Binary (Le, lhs, rhs) }
  | lhs = rel_expr; GE; rhs = add_expr { Binary (Ge, lhs, rhs) }
  | lhs = rel_expr; EQ; rhs = add_expr { Binary (Eq, lhs, rhs) }
  | lhs = rel_expr; NE; rhs = add_expr { Binary (Ne, lhs, rhs) }

add_expr:
  | e = mul_expr { e }
  | lhs = add_expr; PLUS; rhs = mul_expr { Binary (Add, lhs, rhs) }
  | lhs = add_expr; MINUS; rhs = mul_expr { Binary (Sub, lhs, rhs) }

mul_expr:
  | e = unary_expr { e }
  | lhs = mul_expr; STAR; rhs = unary_expr { Binary (Mul, lhs, rhs) }
  | lhs = mul_expr; SLASH; rhs = unary_expr { Binary (Div, lhs, rhs) }
  | lhs = mul_expr; PERCENT; rhs = unary_expr { Binary (Mod, lhs, rhs) }

unary_expr:
  | e = primary_expr { e }
  | PLUS; e = unary_expr { Unary (Pos, e) }
  | MINUS; e = unary_expr { Unary (Neg, e) }
  | BANG; e = unary_expr { Unary (LNot, e) }

primary_expr:
  | n = NUMBER { Int n }
  | name = IDENT { Var name }
  | name = IDENT; LPAREN; args = separated_list(COMMA, expr); RPAREN { Call (name, args) }
  | LPAREN; e = expr; RPAREN { e }
