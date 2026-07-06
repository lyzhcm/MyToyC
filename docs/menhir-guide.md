# Menhir 实践手册：面向 ToyC 编译器

这份手册不是完整翻译 Menhir 官方文档，而是面向本项目的实用版。目标是让你能看懂并维护 `lib/parser.mly`，逐步实现 ToyC 的语法分析。

## 1. Menhir 做什么

Menhir 是 OCaml 生态里的 parser generator。你写一份 `.mly` 语法文件，Menhir 根据它生成 OCaml 解析器。

完整流程是：

```text
ToyC 源码字符串
  ↓ ocamllex: lib/lexer.mll
Token 流
  ↓ Menhir: lib/parser.mly
AST
```

比如源码：

```c
int main() {
  return 1 + 2 * 3;
}
```

会先被 lexer 切成 token：

```text
INT IDENT("main") LPAREN RPAREN LBRACE RETURN NUMBER(1) PLUS NUMBER(2) STAR NUMBER(3) SEMICOLON RBRACE EOF
```

然后 parser 根据语法规则构造 AST。

## 2. 一个 `.mly` 文件的结构

Menhir 文件通常分三段：

```ocaml
%{
(* OCaml 代码区，通常 open Ast *)
%}

(* token、优先级、入口声明 *)

%%

(* 语法规则区 *)
```

例如：

```ocaml
%{
open Ast
%}

%token INT RETURN
%token <string> IDENT
%token <int> NUMBER
%token LPAREN RPAREN LBRACE RBRACE SEMICOLON
%token PLUS STAR EOF

%left PLUS
%left STAR

%start <Ast.program> program

%%

program:
  | funcs = list(func); EOF { funcs }
```

## 3. `%token`：声明终结符

lexer 返回什么 token，parser 里就必须声明什么 token。

无数据 token：

```ocaml
%token INT RETURN IF ELSE WHILE
%token LPAREN RPAREN LBRACE RBRACE SEMICOLON
%token PLUS MINUS STAR SLASH
```

带数据 token：

```ocaml
%token <string> IDENT
%token <int> NUMBER
```

对应 lexer 写法：

```ocaml
| digit+ as n { NUMBER (int_of_string n) }
| ident as name { IDENT name }
```

注意：Menhir token 名通常用全大写，比如 `RETURN`、`NUMBER`。

## 4. `%start`：声明入口规则

入口规则就是 parser 从哪里开始解析。

```ocaml
%start <Ast.program> program
```

意思是：

```ocaml
Parser.program : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> Ast.program
```

所以 `driver.ml` 可以这样调用：

```ocaml
let parse source =
  let lexbuf = Lexing.from_string source in
  Parser.program Lexer.token lexbuf
```

## 5. 语法规则基本写法

Menhir 规则长这样：

```ocaml
nonterminal:
  | pattern { ocaml_action }
  | pattern { ocaml_action }
```

例子：

```ocaml
stmt:
  | RETURN; value = expr; SEMICOLON { Return (Some value) }
  | RETURN; SEMICOLON { Return None }
```

左边是语法，右边 `{ ... }` 是构造 AST 的 OCaml 代码。

## 6. 给子规则命名

你可以给某个符号绑定名字：

```ocaml
func:
  | INT; name = IDENT; LPAREN; RPAREN; body = block
    { { return_type = TInt; name; body } }
```

这里：

```ocaml
name = IDENT
```

如果 lexer 返回：

```ocaml
IDENT "main"
```

那么 action 里的 `name` 就是字符串 `"main"`。

## 7. `option`：可选语法

ToyC 里有：

```text
return Expr? ;
```

可以写成：

```ocaml
stmt:
  | RETURN; value = option(expr); SEMICOLON { Return value }
```

`option(expr)` 的结果类型是：

```ocaml
Ast.expr option
```

也就是：

```ocaml
Some expr
None
```

等价手写版本：

```ocaml
stmt:
  | RETURN; value = expr; SEMICOLON { Return (Some value) }
  | RETURN; SEMICOLON { Return None }
```

## 8. `list`：重复零次或多次

ToyC 的编译单元：

```text
CompUnit -> (Decl | FuncDef)+
```

如果先只支持函数，可以写：

```ocaml
program:
  | funcs = nonempty_list(func); EOF { funcs }
```

`list(x)` 表示零个或多个。

```ocaml
block:
  | LBRACE; stmts = list(stmt); RBRACE { Block stmts }
```

`nonempty_list(x)` 表示一个或多个。

```ocaml
program:
  | items = nonempty_list(comp_item); EOF { items }
```

## 9. `separated_list`：逗号分隔列表

函数调用：

```text
ID "(" (Expr ("," Expr)*)? ")"
```

可以写成：

```ocaml
primary_expr:
  | name = IDENT; LPAREN; args = separated_list(COMMA, expr); RPAREN
    { Call (name, args) }
```

这会同时支持：

```c
foo()
foo(1)
foo(1, 2, 3)
```

函数形参也类似：

```ocaml
param:
  | INT; name = IDENT { { param_type = TInt; param_name = name } }

func:
  | INT; name = IDENT; LPAREN; params = separated_list(COMMA, param); RPAREN; body = block
    { { return_type = TInt; name; params; body } }
```

## 10. 表达式优先级

ToyC 表达式有多层优先级：

```text
||
&&
== !=
< > <= >=
+ -
* / %
一元 + - !
primary
```

Menhir 有两种常见写法。

### 写法 A：用 `%left` / `%right` 声明优先级

```ocaml
%left OR_OR
%left AND_AND
%left EQ NE
%left LT GT LE GE
%left PLUS MINUS
%left STAR SLASH PERCENT
%right UPLUS UMINUS BANG
```

越靠后的优先级越高。所以这里 `STAR` 比 `PLUS` 高。

表达式规则可以写得比较短：

```ocaml
expr:
  | n = NUMBER { Int n }
  | name = IDENT { Var name }
  | LPAREN; e = expr; RPAREN { e }
  | PLUS; e = expr %prec UPLUS { Unary (Pos, e) }
  | MINUS; e = expr %prec UMINUS { Unary (Neg, e) }
  | BANG; e = expr { Unary (LNot, e) }
  | lhs = expr; PLUS; rhs = expr { Binary (Add, lhs, rhs) }
  | lhs = expr; STAR; rhs = expr { Binary (Mul, lhs, rhs) }
```

`%prec UMINUS` 的意思是：这一条规则虽然看到的是 `MINUS expr`，但使用虚拟优先级 `UMINUS`，让一元负号比二元减号优先级高。

### 写法 B：按文法层级拆开

这种更贴近 ToyC 语言定义，也更容易避免冲突：

```ocaml
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
  | lhs = rel_expr; EQ; rhs = add_expr { Binary (Eq, lhs, rhs) }

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
  | name = IDENT { Var name }
  | n = NUMBER { Int n }
  | LPAREN; e = expr; RPAREN { e }
```

对课程项目，我更推荐写法 B，因为它和文法定义一一对应，后面 debug 更直观。

## 11. 处理 `if ... else` 的悬挂 else

经典问题：

```c
if (a)
  if (b) return 1;
  else return 2;
```

`else` 应该匹配最近的 `if`。

一种实用写法是声明优先级：

```ocaml
%nonassoc IF_WITHOUT_ELSE
%nonassoc ELSE
```

规则：

```ocaml
stmt:
  | IF; LPAREN; cond = expr; RPAREN; then_branch = stmt %prec IF_WITHOUT_ELSE
    { If (cond, then_branch, None) }
  | IF; LPAREN; cond = expr; RPAREN; then_branch = stmt; ELSE; else_branch = stmt
    { If (cond, then_branch, Some else_branch) }
```

因为 `ELSE` 优先级更高，Menhir 会把 `else` 交给最近的 `if`。

## 12. ToyC 的推荐 parser 骨架

后续可以把 `parser.mly` 改成这种结构：

```ocaml
program:
  | items = nonempty_list(comp_item); EOF { items }

comp_item:
  | d = decl { GlobalDecl d }
  | f = func_def { FuncDef f }

decl:
  | d = const_decl { d }
  | d = var_decl { d }

const_decl:
  | CONST; INT; name = IDENT; ASSIGN; value = expr; SEMICOLON
    { ConstDecl (name, value) }

var_decl:
  | INT; name = IDENT; ASSIGN; value = expr; SEMICOLON
    { VarDecl (name, Some value) }

func_def:
  | ret = func_type; name = IDENT; LPAREN; params = separated_list(COMMA, param); RPAREN; body = block
    { { return_type = ret; name; params; body } }

func_type:
  | INT { TInt }
  | VOID { TVoid }

param:
  | INT; name = IDENT { { param_type = TInt; param_name = name } }

block:
  | LBRACE; stmts = list(stmt); RBRACE { Block stmts }
```

对应 AST 需要有：

```ocaml
type program_item =
  | GlobalDecl of decl
  | FuncDef of func

and decl =
  | ConstDecl of string * expr
  | VarDecl of string * expr option

and stmt =
  | Block of stmt list
  | Empty
  | ExprStmt of expr
  | Assign of string * expr
  | DeclStmt of decl
  | If of expr * stmt * stmt option
  | While of expr * stmt
  | Break
  | Continue
  | Return of expr option
```

## 13. 赋值语句和表达式语句的冲突

ToyC 语句里有：

```text
Expr ";"
ID "=" Expr ";"
```

如果 `expr` 也能以 `IDENT` 开头，parser 看到 `IDENT` 时可能不知道这是表达式语句还是赋值语句。

对于这个 ToyC 文法，可以直接写：

```ocaml
stmt:
  | SEMICOLON { Empty }
  | e = expr; SEMICOLON { ExprStmt e }
  | name = IDENT; ASSIGN; value = expr; SEMICOLON { Assign (name, value) }
```

Menhir 通常能通过向后看一个 token 区分：

```text
IDENT ASSIGN ...    -> Assign
IDENT PLUS ...      -> ExprStmt
IDENT SEMICOLON     -> ExprStmt
IDENT LPAREN ...    -> 函数调用表达式语句
```

如果出现冲突，可以把赋值也设计成表达式的一种：

```ocaml
type expr =
  | AssignExpr of string * expr
  | ...
```

但对于这门 ToyC，先按语句处理更清楚。

## 14. 与 Dune 集成

`lib/dune` 里需要有：

```lisp
(library
 (name mytoyc)
 (modules ast parser lexer driver ...))

(ocamllex lexer)

(menhir
 (modules parser))
```

构建时 Dune 会自动：

```text
lexer.mll -> lexer.ml
parser.mly -> parser.ml/parser.mli
```

然后其他模块就可以引用：

```ocaml
Parser.program Lexer.token lexbuf
```

## 15. 常见错误

### token 名不一致

lexer 返回：

```ocaml
NUMBER 123
```

parser 必须声明：

```ocaml
%token <int> NUMBER
```

如果 parser 里叫 `INT_LIT`，就会编译失败。

### AST 构造函数不存在

parser 写：

```ocaml
{ Binary (Mod, lhs, rhs) }
```

那 `ast.ml` 里必须有：

```ocaml
type binop = ... | Mod
```

### action 类型不一致

如果 `stmt` 的类型是 `Ast.stmt`，每个分支都必须返回 `Ast.stmt`。

错误例子：

```ocaml
stmt:
  | RETURN; e = expr; SEMICOLON { e }
```

这里返回的是 `expr`，不是 `stmt`。

正确写法：

```ocaml
stmt:
  | RETURN; e = expr; SEMICOLON { Return (Some e) }
```

### 忘记 EOF

入口规则最好消费 `EOF`：

```ocaml
program:
  | items = list(comp_item); EOF { items }
```

否则输入末尾多余内容可能没有被正确发现。

## 16. 一个完整小例子

AST：

```ocaml
type expr =
  | Int of int
  | Binary of string * expr * expr

type stmt =
  | Return of expr

type program = stmt list
```

Parser：

```ocaml
%token RETURN SEMICOLON PLUS STAR EOF
%token <int> NUMBER
%left PLUS
%left STAR
%start <Ast.program> program

%%

program:
  | stmts = list(stmt); EOF { stmts }

stmt:
  | RETURN; e = expr; SEMICOLON { Return e }

expr:
  | n = NUMBER { Int n }
  | lhs = expr; PLUS; rhs = expr { Binary ("+", lhs, rhs) }
  | lhs = expr; STAR; rhs = expr { Binary ("*", lhs, rhs) }
```

输入：

```c
return 1 + 2 * 3;
```

输出 AST 等价于：

```ocaml
[
  Return
    (Binary
       ("+",
        Int 1,
        Binary ("*", Int 2, Int 3)))
]
```

## 17. 本项目下一步建议

当前项目已经有：

```text
lib/lexer.mll
lib/parser.mly
lib/ast.ml
```

下一步建议按这个顺序改：

1. 先补全 `ast.ml`，让它能表示完整 ToyC。
2. 再把 `parser.mly` 按 ToyC 文法分层实现。
3. 用小输入测试 parser：

```c
int main() {
  return 1 + 2 * 3;
}
```

4. 再测复杂一点：

```c
int add(int a, int b) {
  return a + b;
}

int main() {
  int x = add(1, 2);
  if (x > 0) return x;
  return 0;
}
```

Menhir 的核心心法是：语法规则负责“识别结构”，action 负责“构造 AST”。只要 AST 设计清楚，parser 会越来越像把语言定义翻译成 OCaml。
