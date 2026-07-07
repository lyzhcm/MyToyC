let expect_tokens source expected =
  let actual = source |> Mytoyc.Driver.lex_all |> List.map Mytoyc.Token.to_string in
  if actual <> expected then
    failwith
      (Printf.sprintf "token mismatch\nexpected: [%s]\nactual:   [%s]"
         (String.concat "; " expected)
         (String.concat "; " actual))

let expect_parse source =
  ignore (Mytoyc.Driver.parse source)

let expect_parse_error source =
  try
    ignore (Mytoyc.Driver.parse source);
    failwith "expected parse error"
  with
  | Mytoyc.Parser.Error -> ()

let expect_check source =
  source |> Mytoyc.Driver.parse |> Mytoyc.Sema.check_program |> ignore

let contains_substring text fragment =
  let text_len = String.length text in
  let fragment_len = String.length fragment in
  let rec loop index =
    if fragment_len = 0 then true
    else if index + fragment_len > text_len then false
    else if String.sub text index fragment_len = fragment then true
    else loop (index + 1)
  in
  loop 0

let expect_lex_error source expected =
  try
    ignore (Mytoyc.Driver.lex_all source);
    failwith (Printf.sprintf "expected lex error containing %S" expected)
  with
  | Mytoyc.Diagnostic.Error message ->
      if not (contains_substring message expected) then
        failwith
          (Printf.sprintf "error mismatch\nexpected fragment: %S\nactual: %S"
             expected message)

let expect_compile_contains source expected =
  let output = Mytoyc.Driver.compile source in
  List.iter
    (fun fragment ->
      if not (contains_substring output fragment) then
        failwith
          (Printf.sprintf "compile output does not contain %S\noutput:\n%s" fragment
             output))
    expected

let expect_opt_compile_contains source expected =
  let output = Mytoyc.Driver.compile ~optimize:true source in
  List.iter
    (fun fragment ->
      if not (contains_substring output fragment) then
        failwith
          (Printf.sprintf
             "optimized compile output does not contain %S\noutput:\n%s" fragment
             output))
    expected

let expect_opt_compile_lacks source unexpected =
  let output = Mytoyc.Driver.compile ~optimize:true source in
  List.iter
    (fun fragment ->
      if contains_substring output fragment then
        failwith
          (Printf.sprintf
             "optimized compile output unexpectedly contains %S\noutput:\n%s"
             fragment output))
    unexpected

let expect_compile_exact source expected =
  let actual = Mytoyc.Driver.compile source in
  if actual <> expected then
    failwith
      (Printf.sprintf "compile mismatch\nexpected:\n%s\nactual:\n%s" expected actual)

let expect_compile_error source expected =
  try
    ignore (Mytoyc.Driver.compile source);
    failwith (Printf.sprintf "expected compile error containing %S" expected)
  with
  | Mytoyc.Diagnostic.Error message ->
      if not (contains_substring message expected) then
        failwith
          (Printf.sprintf "error mismatch\nexpected fragment: %S\nactual: %S"
             expected message)

let expect_check_error source expected =
  try
    expect_check source;
    failwith (Printf.sprintf "expected check error containing %S" expected)
  with
  | Mytoyc.Diagnostic.Error message ->
      if not (contains_substring message expected) then
        failwith
          (Printf.sprintf "error mismatch\nexpected fragment: %S\nactual: %S"
             expected message)

let expect_run_result source expected =
  let actual = source |> Mytoyc.Driver.compile |> Riscv_sim.run in
  if actual <> expected then
    failwith
      (Printf.sprintf "runtime result mismatch\nexpected: %d\nactual:   %d"
         expected actual)

let () =
  expect_tokens
    {|
const int answer = 42;
int main() {
  // line comment
  int x = 10 + 20;
  /* block
     comment */
  if (x >= answer && x != 0) return x % 3;
  else return -1;
}
|}
    [ "CONST"; "INT"; "IDENT(\"answer\")"; "ASSIGN"; "NUMBER(42)"; "SEMICOLON";
      "INT"; "IDENT(\"main\")"; "LPAREN"; "RPAREN"; "LBRACE";
      "INT"; "IDENT(\"x\")"; "ASSIGN"; "NUMBER(10)"; "PLUS"; "NUMBER(20)"; "SEMICOLON";
      "IF"; "LPAREN"; "IDENT(\"x\")"; "GE"; "IDENT(\"answer\")"; "AND_AND"; "IDENT(\"x\")"; "NE"; "NUMBER(0)"; "RPAREN";
      "RETURN"; "IDENT(\"x\")"; "PERCENT"; "NUMBER(3)"; "SEMICOLON";
      "ELSE"; "RETURN"; "MINUS"; "NUMBER(1)"; "SEMICOLON";
      "RBRACE"; "EOF" ];
  expect_lex_error "int main(){ return 0x2a; }"
    "hexadecimal integer literals are not allowed";
  expect_lex_error "int main(){ return 010; }"
    "decimal integer literals cannot have leading zeros";

  expect_parse "int main(){ return 42; }";
  expect_parse "int main(){ return 1 + 2 * 3; }";
  expect_parse "int main(){ return -(1 + 2); }";
  expect_parse "int main(){ return 1 < 2 && 3 != 4; }";
  expect_parse "int main(){ int a = 1; int b = 2; a = a + b; return a; }";
  expect_parse_error "";
  expect_parse_error "int x;";
  expect_parse_error "int main(){ int x; return 0; }";
  expect_parse "int g = 1; int main(){ return g; }";
  expect_parse "const int c = 1; int main(){ return c; }";
  expect_parse "void noop(){ return; } int main(){ return 0; }";
  expect_parse "int main(){ ; return 0; }";
  expect_parse "int main(){ 1 + 2; return 0; }";
  expect_parse "int main(){ if (1) if (0) return 1; else return 2; return 0; }";
  expect_parse "void f(){ return; } int main(){ f(); return 0; }";
  expect_parse "int id(int x){ return x; } int main(){ return id(1); }";
  expect_parse
    "int add(int a, int b){ return a + b; } int main(){ return add(1, 2); }";
  expect_parse
    "int main(){ return +1 - -2 * !3 / 4 % 5 + (6); }";
  expect_parse
    "int main(){ return 1 < 2 || 3 > 4 || 5 <= 6 || 7 >= 8 || 9 == 10 || 11 != 12; }";
  expect_parse
    "void noop(){} int g = 1; const int c = 2; int main(){ { int x = g + c; } return 0; }";
  expect_parse
    {|
const int answer = 42;
int add(int a, int b) {
  return a + b;
}
int main() {
  int x = add(1, 2);
  if (x > 0) {
    return x;
  } else {
    return 0;
  }
}
|};
  expect_parse
    "int main(){ int x = 0; while (x < 10) { x = x + 1; continue; } return x; }";
  expect_check
    "int add(int a, int b){ return a + b; } int main(){ return add(1, 2); }";
  expect_check
    "int f(){ if (1) return 1; } int main(){ return f(); }";
  expect_check
    "int main(){ int x = 0; while (x < 3) { x = x + 1; if (x == 2) break; } return x; }";
  expect_check_error "int f(){ if (0) return 1; } int main(){ return 0; }"
    "int function must return a value: f";
  expect_check_error "void main(){ return; }" "main must have type int main()";
  expect_check_error "int main(int x){ return x; }" "main must have type int main()";
  expect_check_error "void f(){ return; } int main(){ int x = f(); return x; }"
    "declaration initializer requires an int expression";
  expect_check_error "void f(){ return; } int main(){ if (f()) return 1; return 0; }"
    "if condition requires an int expression";
  expect_check
    "const int a = 1; const int b = a + 2; int main(){ return b; }";
  expect_check_error "int main(){ int x = 1; const int y = x; return y; }"
    "const initializer must be a compile-time constant";
  expect_check_error "const int a = 1; int main(){ a = 2; return a; }"
    "cannot assign to const: a";
  expect_check_error "int main(){ x = 1; int x = 2; return x; }"
    "undefined variable: x";
  expect_check_error "int main(){ return later(); } int later(){ return 1; }"
    "function used before declaration: later";
  expect_check
    "int self(int x){ if (x) return self(x - 1); return 0; } int main(){ return self(3); }";
  expect_check_error "int main(){ return g; } int g = 1;"
    "undefined variable: g";

  expect_compile_exact "int main(){ return 42; }"
    ".text\n.globl main\nmain:\n  addi sp, sp, -16\n  sw ra, 12(sp)\n  sw s0, 8(sp)\n  mv s0, sp\n  li a0, 42\n  lw ra, 12(s0)\n  lw s0, 8(s0)\n  addi sp, sp, 16\n  ret\n";
  expect_compile_contains "int main(){ return 1 + 2 * 3; }"
    [ ".globl main"; "mul"; "add"; "ret" ];
  expect_compile_contains "int main(){ return -(1 + 2); }"
    [ ".globl main"; "add"; "neg"; "ret" ];
  expect_compile_contains "int main(){ return 1 < 2 && 3 != 4; }"
    [ ".globl main"; "slt"; "snez"; "beqz"; "ret" ];
  expect_compile_contains
    "int main(){ int a = 1; int b = 2; a = a + b; return a; }"
    [ ".globl main"; "li t0, 1"; "li t0, 2"; "add"; "ret" ];
  expect_compile_contains
    "int main(){ if (1) return 1; else return 0; }"
    [ ".L_main_if_else_"; ".L_main_if_end_"; "beqz"; "j .L_main_if_end_" ];
  expect_compile_contains
    "int main(){ int x = 0; while (x < 3) { x = x + 1; if (x == 2) continue; if (x > 2) break; } return x; }"
    [ ".L_main_while_cond_"; ".L_main_while_end_"; "beqz";
      "j .L_main_while_cond_" ];
  expect_compile_contains "int main(){ return 1 && 0 || 2; }"
    [ ".L_main_land_false_"; ".L_main_lor_rhs_"; "beqz";
      "j .L_main_lor_end_" ];
  expect_compile_contains
    "int id(int x){ return x; } int main(){ return id(1); }"
    [ ".globl id"; "call id"; "ret" ];
  expect_compile_contains
    "void noop(){ return; } int main(){ noop(); return 0; }"
    [ ".globl noop"; "call noop"; "ret" ];
  expect_compile_contains
    "int g = 1; int main(){ return g; }"
    [ ".data"; ".globl g"; "g:"; ".word 1"; "la t0, g"; "ret" ];
  expect_compile_contains
    "int g = 1; int inc(int x){ return x + 1; } int main(){ g = inc(g); return g; }"
    [ ".data"; "call inc"; "la t1, g"; "ret" ];
  expect_compile_contains
    "const int a = 2; int g = a + 3; int main(){ return g; }"
    [ ".data"; ".word 5" ];
  expect_compile_contains
    "int init(){ return 7; } int g = init(); int main(){ return g; }"
    [ "__mytoyc_init_done"; ".L_main_global_init_"; "call init" ];
  expect_compile_contains
    "int pick9(int a,int b,int c,int d,int e,int f,int g,int h,int i){ return i; } int main(){ return pick9(1,2,3,4,5,6,7,8,9); }"
    [ "call pick9"; "sw t0, 0(sp)" ];
  expect_opt_compile_contains "int main(){ return 1 + 2 * 3; }"
    [ "li a0, 7"; "ret" ];
  expect_opt_compile_lacks "int main(){ return 1 + 2 * 3; }"
    [ "  mul "; "  add " ];
  expect_opt_compile_contains "int main(){ if (0) return 1; return 2; }"
    [ "li a0, 2"; "ret" ];
  expect_opt_compile_lacks "int main(){ if (0) return 1; return 2; }"
    [ "beqz" ];
  expect_opt_compile_contains "int main(){ 1 + 2; return 0; }"
    [ "li a0, 0"; "ret" ];
  expect_opt_compile_lacks "int main(){ 1 + 2; return 0; }"
    [ "li t0, 3"; "sw t0, 0(s0)" ];
  expect_opt_compile_contains
    "int main(){ int a = 1; int b = a + 2; return a; }"
    [ "li a0, 1"; "ret" ];
  expect_opt_compile_lacks
    "int main(){ int a = 1; int b = a + 2; return a; }"
    [ "li t0, 3"; "sw t0, 4(s0)" ];
  expect_compile_error "int main(){ return a; }" "undefined variable: a";
  expect_compile_error "int main(){ int a = 0; int a = 1; return a; }"
    "duplicate variable: a";
  expect_check_error "int main(){ break; return 0; }" "break outside loop";
  expect_check_error "int main(){ return missing(); }"
    "function used before declaration: missing";
  expect_check_error "int add(int a){ return a; } int main(){ return add(1, 2); }"
    "expects 1 argument";

  expect_run_result "int main(){ return 42; }" 42;
  expect_run_result
    "int main(){ int x = 0; while (x < 5) { x = x + 1; if (x == 3) continue; if (x > 4) break; } return x; }"
    5;
  expect_run_result
    "int g = 0; int set(){ g = 1; return 1; } int main(){ if (0 && set()) return 9; return g; }"
    0;
  expect_run_result
    "int g = 0; int set(){ g = 1; return 1; } int main(){ if (1 || set()) return g; return 9; }"
    0;
  expect_run_result
    "int n = 0; int init(){ n = n + 1; return 7; } int g = init(); int main(){ return n + g; }"
    8;
  expect_run_result
    "int pick9(int a,int b,int c,int d,int e,int f,int g,int h,int i){ return i; } int main(){ return pick9(1,2,3,4,5,6,7,8,9); }"
    9;
  expect_run_result
    "int fact(int x){ if (x <= 1) return 1; return x * fact(x - 1); } int main(){ return fact(5); }"
    120;
  expect_run_result "void noop(){ } int main(){ noop(); return 7; }" 7;
  expect_run_result
    "void maybe(int x){ if (x) return; } int main(){ maybe(0); maybe(1); return 8; }"
    8;
  expect_run_result
    "int g = 1; void set(){ g = g + 4; } int main(){ set(); return g; }"
    5;
  expect_run_result
    "int main(){ int a = 2; int b = 3; int c = 4; return +a * -(b + c) + !0 + (a <= b) * 10; }"
    (-3);
  expect_run_result
    "const int c = 3; int g = 4; void bump(){ g = g + c; } int choose(int x){ if (x > 0) { int y = x + g; { int z = y * 2; y = z - c; } return y; } else { while (x < 0) { x = x + 1; if (x == 0) break; } return x; } } int main(){ bump(); return choose(1); }"
    13;
  expect_run_result
    "int id(int x){ return x; } int main(){ return !(1 + 2 * 3 - 7) + ((id(5) > 3 && 0) || (4 / 2 == 2)); }"
    2;
  expect_run_result
    "int main(){ int x = 4; { int x = x + 3; return x; } return 0; }"
    7;
  expect_run_result
    "int main(){ return 1 != 2 < 3; }"
    0;
  expect_compile_contains
    "int main(){ return -2147483648; }"
    [ "-2147483648"; "ret" ]
