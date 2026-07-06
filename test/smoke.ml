let expect_tokens source expected =
  let actual = source |> Mytoyc.Driver.lex_all |> List.map Mytoyc.Token.to_string in
  if actual <> expected then
    failwith
      (Printf.sprintf "token mismatch\nexpected: [%s]\nactual:   [%s]"
         (String.concat "; " expected)
         (String.concat "; " actual))

let expect_parse source =
  ignore (Mytoyc.Driver.parse source)

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

let expect_compile_contains source expected =
  let output = Mytoyc.Driver.compile source in
  List.iter
    (fun fragment ->
      if not (contains_substring output fragment) then
        failwith
          (Printf.sprintf "compile output does not contain %S\noutput:\n%s" fragment
             output))
    expected

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

let () =
  expect_tokens
    {|
const int answer = 0x2a;
int main() {
  // line comment
  int x = 010 + 20;
  /* block
     comment */
  if (x >= answer && x != 0) return x % 3;
  else return -1;
}
|}
    [ "CONST"; "INT"; "IDENT(\"answer\")"; "ASSIGN"; "NUMBER(42)"; "SEMICOLON";
      "INT"; "IDENT(\"main\")"; "LPAREN"; "RPAREN"; "LBRACE";
      "INT"; "IDENT(\"x\")"; "ASSIGN"; "NUMBER(8)"; "PLUS"; "NUMBER(20)"; "SEMICOLON";
      "IF"; "LPAREN"; "IDENT(\"x\")"; "GE"; "IDENT(\"answer\")"; "AND_AND"; "IDENT(\"x\")"; "NE"; "NUMBER(0)"; "RPAREN";
      "RETURN"; "IDENT(\"x\")"; "PERCENT"; "NUMBER(3)"; "SEMICOLON";
      "ELSE"; "RETURN"; "MINUS"; "NUMBER(1)"; "SEMICOLON";
      "RBRACE"; "EOF" ];

  expect_parse "int main(){ return 42; }";
  expect_parse "int main(){ return 1 + 2 * 3; }";
  expect_parse "int main(){ return -(1 + 2); }";
  expect_parse "int main(){ return 1 < 2 && 3 != 4; }";
  expect_parse "int main(){ int a = 1; int b = 2; a = a + b; return a; }";
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
    "int main(){ int x = 0; while (x < 3) { x = x + 1; if (x == 2) break; } return x; }";

  expect_compile_exact "int main(){ return 42; }"
    ".text\n.globl main\nmain:\n  li a0, 42\n  ret\n";
  expect_compile_contains "int main(){ return 1 + 2 * 3; }"
    [ ".globl main"; "mul"; "add"; "mv a0"; "ret" ];
  expect_compile_contains "int main(){ return -(1 + 2); }"
    [ ".globl main"; "add"; "neg"; "mv a0"; "ret" ];
  expect_compile_contains "int main(){ return 1 < 2 && 3 != 4; }"
    [ ".globl main"; "slt"; "snez"; "and"; "mv a0"; "ret" ];
  expect_compile_contains
    "int main(){ int a = 1; int b = 2; a = a + b; return a; }"
    [ ".globl main"; "li t0, 1"; "li t1, 2"; "add"; "mv t0"; "mv a0, t0";
      "ret" ];
  expect_compile_error "int main(){ return a; }" "undefined variable: a";
  expect_compile_error "int main(){ int a; int a; return a; }"
    "duplicate variable: a";
  expect_check_error "int main(){ break; return 0; }" "break outside loop";
  expect_check_error "int main(){ return missing(); }" "undefined function: missing";
  expect_check_error "int add(int a){ return a; } int main(){ return add(1, 2); }"
    "expects 1 argument"
