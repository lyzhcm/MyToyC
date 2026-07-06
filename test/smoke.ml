let expect_tokens source expected =
  let actual = source |> Mytoyc.Driver.lex_all |> List.map Mytoyc.Token.to_string in
  if actual <> expected then
    failwith
      (Printf.sprintf "token mismatch\nexpected: [%s]\nactual:   [%s]"
         (String.concat "; " expected)
         (String.concat "; " actual))

let expect_parse source =
  ignore (Mytoyc.Driver.parse source)

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

  expect_compile_exact "int main(){ return 42; }"
    ".text\n.globl main\nmain:\n  li a0, 42\n  ret\n";
  expect_compile_exact "int main(){ return 1 + 2 * 3; }"
    ".text\n.globl main\nmain:\n  li a0, 7\n  ret\n";
  expect_compile_contains "int main(){ return -(1 + 2); }"
    [ ".globl main"; "li a0, -3"; "ret" ];
  expect_compile_contains "int main(){ return 1 < 2 && 3 != 4; }"
    [ ".globl main"; "li a0, 1"; "ret" ]
