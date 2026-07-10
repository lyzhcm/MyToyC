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

let count_substring text fragment =
  let text_len = String.length text in
  let fragment_len = String.length fragment in
  let rec loop index count =
    if fragment_len = 0 || index + fragment_len > text_len then count
    else if String.sub text index fragment_len = fragment then
      loop (index + fragment_len) (count + 1)
    else loop (index + 1) count
  in
  loop 0 0

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

let expect_compile_lacks source unexpected =
  let output = Mytoyc.Driver.compile source in
  List.iter
    (fun fragment ->
      if contains_substring output fragment then
        failwith
          (Printf.sprintf "compile output unexpectedly contains %S\noutput:\n%s"
             fragment output))
    unexpected

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

let expect_opt_compile_count source fragment expected =
  let output = Mytoyc.Driver.compile ~optimize:true source in
  let actual = count_substring output fragment in
  if actual <> expected then
    failwith
      (Printf.sprintf
         "optimized compile count mismatch for %S\nexpected: %d\nactual:   %d\noutput:\n%s"
         fragment expected actual output)

let expect_compile_exact source expected =
  let actual = Mytoyc.Driver.compile source in
  if actual <> expected then
    failwith
      (Printf.sprintf "compile mismatch\nexpected:\n%s\nactual:\n%s" expected actual)

let expect_optimized_body body expected =
  let actual = Mytoyc.Optimize.optimize_body body in
  if actual <> expected then failwith "optimized IR body mismatch"

let starts_with prefix text =
  let prefix_len = String.length prefix in
  String.length text >= prefix_len && String.sub text 0 prefix_len = prefix

let split_once text ch =
  match String.index_opt text ch with
  | None -> (text, "")
  | Some index ->
      ( String.sub text 0 index,
        String.sub text (index + 1) (String.length text - index - 1) )

let parse_operands text =
  text |> String.split_on_char ',' |> List.map String.trim
  |> List.filter (fun part -> part <> "")

let memory_offset operand =
  let offset, _ = split_once operand '(' in
  int_of_string (String.trim offset)

let expect_real_riscv_immediates source =
  let assembly = Mytoyc.Driver.compile source in
  assembly |> String.split_on_char '\n'
  |> List.iter (fun raw_line ->
         let line = String.trim raw_line in
         let fail imm =
           if imm < -2048 || imm > 2047 then
             failwith
               (Printf.sprintf "RISC-V 12-bit immediate out of range: %d in %s"
                  imm line)
         in
         if starts_with "addi " line then
           match split_once line ' ' |> snd |> parse_operands with
           | [ _; _; imm ] -> fail (int_of_string imm)
           | _ -> ()
         else if starts_with "lw " line || starts_with "sw " line then
           match split_once line ' ' |> snd |> parse_operands with
           | [ _; mem ] -> fail (memory_offset mem)
           | _ -> ())

let many_locals_source count =
  let decls =
    List.init count (fun index -> Printf.sprintf "int v%d = %d;" index (index mod 7))
    |> String.concat " "
  in
  let sum =
    List.init count (fun index -> Printf.sprintf "v%d" index)
    |> String.concat " + "
  in
  Printf.sprintf "int main(){ %s return %s; }" decls sum

let many_args_source count =
  let params =
    List.init count (fun index -> Printf.sprintf "int p%d" index)
    |> String.concat ","
  in
  let args =
    List.init count string_of_int |> String.concat ","
  in
  Printf.sprintf "int pick(%s){ return p%d; } int main(){ return pick(%s); }"
    params (count - 1) args

let many_args_sum_source count =
  let params =
    List.init count (fun index -> Printf.sprintf "int p%d" index)
    |> String.concat ","
  in
  let sum =
    List.init count (fun index -> Printf.sprintf "p%d" index)
    |> String.concat " + "
  in
  let args =
    List.init count string_of_int |> String.concat ","
  in
  Printf.sprintf "int sum(%s){ return %s; } int main(){ return sum(%s); }"
    params sum args

let arithmetic_series_sum count =
  (count * (count - 1)) / 2

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

let expect_opt_run_result source expected =
  let actual = source |> Mytoyc.Driver.compile ~optimize:true |> Riscv_sim.run in
  if actual <> expected then
    failwith
      (Printf.sprintf
         "optimized runtime result mismatch\nexpected: %d\nactual:   %d"
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
  expect_parse "int x; int main(){ return x; }";
  expect_parse "int main(){ int x; return 0; }";
  expect_parse "int main(){ int a, b = 2, c; return a + b + c; }";
  expect_parse "int g = 1; int main(){ return g; }";
  expect_parse "int g; int main(){ return g; }";
  expect_parse "const int c = 1; int main(){ return c; }";
  expect_parse "const int a = 1, b = a + 2; int main(){ return b; }";
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
    ".text\n.globl main\nmain:\n  li a0, 42\n  ret\n";
  expect_compile_contains "int main(){ return 1 + 2 * 3; }"
    [ ".globl main"; "slli"; "add"; "ret" ];
  expect_compile_contains "int main(){ return -(1 + 2); }"
    [ ".globl main"; "add"; "neg"; "ret" ];
  expect_compile_contains "int main(){ return 1 < 2 && 3 != 4; }"
    [ ".globl main"; "slti"; "beq"; "ret" ];
  expect_compile_contains
    "int main(){ int a = 1; int b = 2; a = a + b; return a; }"
    [ ".globl main"; "li "; "add"; "ret" ];
  expect_compile_contains
    "int main(){ if (1) return 1; else return 0; }"
    [ ".L_main_if_else_"; ".L_main_if_end_"; "beqz"; "j .L_main_if_end_" ];
  expect_compile_contains
    "int main(){ int x = 0; while (x < 3) { x = x + 1; if (x == 2) continue; if (x > 2) break; } return x; }"
    [ ".L_main_while_cond_"; ".L_main_while_end_"; "slti";
      "bne"; "j .L_main_while_cond_" ];
  expect_compile_contains "int main(){ return 1 && 0 || 2; }"
    [ ".L_main_land_false_"; ".L_main_lor_rhs_"; "beqz";
      "j .L_main_lor_end_" ];
  expect_compile_contains
    "int id(int x){ return x; } int main(){ return id(1); }"
    [ ".globl __mytoyc_id"; "call __mytoyc_id"; "ret" ];
  expect_compile_lacks
    "int id(int x){ return x; } int main(){ return id(1); }"
    [ "sw s0"; "lw s0"; "mv t3, a0" ];
  expect_compile_contains
    "int add(int a,int b){ return a + b; } int main(){ return add(1,2); }"
    [ "__mytoyc_add:\n  add a0, a0, a1\n  ret" ];
  expect_compile_contains
    "int g(int x){ return x + 1; } int f(int x,int y){ int z = x * y + x; int r = g(x); return r + z; } int main(){ return f(3,4); }"
    [ "mv t3, a0"; "mul t4, t3, t4"; "call __mytoyc_g" ];
  expect_run_result
    "int ret = 5; int add(int a0, int t0){ return a0 + t0 + ret; } int main(){ int a0 = 1; return add(a0, 2); }"
    8;
  expect_run_result "int main(){ int a, b = 2, c; return a + b + c; }" 2;
  expect_run_result "const int a = 1, b = a + 2; int main(){ return b; }" 3;
  expect_compile_contains
    "int ret = 5; int add(int a0, int t0){ return a0 + t0 + ret; } int main(){ return add(1, 2); }"
    [ ".globl __mytoyc_ret"; "__mytoyc_ret:"; ".globl __mytoyc_add";
      "call __mytoyc_add"; "la t0, __mytoyc_ret" ];
  expect_compile_contains
    "void noop(){ return; } int main(){ noop(); return 0; }"
    [ ".globl __mytoyc_noop"; "call __mytoyc_noop"; "ret" ];
  expect_compile_contains
    "int g = 1; int main(){ return g; }"
    [ ".data"; ".globl __mytoyc_g"; "__mytoyc_g:"; ".word 1"; "la t0, __mytoyc_g"; "ret" ];
  expect_compile_contains
    "int g; int main(){ int x; return g + x; }"
    [ ".data"; ".globl __mytoyc_g"; "__mytoyc_g:"; ".word 0"; "ret" ];
  expect_compile_contains
    "int g = 1; int inc(int x){ return x + 1; } int main(){ g = inc(g); return g; }"
    [ ".data"; "call __mytoyc_inc"; "la t1, __mytoyc_g"; "ret" ];
  expect_compile_contains
    "const int a = 2; int g = a + 3; int main(){ return g; }"
    [ ".data"; ".word 5" ];
  expect_compile_contains
    "int init(){ return 7; } int g = init(); int main(){ return g; }"
    [ "__mytoyc___mytoyc_init_done"; ".L_main_global_init_"; "call __mytoyc_init" ];
  expect_compile_contains
    "int pick9(int a,int b,int c,int d,int e,int f,int g,int h,int i){ return i; } int main(){ return pick9(1,2,3,4,5,6,7,8,9); }"
    [ "call __mytoyc_pick9"; "sw t0, 0(sp)" ];
  expect_compile_contains
    "int main(){ int x = 0; if (x) { if (1) x = 1; else x = 2; } else { if (0) x = 3; else x = 4; } if (x) { if (x > 1) x = x + 1; else x = x + 2; } else { x = 0; } return x; }"
    [ ".L_main_if_else_"; ".L_main_if_end_"; "ret" ];
  expect_real_riscv_immediates (many_locals_source 530);
  expect_run_result (many_locals_source 100) 295;
  expect_run_result (many_locals_source 400) 1197;
  expect_real_riscv_immediates (many_args_source 520);
  expect_run_result (many_args_source 520) 519;
  expect_run_result (many_args_sum_source 120) (arithmetic_series_sum 120);
  expect_run_result
    "int sum(int n, int acc){ if (n == 0) return acc; return sum(n - 1, acc + n); } int main(){ return sum(10, 0); }"
    55;
  expect_opt_compile_contains
    "int sum(int n, int acc){ if (n == 0) return acc; return sum(n - 1, acc + n); } int main(){ return sum(10, 0); }"
    [ ".L_sum_tail_loop"; "j .L_sum_tail_loop" ];
  expect_opt_compile_contains "int main(){ int x = 7; return x * 1 + 0; }"
    [ "li a0, 7"; "ret" ];
  expect_opt_compile_lacks "int main(){ int x = 7; return x * 1 + 0; }"
    [ "  mul "; "  add " ];
  expect_opt_compile_contains "int main(){ int x = 7; return (x - x) + (x == x); }"
    [ "li a0, 1"; "ret" ];
  expect_opt_compile_contains "const int g = 5; int main(){ return g + 1; }"
    [ "li a0, 6"; "ret" ];
  expect_opt_compile_lacks "const int g = 5; int main(){ return g + 1; }"
    [ "la t0, __mytoyc_g" ];
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
  expect_opt_compile_contains
    "int main(){ int x = 3; int y = x; return y + 4; }"
    [ "li a0, 7"; "ret" ];
  expect_optimized_body
    Mytoyc.Ir.( [ LoadParam (0, 0); Move (1, Reg 0); Return (Reg 1) ] )
    Mytoyc.Ir.( [ LoadParam (0, 0); Return (Reg 0) ] );
  expect_optimized_body
    Mytoyc.Ir.
      ( [ LoadParam (0, 0); LoadParam (1, 1); Binary (2, Add, Reg 0, Reg 1);
          Binary (3, Add, Reg 0, Reg 1); Return (Reg 3) ] )
    Mytoyc.Ir.
      ( [ LoadParam (0, 0); LoadParam (1, 1); Binary (2, Add, Reg 0, Reg 1);
          Return (Reg 2) ] );
  expect_optimized_body
    Mytoyc.Ir.( [ LoadParam (0, 0); Binary (1, Add, Reg 0, Reg 0); Return (Reg 1) ] )
    Mytoyc.Ir.( [ LoadParam (0, 0); ShiftLeft (1, Reg 0, 1); Return (Reg 1) ] );
  let branch_func =
    Mytoyc.Ir.
      {
        name = "main";
        body =
          [ LoadParam (0, 0); BranchZero (Reg 0, ".L_main_else"); Return (Imm 1);
            Label ".L_main_else"; Return (Imm 2) ];
      }
  in
  let block_func = Mytoyc.Bb_ir.of_ir_func branch_func in
  let block_cfg = Mytoyc.Cfg.of_blocks block_func in
  if Array.length block_cfg.Mytoyc.Cfg.blocks <> 3 then
    failwith "basic block split mismatch";
  (match block_cfg.Mytoyc.Cfg.blocks.(0).Mytoyc.Bb_ir.terminator with
  | BranchZero
      ( Reg 0,
        { label = ".L_main_else"; args = [] },
        Some { label = ".L_main_fallthrough_0"; args = [] } ) ->
      ()
  | _ -> failwith "basic block terminator mismatch");
  if List.length block_cfg.Mytoyc.Cfg.block_succs.(0) <> 2 then
    failwith "basic block cfg successor mismatch";
  let roundtrip = Mytoyc.Bb_ir.to_ir_func block_func in
  if
    Mytoyc.Riscv.emit_program Mytoyc.Ir.{ globals = []; funcs = [ roundtrip ] }
    |> Riscv_sim.run <> 2
  then
    failwith "basic block roundtrip mismatch";
  let cmp_func =
    Mytoyc.Ir.
      {
        name = "main";
        body =
          [ Move (0, Imm 1); Move (1, Imm 2); Binary (2, Lt, Reg 0, Reg 1);
            BranchZero (Reg 2, ".L_main_false"); Return (Imm 1);
            Label ".L_main_false"; Return (Imm 0) ];
      }
  in
  let cmp_block_func = Mytoyc.Bb_ir.of_ir_func cmp_func |> Mytoyc.Bb_ir.fuse_branch_cmp in
  (match (List.hd cmp_block_func.Mytoyc.Bb_ir.blocks).Mytoyc.Bb_ir.terminator with
  | BranchCmp
      ( Lt,
        Reg 0,
        Reg 1,
        { label = ".L_main_false"; args = [] },
        Some { label = ".L_main_fallthrough_0"; args = [] } ) ->
      ()
  | _ -> failwith "branch compare fusion mismatch");
  if
    cmp_block_func |> Mytoyc.Bb_ir.to_ir_func
    |> fun func -> Mytoyc.Riscv.emit_program Mytoyc.Ir.{ globals = []; funcs = [ func ] }
    |> Riscv_sim.run <> 1
  then
    failwith "branch compare roundtrip mismatch";
  let param_block_func =
    Mytoyc.Bb_ir.
      {
        name = "main";
        entry = ".L_main_entry";
        blocks =
          [ { label = ".L_main_entry";
              params = [];
              instrs = [];
              terminator = Jump { label = ".L_main_join"; args = [ Imm 41 ] } };
            { label = ".L_main_join";
              params = [ 0 ];
              instrs = [ Binary (1, Add, Reg 0, Imm 1) ];
              terminator = Return (Reg 1) } ];
      }
  in
  let param_cfg = Mytoyc.Cfg.of_blocks param_block_func in
  if not (Mytoyc.Cfg.IntSet.mem 0 param_cfg.Mytoyc.Cfg.block_defs.(1)) then
    failwith "block parameter defs mismatch";
  if
    param_block_func |> Mytoyc.Bb_ir.to_ir_func
    |> fun func -> Mytoyc.Riscv.emit_program Mytoyc.Ir.{ globals = []; funcs = [ func ] }
    |> Riscv_sim.run <> 42
  then
    failwith "block parameter lowering mismatch";
  let ssa_join_func =
    Mytoyc.Ir.
      {
        name = "main";
        body =
          [ Move (0, Imm 0); BranchZero (Reg 0, ".L_main_else");
            Move (1, Imm 1); Jump ".L_main_join"; Label ".L_main_else";
            Move (1, Imm 2); Label ".L_main_join"; Return (Reg 1) ];
      }
  in
  let ssa_join_block_func =
    ssa_join_func |> Mytoyc.Bb_ir.of_ir_func |> Mytoyc.Bb_ir.add_livein_params
  in
  let join_block =
    List.find
      (fun block -> block.Mytoyc.Bb_ir.label = ".L_main_join")
      ssa_join_block_func.Mytoyc.Bb_ir.blocks
  in
  if List.length join_block.Mytoyc.Bb_ir.params <> 1 then
    failwith "ssa join block parameter mismatch";
  if
    ssa_join_block_func |> Mytoyc.Bb_ir.to_ir_func
    |> fun func -> Mytoyc.Riscv.emit_program Mytoyc.Ir.{ globals = []; funcs = [ func ] }
    |> Riscv_sim.run <> 2
  then
    failwith "ssa join lowering mismatch";
  let ssa_loop_func =
    Mytoyc.Ir.
      {
        name = "main";
        body =
          [ Move (0, Imm 0); Label ".L_main_cond";
            Binary (1, Lt, Reg 0, Imm 3); BranchZero (Reg 1, ".L_main_end");
            Binary (0, Add, Reg 0, Imm 1); Jump ".L_main_cond";
            Label ".L_main_end"; Return (Reg 0) ];
      }
  in
  let ssa_loop_block_func =
    ssa_loop_func |> Mytoyc.Bb_ir.of_ir_func |> Mytoyc.Bb_ir.add_livein_params
  in
  let cond_block =
    List.find
      (fun block -> block.Mytoyc.Bb_ir.label = ".L_main_cond")
      ssa_loop_block_func.Mytoyc.Bb_ir.blocks
  in
  if List.length cond_block.Mytoyc.Bb_ir.params <> 1 then
    failwith "ssa loop block parameter mismatch";
  if
    ssa_loop_block_func |> Mytoyc.Bb_ir.to_ir_func
    |> fun func -> Mytoyc.Riscv.emit_program Mytoyc.Ir.{ globals = []; funcs = [ func ] }
    |> Riscv_sim.run <> 3
  then
    failwith "ssa loop lowering mismatch";
  expect_optimized_body
    Mytoyc.Ir.
      ( [ Move (0, Imm 1); StoreGlobal ("g", Reg 0); Move (1, Imm 2);
          StoreGlobal ("g", Reg 1); Return (Imm 0) ] )
    Mytoyc.Ir.( [ StoreGlobal ("g", Imm 2); Return (Imm 0) ] );
  if
    Mytoyc.Riscv.peephole_asm
      ".text\n  sw t0, 0(s0)\n  lw t1, 0(s0)\n  lw t2, 4(s0)\n  sw t2, 4(s0)\n"
    <> ".text\n  sw t0, 0(s0)\n  mv t1, t0\n  lw t2, 4(s0)\n"
  then failwith "riscv peephole mismatch";
  if
    Mytoyc.Riscv.peephole_asm ".text\n  mv t3, a0\n  mv a0, t3\n"
    <> ".text\n  mv t3, a0\n"
  then failwith "riscv move peephole mismatch";
  expect_opt_compile_contains
    "int main(){ int x = 5; return x * 8; }"
    [ "li a0, 40"; "ret" ];
  expect_opt_compile_contains
    "int f(int x){ if (x) return x * 8; return 0; } int main(){ return f(5); }"
    [ "slli"; "ret" ];
  expect_opt_compile_lacks
    "int f(int x){ if (x) return x * 8; return 0; } int main(){ return f(5); }"
    [ "  mul " ];
  expect_opt_compile_contains
    "int f(int n){ int i = 0; int s = 0; while (i < n) { s = s + i * 3; i = i + 1; } return s; } int main(){ return f(100); }"
    [ "addi a3, a3, 3"; "add a2, a2, a3" ];
  expect_opt_compile_lacks
    "int f(int n){ int i = 0; int s = 0; while (i < n) { s = s + i * 3; i = i + 1; } return s; } int main(){ return f(100); }"
    [ "  mul " ];
  expect_opt_run_result
    "int f(int n){ int i=0; int s=0; while(i<n){ s = s + i * 3 + i * 5; i = i + 1; } return s; } int main(){ return f(5); }"
    80;
  expect_opt_compile_lacks
    "int f(int n){ int i=0; int s=0; while(i<n){ s = s + i * 3 + i * 3; i = i + 1; } return s; } int main(){ return f(5); }"
    [ "  mul " ];
  expect_opt_compile_lacks
    "int f(int n){ int i=0; int s=0; while(i<n){ s = s + i * 8; i = i + 1; } return s; } int main(){ return f(5); }"
    [ "slli" ];
  expect_opt_compile_lacks
    "int f(int x){ if (x) return x * 10; return 0; } int main(){ return f(5); }"
    [ "  mul " ];
  expect_opt_compile_lacks
    "int main(){ if (1) return 3; else return 4; }"
    [ "li a0, 4"; "beqz" ];
  expect_opt_compile_lacks
    "int main(){ int x = 0; while (0) { x = x + 1; } return x; }"
    [ ".L_main_while_cond_"; "beqz" ];
  expect_opt_compile_lacks
    "int main(){ int i = 0; while (i < 1000) { int x = i * i; i = i + 1; } return 7; }"
    [ ".L_main_while_cond_"; "  mul " ];
  expect_opt_run_result
    "int g = 0; int main(){ int i = 0; while (i < 3) { g = g + 1; i = i + 1; } return g; }"
    3;
  expect_opt_compile_count
    "int f(int x,int y){ int a = x + y; if (x) return a + (x + y); return a; } int main(){ return f(2,3); }"
    "  add " 2;
  expect_opt_compile_contains
    "int add(int a,int b){ return a + b; } int main(){ return add(1, 2); }"
    [ "li a0, 3"; "ret" ];
  expect_opt_compile_lacks
    "int add(int a,int b){ return a + b; } int main(){ return add(1, 2); }"
    [ "call __mytoyc_add"; "__mytoyc_add:" ];
  expect_opt_compile_contains
    "int f(int x){ return x + 1; } int g(int y){ return f(y) * 2; } int main(){ return g(3); }"
    [ "li a0, 8"; "ret" ];
  expect_opt_compile_lacks
    "int f(int x){ return x + 1; } int g(int y){ return f(y) * 2; } int main(){ return g(3); }"
    [ "call __mytoyc_f"; "call __mytoyc_g"; "__mytoyc_f:"; "__mytoyc_g:" ];
  expect_opt_compile_contains
    "int h(int a,int b,int c){ int x=a+b; int y=b+c; int z=x*y; int w=z+a; return w-c; } int main(){ return h(1,2,3); }"
    [ "li a0, 13"; "ret" ];
  expect_opt_compile_lacks
    "int h(int a,int b,int c){ int x=a+b; int y=b+c; int z=x*y; int w=z+a; return w-c; } int main(){ return h(1,2,3); }"
    [ "call __mytoyc_h"; "__mytoyc_h:" ];
  expect_opt_compile_lacks
    "int unused(){ return 9; } int main(){ return 1; }"
    [ "__mytoyc_unused" ];
  expect_opt_compile_contains
    "int sum(int n,int acc){ if (n <= 0) return acc; return sum(n - 1, acc + n); } int main(){ return sum(5,0); }"
    [ ".L_sum_tail_loop"; "j .L_sum_tail_loop" ];
  expect_opt_compile_count
    "int sum(int n,int acc){ if (n <= 0) return acc; return sum(n - 1, acc + n); } int main(){ return sum(5,0); }"
    "call __mytoyc_sum" 1;
  expect_opt_run_result
    "int sum(int n,int acc){ if (n <= 0) return acc; return sum(n - 1, acc + n); } int main(){ return sum(5,0); }"
    15;
  expect_opt_compile_contains
    "int f(int n,int a,int b){ int i = 0; int s = 0; while (i < n) { int x = a + b; s = s + x; i = i + 1; } return s; } int main(){ return f(3,4,5); }"
    [ "add a6, a1, a2\n.L_f_while_cond_" ];
  expect_opt_run_result
    "int f(int n,int a,int b){ int i = 0; int s = 0; while (i < n) { int x = a + b; s = s + x; i = i + 1; } return s; } int main(){ return f(3,4,5); }"
    27;
  expect_opt_compile_contains
    "int f(int x){ if (x < 10) return x + 5; return x - 3; } int main(){ return f(1); }"
    [ "slti"; "ret" ];
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

let () =
  expect_run_result
    "int f(int x){ return x + 1; } int g(int x){ return x * 2; } int main(){ return f(10) + g(20) * f(1); }"
    91;
  expect_run_result
    "int main(){ int x = 1; if (1) x = x + 2; while (x < 5) x = x + 1; return x; }"
    5;
  expect_run_result
    "int acc = 0; int add(int x){ acc = acc + x; return acc; } int fib(int n){ if (n <= 1) return n; return fib(n - 1) + fib(n - 2); } int main(){ int i = 0; int s = 0; while (i < 6) { s = s + fib(i); add(i); i = i + 1; } return s + acc; }"
    27


let () =
  expect_run_result "const int c = 0 && (1 / 0); int main(){ return c; }" 0;
  expect_run_result "const int c = 1 || (1 / 0); int main(){ return c; }" 1

let () =
  expect_run_result "int f(){ if (1 || (1 / 0)) return 1; } int main(){ return f(); }" 1;
  expect_run_result "int f(){ if (0 && (1 / 0)) return 1; else return 2; } int main(){ return f(); }" 2

let () =
  expect_run_result "int main(){ if (1) int x = 3; return x; }" 3;
  expect_run_result "int main(){ int x = 1; if (1) { int x = 3; } return x; }" 1;
  expect_run_result "int main(){ int x = 1; if (1) x = x + 4; return x; }" 5

let () =
  expect_run_result "int main(){ int y = 0; if (1) int x = 3; else y = 2; return x + y; }" 3;
  expect_run_result "int main(){ int y = 0; if (0) y = 2; else int x = 4; return x + y; }" 4
