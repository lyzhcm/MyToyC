type env = {
  vars : Ir.vreg Symbol.StringMap.t;
  next_reg : int;
}

let empty_env = { vars = Symbol.StringMap.empty; next_reg = 0 }

let fresh env =
  (env.next_reg, { env with next_reg = env.next_reg + 1 })

let find_var env name =
  match Symbol.StringMap.find_opt name env.vars with
  | Some reg -> reg
  | None -> Diagnostic.fail (Printf.sprintf "undefined variable: %s" name)

let add_var env name reg =
  { env with vars = Symbol.StringMap.add name reg env.vars }

let rec lower_expr env = function
  | Ast.Int value -> (env, [], Ir.Imm value)
  | Ast.Var name -> (env, [], Ir.Reg (find_var env name))
  | Ast.Unary (op, expr) ->
      let env, code, operand = lower_expr env expr in
      let dest, env = fresh env in
      (env, code @ [ Ir.Unary (dest, op, operand) ], Ir.Reg dest)
  | Ast.Binary (op, lhs, rhs) ->
      let env, left_code, left = lower_expr env lhs in
      let env, right_code, right = lower_expr env rhs in
      let dest, env = fresh env in
      (env, left_code @ right_code @ [ Ir.Binary (dest, op, left, right) ], Ir.Reg dest)
  | Ast.Call (name, _) ->
      Diagnostic.fail
        (Printf.sprintf "backend does not support function call yet: %s" name)

let lower_decl env = function
  | Ast.ConstDecl (name, expr) | Ast.VarDecl (name, Some expr) ->
      let dest, env = fresh env in
      let env = add_var env name dest in
      let env, code, value = lower_expr env expr in
      (env, code @ [ Ir.Move (dest, value) ])
  | Ast.VarDecl (name, None) ->
      let dest, env = fresh env in
      let env = add_var env name dest in
      (env, [ Ir.Move (dest, Ir.Imm 0) ])

let rec lower_stmt env = function
  | Ast.Block body ->
      List.fold_left
        (fun (env, code) stmt ->
          let env, stmt_code = lower_stmt env stmt in
          (env, code @ stmt_code))
        (env, []) body
  | Ast.Empty -> (env, [])
  | Ast.DeclStmt decl -> lower_decl env decl
  | Ast.Assign (name, expr) ->
      let dest = find_var env name in
      let env, code, value = lower_expr env expr in
      (env, code @ [ Ir.Move (dest, value) ])
  | Ast.ExprStmt expr ->
      let env, code, _ = lower_expr env expr in
      (env, code)
  | Ast.Return None -> (env, [ Ir.Return (Ir.Imm 0) ])
  | Ast.Return (Some expr) ->
      let env, code, value = lower_expr env expr in
      (env, code @ [ Ir.Return value ])
  | Ast.If _ -> Diagnostic.fail "backend does not support if statement yet"
  | Ast.While _ -> Diagnostic.fail "backend does not support while statement yet"
  | Ast.Break -> Diagnostic.fail "backend does not support break statement yet"
  | Ast.Continue -> Diagnostic.fail "backend does not support continue statement yet"

let lower_func func =
  let env, param_moves =
    List.fold_left
      (fun (env, code) param ->
        let dest, env = fresh env in
        let env = add_var env param.Ast.param_name dest in
        (env, code @ [ Ir.Move (dest, Ir.Imm 0) ]))
      (empty_env, []) func.Ast.params
  in
  let _, body =
    List.fold_left
      (fun (env, code) stmt ->
        let env, stmt_code = lower_stmt env stmt in
        (env, code @ stmt_code))
      (env, param_moves) func.Ast.body
  in
  { Ir.name = func.Ast.name; body }

let lower_program (program : Ast.program) : Ir.program =
  program
  |> List.filter_map (function
       | Ast.GlobalDecl _ -> None
       | Ast.FuncDef func -> Some (lower_func func))
