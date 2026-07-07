type loop_target = {
  break_label : string;
  continue_label : string;
}

type func_sig = {
  return_type : Ast.typ;
}

type env = {
  locals : Ir.vreg Symbol.StringMap.t;
  globals : unit Symbol.StringMap.t;
  funcs : func_sig Symbol.StringMap.t;
  next_reg : int;
  next_label : int;
  loops : loop_target list;
  label_namespace : string;
}

let global_init_guard_name = "__mytoyc_init_done"

let empty_env =
  {
    locals = Symbol.StringMap.empty;
    globals = Symbol.StringMap.empty;
    funcs = Symbol.StringMap.empty;
    next_reg = 0;
    next_label = 0;
    loops = [];
    label_namespace = "global";
  }

let fresh env =
  (env.next_reg, { env with next_reg = env.next_reg + 1 })

let fresh_label env prefix =
  ( Printf.sprintf ".L_%s_%s_%d" env.label_namespace prefix env.next_label,
    { env with next_label = env.next_label + 1 } )

type var_ref =
  | Local of Ir.vreg
  | Global of string

let find_var env name =
  match Symbol.StringMap.find_opt name env.locals with
  | Some reg -> Local reg
  | None -> (
      match Symbol.StringMap.find_opt name env.globals with
      | Some () -> Global name
      | None -> Diagnostic.fail (Printf.sprintf "undefined variable: %s" name))

let add_var env name reg =
  { env with locals = Symbol.StringMap.add name reg env.locals }

let find_func env name =
  match Symbol.StringMap.find_opt name env.funcs with
  | Some sig_ -> sig_
  | None -> Diagnostic.fail (Printf.sprintf "undefined function: %s" name)

let with_saved_vars env f =
  let saved_vars = env.locals in
  let env, code = f env in
  ({ env with locals = saved_vars }, code)

let current_loop env =
  match env.loops with
  | loop :: _ -> loop
  | [] -> Diagnostic.fail "internal error: loop target missing"

let rec lower_expr env = function
  | Ast.Int value -> (env, [], Ir.Imm value)
  | Ast.Var name -> lower_var env name
  | Ast.Unary (op, expr) ->
      let env, code, operand = lower_expr env expr in
      let dest, env = fresh env in
      (env, code @ [ Ir.Unary (dest, op, operand) ], Ir.Reg dest)
  | Ast.Binary (Ast.LAnd, lhs, rhs) -> lower_land env lhs rhs
  | Ast.Binary (Ast.LOr, lhs, rhs) -> lower_lor env lhs rhs
  | Ast.Binary (op, lhs, rhs) ->
      let env, left_code, left = lower_expr env lhs in
      let env, right_code, right = lower_expr env rhs in
      let dest, env = fresh env in
      (env, left_code @ right_code @ [ Ir.Binary (dest, op, left, right) ], Ir.Reg dest)
  | Ast.Call (name, args) -> lower_call_expr env name args

and lower_var env name =
  match find_var env name with
  | Local reg -> (env, [], Ir.Reg reg)
  | Global name ->
      let dest, env = fresh env in
      (env, [ Ir.LoadGlobal (dest, name) ], Ir.Reg dest)

and lower_land env lhs rhs =
  let env, left_code, left = lower_expr env lhs in
  let dest, env = fresh env in
  let false_label, env = fresh_label env "land_false" in
  let end_label, env = fresh_label env "land_end" in
  let env, right_code, right = lower_expr env rhs in
  ( env,
    left_code
    @ [ Ir.BranchZero (left, false_label) ]
    @ right_code
    @ [ Ir.BranchZero (right, false_label);
        Ir.Move (dest, Ir.Imm 1);
        Ir.Jump end_label;
        Ir.Label false_label;
        Ir.Move (dest, Ir.Imm 0);
        Ir.Label end_label ],
    Ir.Reg dest )

and lower_lor env lhs rhs =
  let env, left_code, left = lower_expr env lhs in
  let dest, env = fresh env in
  let rhs_label, env = fresh_label env "lor_rhs" in
  let false_label, env = fresh_label env "lor_false" in
  let end_label, env = fresh_label env "lor_end" in
  let env, right_code, right = lower_expr env rhs in
  ( env,
    left_code
    @ [ Ir.BranchZero (left, rhs_label);
        Ir.Move (dest, Ir.Imm 1);
        Ir.Jump end_label;
        Ir.Label rhs_label ]
    @ right_code
    @ [ Ir.BranchZero (right, false_label);
        Ir.Move (dest, Ir.Imm 1);
        Ir.Jump end_label;
        Ir.Label false_label;
        Ir.Move (dest, Ir.Imm 0);
        Ir.Label end_label ],
    Ir.Reg dest )

and lower_call env dest name args =
  let _ = find_func env name in
  let env, rev_args, rev_code =
    List.fold_left
      (fun (env, args_acc, code_acc) arg ->
        let env, arg_code, operand = lower_expr env arg in
        (env, operand :: args_acc, code_acc @ arg_code))
      (env, [], []) args
  in
  (env, rev_code @ [ Ir.Call (dest, name, List.rev rev_args) ])

and lower_call_expr env name args =
  let sig_ = find_func env name in
  match sig_.return_type with
  | Ast.TVoid ->
      Diagnostic.fail
        (Printf.sprintf "void function cannot be used as a value: %s" name)
  | Ast.TInt ->
      let dest, env = fresh env in
      let env, code = lower_call env (Some dest) name args in
      (env, code, Ir.Reg dest)

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
  | Ast.Block body -> lower_block env body
  | Ast.Empty -> (env, [])
  | Ast.DeclStmt decl -> lower_decl env decl
  | Ast.Assign (name, expr) ->
      let env, code, value = lower_expr env expr in
      let store =
        match find_var env name with
        | Local dest -> [ Ir.Move (dest, value) ]
        | Global global_name -> [ Ir.StoreGlobal (global_name, value) ]
      in
      (env, code @ store)
  | Ast.ExprStmt (Ast.Call (name, args)) -> lower_expr_stmt_call env name args
  | Ast.ExprStmt expr ->
      let env, code, _ = lower_expr env expr in
      (env, code)
  | Ast.Return None -> (env, [ Ir.Return (Ir.Imm 0) ])
  | Ast.Return (Some expr) ->
      let env, code, value = lower_expr env expr in
      (env, code @ [ Ir.Return value ])
  | Ast.If (cond, then_branch, else_branch) ->
      lower_if env cond then_branch else_branch
  | Ast.While (cond, body) -> lower_while env cond body
  | Ast.Break ->
      let loop = current_loop env in
      (env, [ Ir.Jump loop.break_label ])
  | Ast.Continue ->
      let loop = current_loop env in
      (env, [ Ir.Jump loop.continue_label ])

and lower_expr_stmt_call env name args =
  let sig_ = find_func env name in
  match sig_.return_type with
  | Ast.TVoid -> lower_call env None name args
  | Ast.TInt ->
      let env, code, _ = lower_call_expr env name args in
      (env, code)

and lower_block env body =
  with_saved_vars env (fun env ->
      List.fold_left
        (fun (env, code) stmt ->
          let env, stmt_code = lower_stmt env stmt in
          (env, code @ stmt_code))
        (env, []) body)

and lower_scoped_stmt env stmt =
  with_saved_vars env (fun env -> lower_stmt env stmt)

and lower_if env cond then_branch else_branch =
  let env, cond_code, cond_value = lower_expr env cond in
  match else_branch with
  | None ->
      let end_label, env = fresh_label env "if_end" in
      let env, then_code = lower_scoped_stmt env then_branch in
      ( env,
        cond_code
        @ [ Ir.BranchZero (cond_value, end_label) ]
        @ then_code
        @ [ Ir.Label end_label ] )
  | Some else_branch ->
      let else_label, env = fresh_label env "if_else" in
      let end_label, env = fresh_label env "if_end" in
      let env, then_code = lower_scoped_stmt env then_branch in
      let env, else_code = lower_scoped_stmt env else_branch in
      ( env,
        cond_code
        @ [ Ir.BranchZero (cond_value, else_label) ]
        @ then_code
        @ [ Ir.Jump end_label; Ir.Label else_label ]
        @ else_code
        @ [ Ir.Label end_label ] )

and lower_while env cond body =
  let cond_label, env = fresh_label env "while_cond" in
  let end_label, env = fresh_label env "while_end" in
  let env, cond_code, cond_value = lower_expr env cond in
  let loop_env =
    { env with loops = { break_label = end_label; continue_label = cond_label } :: env.loops }
  in
  let loop_env, body_code = lower_scoped_stmt loop_env body in
  let env = { loop_env with loops = env.loops } in
  ( env,
    [ Ir.Label cond_label ]
    @ cond_code
    @ [ Ir.BranchZero (cond_value, end_label) ]
    @ body_code
    @ [ Ir.Jump cond_label; Ir.Label end_label ] )

let lower_global_decl env = function
  | Ast.ConstDecl (name, expr) | Ast.VarDecl (name, Some expr) ->
      let env, code, value = lower_expr env expr in
      (env, code @ [ Ir.StoreGlobal (name, value) ])
  | Ast.VarDecl (_, None) -> (env, [])

let lower_global_init_decls env decls =
  List.fold_left
    (fun (env, code) decl ->
      let env, decl_code = lower_global_decl env decl in
      (env, code @ decl_code))
    (env, []) decls

let lower_guarded_global_init env decls =
  if decls = [] then (env, [])
  else
    let flag_reg, env = fresh env in
    let init_label, env = fresh_label env "global_init" in
    let end_label, env = fresh_label env "global_init_end" in
    let env, init_code = lower_global_init_decls env decls in
    ( env,
      [ Ir.LoadGlobal (flag_reg, global_init_guard_name);
        Ir.BranchZero (Ir.Reg flag_reg, init_label);
        Ir.Jump end_label;
        Ir.Label init_label;
        Ir.StoreGlobal (global_init_guard_name, Ir.Imm 1) ]
      @ init_code
      @ [ Ir.Label end_label ] )

let lower_func base_env ?(global_init_decls = []) func =
  let env =
    {
      base_env with
      locals = Symbol.StringMap.empty;
      next_reg = 0;
      next_label = 0;
      loops = [];
      label_namespace = func.Ast.name;
    }
  in
  let env, param_moves =
    List.fold_left
      (fun (env, code) (index, param) ->
        let dest, env = fresh env in
        let env = add_var env param.Ast.param_name dest in
        (env, code @ [ Ir.LoadParam (dest, index) ]))
      (env, []) (List.mapi (fun index param -> (index, param)) func.Ast.params)
  in
  let env, global_init_code =
    lower_guarded_global_init env global_init_decls
  in
  let _, body =
    List.fold_left
      (fun (env, code) stmt ->
        let env, stmt_code = lower_stmt env stmt in
        (env, code @ stmt_code))
      (env, param_moves @ global_init_code) func.Ast.body
  in
  { Ir.name = func.Ast.name; body }

let build_global_env (program : Ast.program) =
  List.fold_left
    (fun globals item ->
      match item with
      | Ast.GlobalDecl (Ast.ConstDecl (name, _) | Ast.VarDecl (name, _)) ->
          Symbol.StringMap.add name () globals
      | Ast.FuncDef _ -> globals)
    Symbol.StringMap.empty program

let build_func_env (program : Ast.program) =
  List.fold_left
    (fun funcs item ->
      match item with
      | Ast.GlobalDecl _ -> funcs
      | Ast.FuncDef func ->
          Symbol.StringMap.add func.Ast.name { return_type = func.return_type } funcs)
    Symbol.StringMap.empty program

let bool_to_int value =
  if value then 1 else 0

let apply_unop op value =
  match op with
  | Ast.Pos -> value
  | Ast.Neg -> -value
  | Ast.LNot -> bool_to_int (value = 0)

let apply_binop op lhs rhs =
  match op with
  | Ast.Add -> Some (lhs + rhs)
  | Ast.Sub -> Some (lhs - rhs)
  | Ast.Mul -> Some (lhs * rhs)
  | Ast.Div ->
      if rhs = 0 then None else Some (lhs / rhs)
  | Ast.Mod ->
      if rhs = 0 then None else Some (lhs mod rhs)
  | Ast.Lt -> Some (bool_to_int (lhs < rhs))
  | Ast.Gt -> Some (bool_to_int (lhs > rhs))
  | Ast.Le -> Some (bool_to_int (lhs <= rhs))
  | Ast.Ge -> Some (bool_to_int (lhs >= rhs))
  | Ast.Eq -> Some (bool_to_int (lhs = rhs))
  | Ast.Ne -> Some (bool_to_int (lhs <> rhs))
  | Ast.LAnd -> Some (bool_to_int (lhs <> 0 && rhs <> 0))
  | Ast.LOr -> Some (bool_to_int (lhs <> 0 || rhs <> 0))

let rec eval_static_expr consts = function
  | Ast.Int value -> Some value
  | Ast.Var name -> Symbol.StringMap.find_opt name consts
  | Ast.Unary (op, expr) -> Option.map (apply_unop op) (eval_static_expr consts expr)
  | Ast.Binary (op, lhs, rhs) -> (
      match (eval_static_expr consts lhs, eval_static_expr consts rhs) with
      | Some lhs, Some rhs -> apply_binop op lhs rhs
      | _ -> None)
  | Ast.Call _ -> None

let collect_global_initializers (program : Ast.program) =
  List.fold_left
    (fun (consts, globals, runtime_decls) item ->
      match item with
      | Ast.FuncDef _ -> (consts, globals, runtime_decls)
      | Ast.GlobalDecl decl -> (
          match decl with
          | Ast.ConstDecl (name, expr) -> (
              match eval_static_expr consts expr with
              | Some value ->
                  ( Symbol.StringMap.add name value consts,
                    { Ir.name; init = value } :: globals,
                    runtime_decls )
              | None ->
                  (consts, { Ir.name; init = 0 } :: globals, decl :: runtime_decls))
          | Ast.VarDecl (name, Some expr) -> (
              match eval_static_expr consts expr with
              | Some value ->
                  (consts, { Ir.name; init = value } :: globals, runtime_decls)
              | None ->
                  (consts, { Ir.name; init = 0 } :: globals, decl :: runtime_decls))
          | Ast.VarDecl (name, None) ->
              (consts, { Ir.name; init = 0 } :: globals, runtime_decls)))
    (Symbol.StringMap.empty, [], []) program
  |> fun (_, globals, runtime_decls) -> (List.rev globals, List.rev runtime_decls)

let lower_program (program : Ast.program) : Ir.program =
  let globals, global_init_decls = collect_global_initializers program in
  let globals =
    if global_init_decls = [] then globals
    else { Ir.name = global_init_guard_name; init = 0 } :: globals
  in
  let globals_env = build_global_env program in
  let globals_env =
    if global_init_decls = [] then globals_env
    else Symbol.StringMap.add global_init_guard_name () globals_env
  in
  let funcs_env = build_func_env program in
  let base_env =
    { empty_env with globals = globals_env; funcs = funcs_env }
  in
  let funcs =
    program
    |> List.filter_map (function
         | Ast.GlobalDecl _ -> None
         | Ast.FuncDef func ->
             let global_init_decls =
               if func.Ast.name = "main" then global_init_decls else []
             in
             Some (lower_func base_env ~global_init_decls func))
  in
  { Ir.globals; funcs }
