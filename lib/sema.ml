module StringMap = Symbol.StringMap
module StringSet = Set.Make (String)

type func_sig = {
  return_type : Ast.typ;
  param_count : int;
}

type binding = {
  mutable_ : bool;
  const_value : int option;
}

type env = {
  globals : binding StringMap.t;
  funcs : func_sig StringMap.t;
  scopes : binding StringMap.t list;
  in_loop : bool;
}

type top_level_env = {
  declared_globals : binding StringMap.t;
  declared_funcs : func_sig StringMap.t;
}

let empty_env funcs globals =
  { funcs; globals; scopes = [ StringMap.empty ]; in_loop = false }

let empty_top_level_env =
  { declared_globals = StringMap.empty; declared_funcs = StringMap.empty }

let enter_scope env =
  { env with scopes = StringMap.empty :: env.scopes }

let leave_scope env =
  match env.scopes with
  | _ :: rest -> { env with scopes = rest }
  | [] -> env

let current_scope (env : env) =
  match env.scopes with
  | scope :: _ -> scope
  | [] -> StringMap.empty

let replace_current_scope (env : env) scope =
  match env.scopes with
  | _ :: rest -> { env with scopes = scope :: rest }
  | [] -> { env with scopes = [ scope ] }

let declare_local (env : env) name binding =
  let scope = current_scope env in
  if StringMap.mem name scope then
    Diagnostic.fail (Printf.sprintf "duplicate variable: %s" name);
  replace_current_scope env (StringMap.add name binding scope)

let rec find_in_scopes name = function
  | [] -> None
  | scope :: rest -> (
      match StringMap.find_opt name scope with
      | Some binding -> Some binding
      | None -> find_in_scopes name rest)

let find_binding env name =
  match find_in_scopes name env.scopes with
  | Some binding -> Some binding
  | None -> StringMap.find_opt name env.globals

let find_binding_exn env name =
  match find_binding env name with
  | Some binding -> binding
  | None -> Diagnostic.fail (Printf.sprintf "undefined variable: %s" name)

let ensure_int context = function
  | Ast.TInt -> ()
  | Ast.TVoid ->
      Diagnostic.fail (Printf.sprintf "%s requires an int expression" context)

let bool_to_int value =
  if value then 1 else 0

let i32 value =
  Int32.to_int (Int32.of_int value)

let apply_unop op value =
  match op with
  | Ast.Pos -> i32 value
  | Ast.Neg -> i32 (-value)
  | Ast.LNot -> bool_to_int (value = 0)

let apply_binop op lhs rhs =
  match op with
  | Ast.Add -> i32 (lhs + rhs)
  | Ast.Sub -> i32 (lhs - rhs)
  | Ast.Mul -> i32 (lhs * rhs)
  | Ast.Div ->
      if rhs = 0 then Diagnostic.fail "division by zero in constant expression";
      Int32.(to_int (div (of_int lhs) (of_int rhs)))
  | Ast.Mod ->
      if rhs = 0 then Diagnostic.fail "modulo by zero in constant expression";
      Int32.(to_int (rem (of_int lhs) (of_int rhs)))
  | Ast.Lt -> bool_to_int (lhs < rhs)
  | Ast.Gt -> bool_to_int (lhs > rhs)
  | Ast.Le -> bool_to_int (lhs <= rhs)
  | Ast.Ge -> bool_to_int (lhs >= rhs)
  | Ast.Eq -> bool_to_int (lhs = rhs)
  | Ast.Ne -> bool_to_int (lhs <> rhs)
  | Ast.LAnd -> bool_to_int (lhs <> 0 && rhs <> 0)
  | Ast.LOr -> bool_to_int (lhs <> 0 || rhs <> 0)

let rec eval_const_expr env = function
  | Ast.Int value -> i32 value
  | Ast.Var name -> (
      match find_binding env name with
      | Some { const_value = Some value; _ } -> value
      | Some _ ->
          Diagnostic.fail
            (Printf.sprintf
               "const initializer must be a compile-time constant: %s" name)
      | None -> Diagnostic.fail (Printf.sprintf "undefined variable: %s" name))
  | Ast.Unary (op, expr) -> apply_unop op (eval_const_expr env expr)
  | Ast.Binary (Ast.LAnd, lhs, rhs) ->
      let lhs_value = eval_const_expr env lhs in
      if lhs_value = 0 then 0
      else bool_to_int (eval_const_expr env rhs <> 0)
  | Ast.Binary (Ast.LOr, lhs, rhs) ->
      let lhs_value = eval_const_expr env lhs in
      if lhs_value <> 0 then 1
      else bool_to_int (eval_const_expr env rhs <> 0)
  | Ast.Binary (op, lhs, rhs) ->
      apply_binop op (eval_const_expr env lhs) (eval_const_expr env rhs)
  | Ast.Call (name, _) ->
      Diagnostic.fail
        (Printf.sprintf
           "const initializer must be a compile-time constant: call to %s" name)

let rec check_expr env = function
  | Ast.Int _ -> Ast.TInt
  | Ast.Unary (_, expr) ->
      let typ = check_expr env expr in
      ensure_int "unary operator" typ;
      Ast.TInt
  | Ast.Binary (_, lhs, rhs) ->
      let lhs_type = check_expr env lhs in
      let rhs_type = check_expr env rhs in
      ensure_int "binary operator" lhs_type;
      ensure_int "binary operator" rhs_type;
      Ast.TInt
  | Ast.Var name ->
      ignore (find_binding_exn env name);
      Ast.TInt
  | Ast.Call (name, args) -> (
      match StringMap.find_opt name env.funcs with
      | None ->
          Diagnostic.fail
            (Printf.sprintf "function used before declaration: %s" name)
      | Some sig_ ->
          if List.length args <> sig_.param_count then
            Diagnostic.fail
              (Printf.sprintf "function %s expects %d argument(s), got %d" name
                 sig_.param_count (List.length args));
          List.iter
            (fun arg ->
              let typ = check_expr env arg in
              ensure_int "function argument" typ)
            args;
          sig_.return_type)

let check_decl env = function
  | Ast.ConstDecl (name, value) ->
      let const_value = eval_const_expr env value in
      let env = declare_local env name { mutable_ = false; const_value = Some const_value } in
      env
  | Ast.VarDecl (name, init) ->
      Option.iter
        (fun expr -> ensure_int "declaration initializer" (check_expr env expr))
        init;
      declare_local env name { mutable_ = true; const_value = None }

let rec early_static_expr = function
  | Ast.Int value -> Some (i32 value)
  | Ast.Var _ | Ast.Call _ -> None
  | Ast.Unary (op, expr) -> Option.map (apply_unop op) (early_static_expr expr)
  | Ast.Binary (Ast.LAnd, lhs, rhs) -> (
      match early_static_expr lhs with
      | Some 0 -> Some 0
      | Some _ -> Option.map (fun value -> bool_to_int (value <> 0)) (early_static_expr rhs)
      | None -> early_static_binop Ast.LAnd lhs rhs)
  | Ast.Binary (Ast.LOr, lhs, rhs) -> (
      match early_static_expr lhs with
      | Some 0 -> Option.map (fun value -> bool_to_int (value <> 0)) (early_static_expr rhs)
      | Some _ -> Some 1
      | None -> early_static_binop Ast.LOr lhs rhs)
  | Ast.Binary (op, lhs, rhs) -> early_static_binop op lhs rhs

and early_static_binop op lhs rhs =
  match (early_static_expr lhs, early_static_expr rhs) with
  | _, Some 0 when op = Ast.Div || op = Ast.Mod -> None
  | Some lhs, Some rhs -> Some (apply_binop op lhs rhs)
  | _ -> None

let early_const_truth expr =
  Option.map (fun value -> value <> 0) (early_static_expr expr)
let rec check_stmt return_type env = function
  | Ast.Block body ->
      let block_env = enter_scope env in
      let block_env = List.fold_left (check_stmt return_type) block_env body in
      leave_scope block_env
  | Ast.Empty -> env
  | Ast.DeclStmt decls -> List.fold_left check_decl env decls
  | Ast.Assign (name, value) ->
      let binding = find_binding_exn env name in
      if not binding.mutable_ then
        Diagnostic.fail (Printf.sprintf "cannot assign to const: %s" name);
      ensure_int "assignment" (check_expr env value);
      env
  | Ast.ExprStmt expr ->
      ignore (check_expr env expr);
      env
  | Ast.If (cond, then_branch, None) ->
      ensure_int "if condition" (check_expr env cond);
      check_stmt return_type env then_branch
  | Ast.If (cond, then_branch, Some else_branch) ->
      ensure_int "if condition" (check_expr env cond);
      begin
        match early_const_truth cond with
        | Some true -> check_stmt return_type env then_branch
        | Some false -> check_stmt return_type env else_branch
        | None ->
            ignore (check_stmt return_type env then_branch);
            ignore (check_stmt return_type env else_branch);
            env
      end
  | Ast.While (cond, body) ->
      ensure_int "while condition" (check_expr env cond);
      ignore (check_stmt return_type { env with in_loop = true } body);
      env
  | Ast.Break ->
      if not env.in_loop then Diagnostic.fail "break outside loop";
      env
  | Ast.Continue ->
      if not env.in_loop then Diagnostic.fail "continue outside loop";
      env
  | Ast.Return value -> (
      match (return_type, value) with
      | Ast.TInt, Some expr ->
          ensure_int "return" (check_expr env expr);
          env
      | Ast.TInt, None -> Diagnostic.fail "int function must return a value"
      | Ast.TVoid, Some _ -> Diagnostic.fail "void function must not return a value"
      | Ast.TVoid, None -> env)

let rec eval_static_expr = function
  | Ast.Int value -> Some value
  | Ast.Var _ | Ast.Call _ -> None
  | Ast.Unary (op, expr) -> Option.map (apply_unop op) (eval_static_expr expr)
  | Ast.Binary (Ast.LAnd, lhs, rhs) -> (
      match eval_static_expr lhs with
      | Some 0 -> Some 0
      | Some _ -> Option.map (fun value -> bool_to_int (value <> 0)) (eval_static_expr rhs)
      | None -> eval_static_binop Ast.LAnd lhs rhs)
  | Ast.Binary (Ast.LOr, lhs, rhs) -> (
      match eval_static_expr lhs with
      | Some 0 -> Option.map (fun value -> bool_to_int (value <> 0)) (eval_static_expr rhs)
      | Some _ -> Some 1
      | None -> eval_static_binop Ast.LOr lhs rhs)
  | Ast.Binary (op, lhs, rhs) -> eval_static_binop op lhs rhs

and eval_static_binop op lhs rhs =
  match (eval_static_expr lhs, eval_static_expr rhs) with
  | _, Some 0 when op = Ast.Div || op = Ast.Mod -> None
  | Some lhs, Some rhs -> Some (apply_binop op lhs rhs)
  | _ -> None

let const_truth expr =
  Option.map (fun value -> value <> 0) (eval_static_expr expr)

let option_map_default option ~default ~f =
  match option with
  | Some value -> f value
  | None -> default

let rec stmt_must_return = function
  | Ast.Return _ -> true
  | Ast.Block body -> block_must_return body
  | Ast.If (cond, then_branch, else_branch) -> (
      match early_const_truth cond with
      | Some true -> stmt_must_return then_branch
      | Some false ->
          option_map_default else_branch ~default:false ~f:stmt_must_return
      | None -> (
          match else_branch with
          | Some else_branch ->
              stmt_must_return then_branch && stmt_must_return else_branch
          | None -> false))
  | Ast.While (cond, body) -> (
      match early_const_truth cond with
      | Some false -> false
      | Some true ->
          let body_breaks = stmt_may_break body in
          stmt_must_return body && not body_breaks
      | None -> false)
  | Ast.Empty | Ast.DeclStmt _ | Ast.Assign _ | Ast.ExprStmt _ | Ast.Break
  | Ast.Continue ->
      false

and block_must_return body =
  match body with
  | [] -> false
  | stmt :: rest ->
      stmt_must_return stmt
      || (stmt_may_fallthrough stmt && block_must_return rest)

and stmt_may_fallthrough = function
  | Ast.Return _ | Ast.Break | Ast.Continue -> false
  | Ast.Empty | Ast.DeclStmt _ | Ast.Assign _ | Ast.ExprStmt _ -> true
  | Ast.Block body -> block_may_fallthrough body
  | Ast.If (cond, then_branch, else_branch) -> (
      match early_const_truth cond with
      | Some true -> stmt_may_fallthrough then_branch
      | Some false ->
          option_map_default else_branch ~default:true ~f:stmt_may_fallthrough
      | None -> (
          match else_branch with
          | Some else_branch ->
              stmt_may_fallthrough then_branch
              || stmt_may_fallthrough else_branch
          | None -> true))
  | Ast.While (cond, body) -> (
      match early_const_truth cond with
      | Some false -> true
      | Some true -> stmt_may_break body
      | None -> true)

and block_may_fallthrough body =
  match body with
  | [] -> true
  | stmt :: rest ->
      if stmt_may_fallthrough stmt then block_may_fallthrough rest else false

and stmt_may_break = function
  | Ast.Break -> true
  | Ast.Return _ | Ast.Continue | Ast.Empty | Ast.DeclStmt _ | Ast.Assign _
  | Ast.ExprStmt _ ->
      false
  | Ast.Block body -> block_may_break body
  | Ast.If (cond, then_branch, else_branch) -> (
      match early_const_truth cond with
      | Some true -> stmt_may_break then_branch
      | Some false ->
          option_map_default else_branch ~default:false ~f:stmt_may_break
      | None -> (
          match else_branch with
          | Some else_branch ->
              stmt_may_break then_branch || stmt_may_break else_branch
          | None -> stmt_may_break then_branch))
  | Ast.While _ -> false

and block_may_break body =
  match body with
  | [] -> false
  | stmt :: rest ->
      stmt_may_break stmt
      || (stmt_may_fallthrough stmt && block_may_break rest)

let add_param env param =
  match param.Ast.param_type with
  | Ast.TInt ->
      declare_local env param.param_name { mutable_ = true; const_value = None }
  | Ast.TVoid ->
      Diagnostic.fail
        (Printf.sprintf "parameter cannot have void type: %s" param.param_name)

let check_func top_env self_sig func =
  let funcs = StringMap.add func.Ast.name self_sig top_env.declared_funcs in
  let env = empty_env funcs top_env.declared_globals in
  let env = List.fold_left add_param env func.Ast.params in
  ignore (List.fold_left (check_stmt func.return_type) env func.body);
  match func.return_type with
  | Ast.TInt ->
      if not (block_must_return func.body) then
        Diagnostic.fail
          (Printf.sprintf "int function must return a value: %s" func.name)
  | Ast.TVoid -> ()

let check_global_decl top_env = function
  | Ast.ConstDecl (name, value) ->
      let env = empty_env top_env.declared_funcs top_env.declared_globals in
      let const_value = eval_const_expr env value in
      StringMap.add name { mutable_ = false; const_value = Some const_value }
        top_env.declared_globals
  | Ast.VarDecl (name, init) ->
      let env = empty_env top_env.declared_funcs top_env.declared_globals in
      Option.iter
        (fun expr -> ensure_int "global initializer" (check_expr env expr))
        init;
      StringMap.add name { mutable_ = true; const_value = None }
        top_env.declared_globals

let collect_program program =
  let funcs = ref StringMap.empty in
  let globals = ref StringSet.empty in
  let seen = ref StringSet.empty in
  let add_name name =
    if StringSet.mem name !seen then
      Diagnostic.fail (Printf.sprintf "duplicate top-level name: %s" name);
    seen := StringSet.add name !seen
  in
  List.iter
    (function
      | Ast.GlobalDecl decls ->
          List.iter
            (function
              | Ast.ConstDecl (name, _) | Ast.VarDecl (name, _) ->
                  add_name name;
                  globals := StringSet.add name !globals)
            decls
      | Ast.FuncDef func ->
          add_name func.name;
          funcs :=
            StringMap.add func.name
              { return_type = func.return_type; param_count = List.length func.params }
              !funcs)
    program;
  (!funcs, !globals)

let check_program (program : Ast.program) =
  let funcs, _ = collect_program program in
  let main_sig =
    match StringMap.find_opt "main" funcs with
    | None -> Diagnostic.fail "program must define main"
    | Some sig_ -> sig_
  in
  if main_sig.return_type <> Ast.TInt || main_sig.param_count <> 0 then
    Diagnostic.fail "main must have type int main()";
  let _ =
    List.fold_left
      (fun top_env item ->
        match item with
        | Ast.GlobalDecl decls ->
            let declared_globals =
              List.fold_left
                (fun declared_globals decl ->
                  check_global_decl { top_env with declared_globals } decl)
                top_env.declared_globals decls
            in
            { top_env with declared_globals }
        | Ast.FuncDef func ->
            let self_sig =
              match StringMap.find_opt func.Ast.name funcs with
              | Some sig_ -> sig_
              | None ->
                  Diagnostic.fail
                    (Printf.sprintf "internal error: missing signature for %s"
                       func.Ast.name)
            in
            check_func top_env self_sig func;
            {
              top_env with
              declared_funcs = StringMap.add func.Ast.name self_sig top_env.declared_funcs;
            })
      empty_top_level_env program
  in
  program
