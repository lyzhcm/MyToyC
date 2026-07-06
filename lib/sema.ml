module StringMap = Symbol.StringMap
module StringSet = Set.Make (String)

type func_sig = {
  return_type : Ast.typ;
  param_count : int;
}

type env = {
  globals : StringSet.t;
  funcs : func_sig StringMap.t;
  scopes : StringSet.t list;
  in_loop : bool;
}

let empty_env funcs globals =
  { funcs; globals; scopes = [ StringSet.empty ]; in_loop = false }

let enter_scope env =
  { env with scopes = StringSet.empty :: env.scopes }

let leave_scope env =
  match env.scopes with
  | _ :: rest -> { env with scopes = rest }
  | [] -> env

let current_scope (env : env) =
  match env.scopes with
  | scope :: _ -> scope
  | [] -> StringSet.empty

let replace_current_scope (env : env) scope =
  match env.scopes with
  | _ :: rest -> { env with scopes = scope :: rest }
  | [] -> { env with scopes = [ scope ] }

let declare_local (env : env) name =
  let scope = current_scope env in
  if StringSet.mem name scope then
    Diagnostic.fail (Printf.sprintf "duplicate variable: %s" name);
  replace_current_scope env (StringSet.add name scope)

let rec local_exists name = function
  | [] -> false
  | scope :: rest -> StringSet.mem name scope || local_exists name rest

let var_exists env name =
  local_exists name env.scopes || StringSet.mem name env.globals

let rec check_expr env = function
  | Ast.Int _ -> ()
  | Ast.Unary (_, expr) -> check_expr env expr
  | Ast.Binary (_, lhs, rhs) ->
      check_expr env lhs;
      check_expr env rhs
  | Ast.Var name ->
      if not (var_exists env name) then
        Diagnostic.fail (Printf.sprintf "undefined variable: %s" name)
  | Ast.Call (name, args) -> (
      match StringMap.find_opt name env.funcs with
      | None -> Diagnostic.fail (Printf.sprintf "undefined function: %s" name)
      | Some sig_ ->
          if List.length args <> sig_.param_count then
            Diagnostic.fail
              (Printf.sprintf "function %s expects %d argument(s), got %d" name
                 sig_.param_count (List.length args));
          List.iter (check_expr env) args)

let check_decl env = function
  | Ast.ConstDecl (name, value) ->
      check_expr env value;
      declare_local env name
  | Ast.VarDecl (name, init) ->
      Option.iter (check_expr env) init;
      declare_local env name

let rec check_stmt return_type env = function
  | Ast.Block body ->
      let block_env = enter_scope env in
      let block_env = List.fold_left (check_stmt return_type) block_env body in
      leave_scope block_env
  | Ast.Empty -> env
  | Ast.DeclStmt decl -> check_decl env decl
  | Ast.Assign (name, value) ->
      if not (var_exists env name) then
        Diagnostic.fail (Printf.sprintf "undefined variable: %s" name);
      check_expr env value;
      env
  | Ast.ExprStmt expr ->
      check_expr env expr;
      env
  | Ast.If (cond, then_branch, else_branch) ->
      check_expr env cond;
      ignore (check_stmt return_type (enter_scope env) then_branch);
      Option.iter
        (fun stmt -> ignore (check_stmt return_type (enter_scope env) stmt))
        else_branch;
      env
  | Ast.While (cond, body) ->
      check_expr env cond;
      ignore
        (check_stmt return_type (enter_scope { env with in_loop = true }) body);
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
          check_expr env expr;
          env
      | Ast.TInt, None -> Diagnostic.fail "int function must return a value"
      | Ast.TVoid, Some _ -> Diagnostic.fail "void function must not return a value"
      | Ast.TVoid, None -> env)

let rec stmt_has_return = function
  | Ast.Return _ -> true
  | Ast.Block body -> List.exists stmt_has_return body
  | Ast.If (_, then_branch, Some else_branch) ->
      stmt_has_return then_branch && stmt_has_return else_branch
  | _ -> false

let add_param env param =
  match param.Ast.param_type with
  | Ast.TInt -> declare_local env param.param_name
  | Ast.TVoid ->
      Diagnostic.fail
        (Printf.sprintf "parameter cannot have void type: %s" param.param_name)

let check_func funcs globals func =
  let env = empty_env funcs globals in
  let env = List.fold_left add_param env func.Ast.params in
  ignore (List.fold_left (check_stmt func.return_type) env func.body);
  match func.return_type with
  | Ast.TInt ->
      if not (List.exists stmt_has_return func.body) then
        Diagnostic.fail
          (Printf.sprintf "int function must return a value: %s" func.name)
  | Ast.TVoid -> ()

let collect_program program =
  let funcs = ref StringMap.empty in
  let globals = ref StringSet.empty in
  let add_name name =
    if StringMap.mem name !funcs || StringSet.mem name !globals then
      Diagnostic.fail (Printf.sprintf "duplicate top-level name: %s" name)
  in
  List.iter
    (function
      | Ast.GlobalDecl (Ast.ConstDecl (name, _) | Ast.VarDecl (name, _)) ->
          add_name name;
          globals := StringSet.add name !globals
      | Ast.FuncDef func ->
          add_name func.name;
          funcs :=
            StringMap.add func.name
              { return_type = func.return_type; param_count = List.length func.params }
              !funcs)
    program;
  (!funcs, !globals)

let check_global_decl funcs globals = function
  | Ast.ConstDecl (_, value) ->
      check_expr (empty_env funcs globals) value
  | Ast.VarDecl (_, init) ->
      Option.iter (check_expr (empty_env funcs globals)) init

let check_program (program : Ast.program) =
  let funcs, globals = collect_program program in
  if not (StringMap.mem "main" funcs) then Diagnostic.fail "program must define main";
  List.iter
    (function
      | Ast.GlobalDecl decl -> check_global_decl funcs globals decl
      | Ast.FuncDef func -> check_func funcs globals func)
    program;
  program
