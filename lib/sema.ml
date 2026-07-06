let rec check_expr = function
  | Ast.Int _ -> ()
  | Ast.Unary (_, expr) -> check_expr expr
  | Ast.Binary (_, lhs, rhs) ->
      check_expr lhs;
      check_expr rhs
  | Ast.Var name ->
      Diagnostic.fail
        (Printf.sprintf "unsupported variable expression in this stage: %s" name)
  | Ast.Call (name, _) ->
      Diagnostic.fail
        (Printf.sprintf "unsupported function call in this stage: %s" name)

let check_stmt return_type = function
  | Ast.Return value -> (
      match (return_type, value) with
      | Ast.TInt, Some expr -> check_expr expr
      | Ast.TInt, None -> Diagnostic.fail "int function must return a value"
      | Ast.TVoid, Some _ -> Diagnostic.fail "void function must not return a value"
      | Ast.TVoid, None -> ())

let check_func func =
  List.iter (check_stmt func.Ast.return_type) func.body;
  match (func.Ast.return_type, func.body) with
  | Ast.TInt, [] ->
      Diagnostic.fail
        (Printf.sprintf "int function must return a value: %s" func.name)
  | _ -> ()

let check_program (program : Ast.program) =
  let seen = Hashtbl.create 16 in
  let has_main = ref false in
  List.iter
    (fun func ->
      if Hashtbl.mem seen func.Ast.name then
        Diagnostic.fail (Printf.sprintf "duplicate function: %s" func.name);
      Hashtbl.add seen func.name ();
      if func.name = "main" then has_main := true;
      check_func func)
    program;
  if not !has_main then Diagnostic.fail "program must define main";
  program
