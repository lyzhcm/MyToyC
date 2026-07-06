let truthy value = if value = 0 then 0 else 1

let rec eval_expr = function
  | Ast.Int value -> value
  | Ast.Unary (op, expr) ->
      let value = eval_expr expr in
      (match op with
      | Ast.Pos -> value
      | Ast.Neg -> -value
      | Ast.LNot -> if value = 0 then 1 else 0)
  | Ast.Binary (op, lhs, rhs) ->
      let left = eval_expr lhs in
      let right = eval_expr rhs in
      (match op with
      | Ast.Add -> left + right
      | Ast.Sub -> left - right
      | Ast.Mul -> left * right
      | Ast.Div ->
          if right = 0 then Diagnostic.fail "division by zero";
          left / right
      | Ast.Mod ->
          if right = 0 then Diagnostic.fail "modulo by zero";
          left mod right
      | Ast.Lt -> if left < right then 1 else 0
      | Ast.Gt -> if left > right then 1 else 0
      | Ast.Le -> if left <= right then 1 else 0
      | Ast.Ge -> if left >= right then 1 else 0
      | Ast.Eq -> if left = right then 1 else 0
      | Ast.Ne -> if left <> right then 1 else 0
      | Ast.LAnd -> if truthy left <> 0 && truthy right <> 0 then 1 else 0
      | Ast.LOr -> if truthy left <> 0 || truthy right <> 0 then 1 else 0)
  | Ast.Var name ->
      Diagnostic.fail
        (Printf.sprintf "unsupported variable expression in this stage: %s" name)
  | Ast.Call (name, _) ->
      Diagnostic.fail
        (Printf.sprintf "unsupported function call in this stage: %s" name)

let lower_stmt = function
  | Ast.Return None -> Ir.Return (Ir.Imm 0)
  | Ast.Return (Some expr) -> Ir.Return (Ir.Imm (eval_expr expr))

let lower_func func =
  { Ir.name = func.Ast.name; body = List.map lower_stmt func.body }

let lower_program (program : Ast.program) : Ir.program =
  List.map lower_func program
