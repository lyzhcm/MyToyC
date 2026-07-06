let run ~enabled (program : Ir.program) =
  if enabled then program else program
