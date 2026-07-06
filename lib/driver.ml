let parse source =
  let lexbuf = Lexing.from_string source in
  Parser.program Lexer.token lexbuf

let compile ?(optimize = false) source =
  source
  |> parse
  |> Sema.check_program
  |> Irgen.lower_program
  |> Optimize.run ~enabled:optimize
  |> Codegen.emit_program

let read_stdin () =
  let buffer = Buffer.create 4096 in
  (try
     while true do
       Buffer.add_string buffer (input_line stdin);
       Buffer.add_char buffer '\n'
     done
   with End_of_file -> ());
  Buffer.contents buffer

let run () =
  match Array.to_list Sys.argv with
  | [_] ->
      let source = read_stdin () in
      print_string (compile source)
  | [_; "-opt"] ->
      let source = read_stdin () in
      print_string (compile ~optimize:true source)
  | _ ->
      Diagnostic.fail "usage: mytoyc [-opt] < input.tc > output.s"
