let tokenize = Ocaml_lite.Lexer.tokenize
let parse = Ocaml_lite.Parser.parse
let typecheck = Ocaml_lite.Typechecker.typecheck
let interpret = Ocaml_lite.Interpreter.interpret

let () =
  if Array.length Sys.argv <> 2
  then failwith "Expected exactly one command line argument"
  else
    let ch = In_channel.open_text Sys.argv.(1) in
    let text = In_channel.input_all ch in
    let () = In_channel.close ch in
    let token_list = tokenize text in
    let ast = parse token_list in
    let _ = typecheck ast in
    let _ = interpret ast in ()
