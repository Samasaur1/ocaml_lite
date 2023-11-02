open Ast
open Lexer

exception ParseError of string

let parse (_: token list): program =
  failwith "stub"
