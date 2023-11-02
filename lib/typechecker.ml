open Ast

exception TypecheckError of string

let typecheck (_: program): (string * typ) list =
  failwith "stub"
