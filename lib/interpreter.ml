open Ast

type value =
  | IntLiteral of int
  | StringLiteral of string
  | BoolLiteral of bool
  | IDontKnowYet

let interpret (_: program): value =
  failwith "stub"
