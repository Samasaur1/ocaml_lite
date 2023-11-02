open OUnit2
open Ocaml_lite.Lexer
open Ocaml_lite.Ast
open Ocaml_lite.Parser

let parse_tests = "parser tests" >::: [
  "basic single binding" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, IntLiteralExpr (1))]))
    (parse (tokenize "let x = 1;;")));
  "two bindings" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, IntLiteralExpr (1)); NonRecursiveBinding ("y", [], None, IntLiteralExpr (2))]))
    (parse (tokenize "let x = 1;;\nlet y = 2;;")));
  "no bindings" >::
  (fun _ -> try
    let _ = parse (tokenize "") in
      assert_failure "parsed an empty program"
    with
      | ParseError _ -> assert_bool "" true
      | _ -> assert_failure "Unexpected error");
  "single binding without semicolons" >::
  (fun _ -> try
    let _ = parse (tokenize "let x = 1") in
      assert_failure "parsed a program without semicolons"
    with
      | ParseError _ -> assert_bool "" true
      | _ -> assert_failure "Unexpected error");
  "plus associativity" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (BinopExpr (IntLiteralExpr (1), Plus, IntLiteralExpr (1)), Plus, IntLiteralExpr (1)))]))
    (parse (tokenize "let x = 1 + 1 + 1;;")));
  "overriding plus associativity" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (IntLiteralExpr (1), Plus, BinopExpr (IntLiteralExpr (1), Plus, IntLiteralExpr (1))))]))
    (parse (tokenize "let x = 1 + (1+1);;")));
  "times associativity" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (BinopExpr (IntLiteralExpr (1), Times, IntLiteralExpr (1)), Times, IntLiteralExpr (1)))]))
    (parse (tokenize "let x = 1 * 1 * 1;;")));
  "overriding times associativity" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (IntLiteralExpr (1), Times, BinopExpr (IntLiteralExpr (1), Times, IntLiteralExpr (1))))]))
    (parse (tokenize "let x = 1 * (1*1);;")));
  "plus and times associativity (1)" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (IntLiteralExpr (1), Plus, BinopExpr (IntLiteralExpr (2), Times, IntLiteralExpr (3))))]))
    (parse (tokenize "let x = 1 + 2 * 3;;")));
  "plus and times associativity (2)" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (BinopExpr (IntLiteralExpr (1), Times, IntLiteralExpr (2)), Plus, IntLiteralExpr (3)))]))
    (parse (tokenize "let x = 1 * 2 + 3;;")));
  "single member type definition" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("Constructor", None)])]))
    (parse (tokenize "type t =\n  | Constructor;;")));
  "single member with value type definition" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some (IntType))])]))
    (parse (tokenize "type t =\n  | A of int;;")));
  "type definition without constructors" >::
  (fun _ -> try
    let _ = parse (tokenize "type t;;") in
      assert_failure "parsed type definition without constructors"
    with
      | ParseError _ -> assert_bool "" true
      | _ -> assert_failure "Unexpected error");
  "double member type definition" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", None); ("B", None)])]))
    (parse (tokenize "type t =\n  | A\n  |B;;")));
  "single member type definition without bar" >::
  (fun _ -> try
    let _ = parse (tokenize "type t = A;;") in
      assert_failure "parsed type definition without bar"
    with
      | ParseError _ -> assert_bool "" true
      | _ -> assert_failure "Unexpected error");
  "double member type definition with single value" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(BoolType)); ("B", None)])]))
    (parse (tokenize "type t =\n  | A of bool\n\t|B;;")));
  "identity function" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("id", [UntypedParam "x"], None, VarExpr "x")]))
    (parse (tokenize "let id x = x;;")));
  "integer square function" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("square", [TypedParam ("x", IntType)], Some (IntType), BinopExpr (VarExpr "x", Times, VarExpr "x"))]))
    (parse (tokenize "let square (x: int): int = x * x;;")));
  "type cross type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(TupleType (UnitType, StringType)))])]))
    (parse (tokenize "type t = | A of unit * string;;")));
  "type -> type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(FunctionType (UserDeclaredType "f", UserDeclaredType "g")))])]))
    (parse (tokenize "type t = | A of f -> g;;")));
]