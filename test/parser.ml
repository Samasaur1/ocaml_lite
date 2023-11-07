open OUnit2
open Ocaml_lite.Lexer
open Ocaml_lite.Ast
open Ocaml_lite.Parser

let parse_tests = "parser tests" >::: [
  "basic single binding" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, IntLiteralExpr (1))]))
    (parse (tokenize "let x = 1;;"))
  ~printer:(string_of_program 0));
  "two bindings" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, IntLiteralExpr (1)); NonRecursiveBinding ("y", [], None, IntLiteralExpr (2))]))
    (parse (tokenize "let x = 1;;\nlet y = 2;;"))
  ~printer:(string_of_program 0));
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
    (parse (tokenize "let x = 1 + 1 + 1;;"))
  ~printer:(string_of_program 0));
  "overriding plus associativity" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (IntLiteralExpr (1), Plus, BinopExpr (IntLiteralExpr (1), Plus, IntLiteralExpr (1))))]))
    (parse (tokenize "let x = 1 + (1+1);;"))
  ~printer:(string_of_program 0));
  "times associativity" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (BinopExpr (IntLiteralExpr (1), Times, IntLiteralExpr (1)), Times, IntLiteralExpr (1)))]))
    (parse (tokenize "let x = 1 * 1 * 1;;"))
  ~printer:(string_of_program 0));
  "overriding times associativity" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (IntLiteralExpr (1), Times, BinopExpr (IntLiteralExpr (1), Times, IntLiteralExpr (1))))]))
    (parse (tokenize "let x = 1 * (1*1);;"))
  ~printer:(string_of_program 0));
  "plus and times associativity (1)" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (IntLiteralExpr (1), Plus, BinopExpr (IntLiteralExpr (2), Times, IntLiteralExpr (3))))]))
    (parse (tokenize "let x = 1 + 2 * 3;;"))
  ~printer:(string_of_program 0));
  "plus and times associativity (2)" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (BinopExpr (IntLiteralExpr (1), Times, IntLiteralExpr (2)), Plus, IntLiteralExpr (3)))]))
    (parse (tokenize "let x = 1 * 2 + 3;;"))
  ~printer:(string_of_program 0));
  "single member type definition" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("Constructor", None)])]))
    (parse (tokenize "type t =\n  | Constructor;;"))
  ~printer:(string_of_program 0));
  "single member with value type definition" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some (IntType))])]))
    (parse (tokenize "type t =\n  | A of int;;"))
  ~printer:(string_of_program 0));
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
    (parse (tokenize "type t =\n  | A\n  |B;;"))
  ~printer:(string_of_program 0));
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
    (parse (tokenize "type t =\n  | A of bool\n\t|B;;"))
  ~printer:(string_of_program 0));
  "identity function" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("id", [UntypedParam "x"], None, VarExpr "x")]))
    (parse (tokenize "let id x = x;;"))
  ~printer:(string_of_program 0));
  "integer square function" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("square", [TypedParam ("x", IntType)], Some (IntType), BinopExpr (VarExpr "x", Times, VarExpr "x"))]))
    (parse (tokenize "let square (x: int): int = x * x;;"))
  ~printer:(string_of_program 0));
  "type cross type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(TupleType [UnitType; StringType;]))])]))
    (parse (tokenize "type t = | A of unit * string;;"))
  ~printer:(string_of_program 0));
  "type -> type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(FunctionType (UserDeclaredType "f", UserDeclaredType "g")))])]))
    (parse (tokenize "type t = | A of f -> g;;"))
  ~printer:(string_of_program 0));
  "type cross type cross type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(TupleType [UnitType; StringType; BoolType;]))])]))
    (parse (tokenize "type t = | A of unit * string * bool;;"))
  ~printer:(string_of_program 0));
  "type cross (type cross type)" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(TupleType [UnitType; TupleType [StringType; BoolType;];]))])]))
    (parse (tokenize "type t = | A of unit * (string * bool);;"))
  ~printer:(string_of_program 0));
  "(type cross type) cross type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(TupleType [TupleType [UnitType; StringType;]; BoolType;]))])]))
    (parse (tokenize "type t = | A of (unit * string) * bool;;"))
  ~printer:(string_of_program 0));
  "match with one variable case" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, MatchExpr (VarExpr "y", [MatchBranch ("z", None, IntLiteralExpr 0)]))]))
    (parse (tokenize "let x = match y with | z => 0;;"))
  ~printer:(string_of_program 0));
  "match without vertical bar" >::
  (fun _ -> try
    let _ = parse (tokenize "let x = match y with z => 0;;") in
      assert_failure "parsed match branch without bar"
    with
    | ParseError _ -> assert_bool "" true
    | _ -> assert_failure "Unexpected error");
  "match with wrong arrow" >::
  (fun _ -> try
    let _ = parse (tokenize "let x = match y with | z -> 0;;") in
      assert_failure "parsed match branch with wrong arrow"
    with
    | ParseError _ -> assert_bool "" true
    | _ -> assert_failure "Unexpected error");
  "match with two variable cases" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, MatchExpr (VarExpr "y", [MatchBranch ("z", None, IntLiteralExpr 0); MatchBranch ("a", None, IntLiteralExpr 1)]))]))
    (parse (tokenize "let x = match y with | z => 0 | a => 1;;"))
  ~printer:(string_of_program 0));
  "match with one case with multiple pattern vars" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, MatchExpr (VarExpr "y", [MatchBranch ("z", Some(MultiplePatternVars ["a"; "b";]), IntLiteralExpr 0)]))]))
    (parse (tokenize "let x = match y with | z (a, b) => 0;;"))
  ~printer:(string_of_program 0));
]
