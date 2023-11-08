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
  "let-in" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, LetExpr ("y", [], None, IntLiteralExpr 1, BinopExpr (VarExpr "y", Plus, IntLiteralExpr 2)))]))
    (parse (tokenize "let x = let y = 1 in y + 2;;"))
  ~printer:(string_of_program 0));
  "let-in with vars" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, LetExpr ("y", [UntypedParam "z"], None, BinopExpr (VarExpr "z", Plus, IntLiteralExpr 1), FunAppExpr (VarExpr "y", IntLiteralExpr 2)))]))
    (parse (tokenize "let x = let y z = z + 1 in y 2;;"))
  ~printer:(string_of_program 0));
  "let-rec-in" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, LetRecExpr ("y", [], None, IntLiteralExpr 1, BinopExpr (VarExpr "y", Plus, IntLiteralExpr 2)))]))
    (parse (tokenize "let x = let rec y = 1 in y + 2;;"))
  ~printer:(string_of_program 0));
  "if-then-else" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, IfExpr (BinopExpr (IntLiteralExpr 0, LessThan, IntLiteralExpr 1), IntLiteralExpr 0, IntLiteralExpr 1))]))
    (parse (tokenize "let x = if 0 < 1 then 0 else 1;;"))
  ~printer:(string_of_program 0));
  "if-then-else (greedy consume)" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, IfExpr (BinopExpr (IntLiteralExpr 0, LessThan, IntLiteralExpr 1), IntLiteralExpr 0, BinopExpr (IntLiteralExpr 1, Times, IntLiteralExpr 2)))]))
    (parse (tokenize "let x = if 0 < 1 then 0 else 1 * 2;;"))
  ~printer:(string_of_program 0));
  "function literals" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, FunDefExpr ([UntypedParam "y"], None, BinopExpr (VarExpr "y", Times, VarExpr "y")))]))
    (parse (tokenize "let x = fun y => y * y;;"))
  ~printer:(string_of_program 0));
  "function literals (typed and untyped params)" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, FunDefExpr ([UntypedParam "y"; TypedParam ("z", IntType)], None, BinopExpr (VarExpr "y", Minus, VarExpr "z")))]))
    (parse (tokenize "let x = fun y (z: int) => y - z;;"))
  ~printer:(string_of_program 0));
  "function literal (fully typed)" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, FunDefExpr ([TypedParam ("a", IntType); UntypedParam "b"; TypedParam ("c", BoolType)], Some(StringType), IfExpr (VarExpr "c", (FunAppExpr (VarExpr "string_of_int", VarExpr "a")), VarExpr "b")))]))
    (parse (tokenize "let x = fun (a: int) b (c: bool): string => if c then string_of_int a else b;;"))
  ~printer:(string_of_program 0));
  "function application" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, FunAppExpr (VarExpr "string_of_int", IntLiteralExpr 2))]))
    (parse (tokenize "let x = string_of_int 2;;"))
  ~printer:(string_of_program 0));
  "tuple exprs" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, TupleExpr ([BoolLiteralExpr true; IntLiteralExpr 2; StringLiteralExpr "three"]))]))
    (parse (tokenize "let x = (true, 2, \"three\");;"))
  ~printer:(string_of_program 0));
  "type * type -> type * type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("T", Some (FunctionType (TupleType ([IntType; IntType]), TupleType ([IntType; IntType]))))])]))
    (parse (tokenize "type t = | T of int * int -> int * int;;"))
  ~printer:(string_of_program 0));
  "type -> type * type -> type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("T", Some (FunctionType (IntType, FunctionType (TupleType ([IntType; IntType]), IntType))))])]))
    (parse (tokenize "type t = | T of int -> int * int -> int;;"))
  ~printer:(string_of_program 0));
  "type -> type -> type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(FunctionType (UnitType, FunctionType (StringType, BoolType))))])]))
    (parse (tokenize "type t = | A of unit -> string -> bool;;"))
  ~printer:(string_of_program 0));
  "type -> (type -> type)" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(FunctionType (UnitType, FunctionType (StringType, BoolType))))])]))
    (parse (tokenize "type t = | A of unit -> (string -> bool);;"))
  ~printer:(string_of_program 0));
  "(type -> type) -> type" >::
  (fun _ -> assert_equal
    (Program ([TypeDefBinding ("t", [("A", Some(FunctionType (FunctionType (UnitType, StringType), BoolType)))])]))
    (parse (tokenize "type t = | A of (unit -> string) -> bool;;"))
  ~printer:(string_of_program 0));
  "overriding let associativity" >::
  (fun _ -> assert_equal
    (Program ([NonRecursiveBinding ("x", [], None, BinopExpr (LetExpr ("y", [], None, IntLiteralExpr 1, VarExpr "y"), Plus, IntLiteralExpr 2))]))
    (parse (tokenize "let x = (let y = 1 in y) + 2;;"))
  ~printer:(string_of_program 0));
  "basic single rec binding" >::
  (fun _ -> assert_equal
    (Program ([RecursiveBinding ("x", [], None, IntLiteralExpr (1))]))
    (parse (tokenize "let rec x = 1;;"))
  ~printer:(string_of_program 0));

  (* "example test" >::
  (fun _ -> assert_equal
    (Program ([]))
    (parse (tokenism "Example program"))
  ~printer:(string_of_program 0)); *)
]
