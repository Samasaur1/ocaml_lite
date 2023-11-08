open OUnit2
(* open Util *)
open Ocaml_lite.Ast
open Ocaml_lite.Lexer
open Ocaml_lite.Parser

let parse (lst: token list): binding list =
  let Program (bds) = parse lst in
    bds

(* `type` statements *)

let test_empty _ =
  assert_equal (parse [ EOF ]) [];
  assert_equal (parse []) []

let test_simple_type_decl _ =
  assert_equal
    (parse (tokenize "type a = | b;;"))
    [ TypeDefBinding ("a", [ ("b", None) ]) ]

let test_empty_type_illegal _ =
  assert_raises (ParseError "Type list cannot be empty") (fun _ ->
      parse (tokenize "type a = ;;"))

let test_multiple_type_decl _ =
  assert_equal
    (parse (tokenize "type a = | b | c ;;"))
    [ TypeDefBinding ("a", [ ("b", None); ("c", None) ]) ]

let test_type_of_decl _ =
  assert_equal
    (parse (tokenize "type a = | b of int ;;"))
    [ TypeDefBinding ("a", [ ("b", Some IntType) ]) ]

let test_multiple_of_decl _ =
  assert_equal
    (parse (tokenize "type a = | b of string | c of int -> int ;;"))
    [ TypeDefBinding ("a", [ ("b", Some StringType); ("c", Some (FunctionType (IntType, IntType))) ]) ]

let test_mixed_ty_decl _ =
  assert_equal
    (parse (tokenize "type a = | b of int -> string | c | d | e of bool ;;"))
    [
      TypeDefBinding
        ( "a",
          [
            ("b", Some (FunctionType (IntType, StringType)));
            ("c", None);
            ("d", None);
            ("e", Some BoolType);
          ] );
    ]

(* Top-level `let` statements *)

let test_untyped_let _ =
  assert_equal
    (parse (tokenize "let a = () ;;"))
    [ NonRecursiveBinding ("a", [], None, UnitExpr) ];
  assert_equal
    (parse (tokenize "let rec a = () ;;"))
    [ RecursiveBinding ("a", [], None, UnitExpr) ]

let test_typed_let_val _ =
  assert_equal
    (parse (tokenize "let a : unit = () ;;"))
    [ NonRecursiveBinding ("a", [], Some UnitType, UnitExpr) ];
  assert_equal
    (parse (tokenize "let rec a : unit = () ;;"))
    [ RecursiveBinding ("a", [], Some UnitType, UnitExpr) ]

let test_let_untyped_param _ =
  assert_equal
    (parse (tokenize "let a b = () ;;"))
    [ NonRecursiveBinding ("a", [ UntypedParam "b" ], None, UnitExpr) ];
  assert_equal
    (parse (tokenize "let rec a b = () ;;"))
    [ RecursiveBinding ("a", [ UntypedParam "b" ], None, UnitExpr) ]

let test_let_typed_param _ =
  assert_equal
    (parse (tokenize "let a (b : int) = () ;;"))
    [ NonRecursiveBinding ("a", [ TypedParam ("b", IntType) ], None, UnitExpr) ];
  assert_equal
    (parse (tokenize "let rec a (b : int) = () ;;"))
    [ RecursiveBinding ("a", [ TypedParam ("b", IntType) ], None, UnitExpr) ]

let test_let_unty_params _ =
  assert_equal
    (parse (tokenize "let a b c = () ;;"))
    [ NonRecursiveBinding ("a", [ UntypedParam "b"; UntypedParam "c" ], None, UnitExpr) ];
  assert_equal
    (parse (tokenize "let rec a b c = () ;;"))
    [ RecursiveBinding ("a", [ UntypedParam "b"; UntypedParam "c" ], None, UnitExpr) ]

let test_let_ty_params _ =
  assert_equal
    (parse (tokenize "let a (b : int -> unit) (c : string) = () ;;"))
    [
      NonRecursiveBinding
          ( "a",
          [ TypedParam ("b", FunctionType (IntType, UnitType)); TypedParam ("c", StringType) ],
          None,
          UnitExpr );
    ];
  assert_equal
    (parse (tokenize "let rec a (b : int -> unit) (c : string) = () ;;"))
    [
      RecursiveBinding
        ( "a",
          [ TypedParam ("b", FunctionType (IntType, UnitType)); TypedParam ("c", StringType) ],
          None,
          UnitExpr );
    ]

let test_let_complex_params _ =
  assert_equal
    (parse (tokenize "let a (b : int * string) c d (e : bool) = () ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [
            TypedParam ("b", TupleType [ IntType; StringType ]);
            UntypedParam "c";
            UntypedParam "d";
            TypedParam ("e", BoolType);
          ],
          None,
          UnitExpr );
    ];
  assert_equal
    (parse (tokenize "let rec a (b : int * string) c d (e : bool) = () ;;"))
    [
      RecursiveBinding
        ( "a",
          [
            TypedParam ("b", TupleType [ IntType; StringType ]);
            UntypedParam "c";
            UntypedParam "d";
            TypedParam ("e", BoolType);
          ],
          None,
          UnitExpr );
    ]

let test_let_complex _ =
  assert_equal
    (parse
       (tokenize
          "let a b (c : (int * string) -> unit) d (e : unit) : int -> string = () ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [
            UntypedParam "b";
            TypedParam ("c", FunctionType (TupleType [ IntType; StringType ], UnitType));
            UntypedParam "d";
            TypedParam ("e", UnitType);
          ],
          Some (FunctionType (IntType, StringType)),
          UnitExpr );
    ];
  assert_equal
    (parse
       (tokenize
          "let rec a b (c : (int * string) -> unit) d (e : unit) : int -> string = () ;;"))
    [
      RecursiveBinding
        ( "a",
          [
            UntypedParam "b";
            TypedParam ("c", FunctionType (TupleType [ IntType; StringType ], UnitType));
            UntypedParam "d";
            TypedParam ("e", UnitType);
          ],
          Some (FunctionType (IntType, StringType)),
          UnitExpr );
    ]

let test_simple_let_in _ =
  assert_equal
    (parse (tokenize "let a = let b = c in d ;;"))
    [
      NonRecursiveBinding ("a", [], None, LetExpr ("b", [], None, VarExpr "c", VarExpr "d"));
    ];
  assert_equal
    (parse (tokenize "let a = let rec b = c in d ;;"))
    [
      NonRecursiveBinding ("a", [], None, LetRecExpr ("b", [], None, VarExpr "c", VarExpr "d"));
    ]

let test_typed_let_in_val _ =
  assert_equal
    (parse (tokenize "let a = let b : unit = () in c ;;"))
    [
      Let
        (false, "a", [], None, LetExpr ("b", [], Some UnitType, UnitExpr, VarExpr "c"));
    ];
  assert_equal
    (parse (tokenize "let a = let rec b : unit = () in c ;;"))
    [
      Let
        (false, "a", [], None, LetRecExpr ("b", [], Some UnitType, UnitExpr, VarExpr "c"));
    ]

let test_let_in_untyped_param _ =
  assert_equal
    (parse (tokenize "let a = let b c = () in d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetExpr ("b", [ UntypedParam "c" ], None, UnitExpr, VarExpr "d") );
    ];
  assert_equal
    (parse (tokenize "let a = let rec b c = () in d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetRecExpr ("b", [ UntypedParam "c" ], None, UnitExpr, VarExpr "d") );
    ]

let test_let_in_typed_param _ =
  assert_equal
    (parse (tokenize "let a = let b (c : int) = () in d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetExpr ("b", [ TypedParam ("c", IntType) ], None, UnitExpr, VarExpr "d") );
    ];
  assert_equal
    (parse (tokenize "let a = let rec b (c : int) = () in d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetRecExpr ("b", [ TypedParam ("c", IntType) ], None, UnitExpr, VarExpr "d") );
    ]

let test_let_in_unty_params _ =
  assert_equal
    (parse (tokenize "let a = let b c d = () in e ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetExpr ("b", [ UntypedParam "c"; UntypedParam "d" ], None, UnitExpr, VarExpr "e")
        );
    ];
  assert_equal
    (parse (tokenize "let a = let rec b c d = () in e ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetRecExpr ("b", [ UntypedParam "c"; UntypedParam "d" ], None, UnitExpr, VarExpr "e")
        );
    ]

let test_let_in_ty_params _ =
  assert_equal
    (parse
       (tokenize "let a = let b (c : int) (d : string -> bool) = () in e ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetIn
            ( false,
              "b",
              [ TypedParam ("c", IntType); ("d", Some (FunctionType (StringType, BoolType))) ],
              None,
              UnitExpr,
              VarExpr "e" ) );
    ];
  assert_equal
    (parse
       (tokenize "let a = let rec b (c : int) (d : string -> bool) = () in e ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetIn
            ( true,
              "b",
              [ TypedParam ("c", IntType); ("d", Some (FunctionType (StringType, BoolType))) ],
              None,
              UnitExpr,
              VarExpr "e" ) );
    ]

let test_let_in_complex_params _ =
  assert_equal
    (parse
       (tokenize "let a = let b (c : string) d e (f : unit * bool) = () in g ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetIn
            ( false,
              "b",
              [
                TypedParam ("c", StringType);
                UntypedParam "d";
                UntypedParam "e";
                ("f", Some (TupleType [ UnitType; BoolType ]));
              ],
              None,
              UnitExpr,
              VarExpr "g" ) );
    ];
  assert_equal
    (parse
       (tokenize
          "let a = let rec b (c : string) d e (f : unit * bool) = () in g ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetIn
            ( true,
              "b",
              [
                TypedParam ("c", StringType);
                UntypedParam "d";
                UntypedParam "e";
                ("f", Some (TupleType [ UnitType; BoolType ]));
              ],
              None,
              UnitExpr,
              VarExpr "g" ) );
    ]

let test_let_in_complex _ =
  assert_equal
    (parse
       (tokenize
          "let a = let b (c : int * bool) d (e : unit -> unit) f : string = () in g ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetIn
            ( false,
              "b",
              [
                ("c", Some (TupleType [ IntType; BoolType ]));
                UntypedParam "d";
                ("e", Some (FunctionType (UnitType, UnitType)));
                UntypedParam "f";
              ],
              Some StringType,
              UnitExpr,
              VarExpr "g" ) );
    ];
  assert_equal
    (parse
       (tokenize
          "let a = let rec b (c : int * bool) d (e : unit -> unit) f : string = () in g ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetIn
            ( true,
              "b",
              [
                ("c", Some (TupleType [ IntType; BoolType ]));
                UntypedParam "d";
                ("e", Some (FunctionType (UnitType, UnitType)));
                UntypedParam "f";
              ],
              Some StringType,
              UnitExpr,
              VarExpr "g" ) );
    ]

let test_nested_let_in_param _ =
  assert_equal
    (parse (tokenize "let a = let b = let rec c = () in d in e ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetIn
            ( false,
              "b",
              [],
              None,
              LetRecExpr ("c", [], None, UnitExpr, VarExpr "d"),
              VarExpr "e" ) );
    ]

let test_nested_let_in_value _ =
  assert_equal
    (parse (tokenize "let a = let rec b = () in let c = () in d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          LetIn
            ( true,
              "b",
              [],
              None,
              UnitExpr,
              LetExpr ("c", [], None, UnitExpr, VarExpr "d") ) );
    ]

let test_simple_cond _ =
  assert_equal
    (parse (tokenize "let a = if b then c else d ;;"))
    [ NonRecursiveBinding ("a", [], None, IfExpr (VarExpr "b", VarExpr "c", VarExpr "d")) ]

let test_nested_if_cond _ =
  assert_equal
    (parse (tokenize "let a = if if b then c else d then e else f ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          IfExpr (IfExpr (VarExpr "b", VarExpr "c", VarExpr "d"), VarExpr "e", VarExpr "f") );
    ]

let test_nested_then_cond _ =
  assert_equal
    (parse (tokenize "let a = if b then if c then d else e else f ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          IfExpr (VarExpr "b", IfExpr (VarExpr "c", VarExpr "d", VarExpr "e"), VarExpr "f") );
    ]

let test_nested_else_cond _ =
  assert_equal
    (parse (tokenize "let a = if b then c else if d then e else f ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          IfExpr (VarExpr "b", VarExpr "c", IfExpr (VarExpr "d", VarExpr "e", VarExpr "f")) );
    ]

let test_super_nested_cond _ =
  assert_equal
    (parse
       (tokenize
          "let a = if if b then c else d then if e then f else g else if h then i else j ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          IfExpr
            ( IfExpr (VarExpr "b", VarExpr "c", VarExpr "d"),
              IfExpr (VarExpr "e", VarExpr "f", VarExpr "g"),
              IfExpr (VarExpr "h", VarExpr "i", VarExpr "j") ) );
    ]

(* Remember that nullary functions are illegal *)
let test_nullary_lambda _ =
  assert_raises (ParseError "'fun' cannot have empty parameter list") (fun () ->
      parse (tokenize "let a = fun => () ;;"))

let test_simple_lambda _ =
  assert_equal
    (parse (tokenize "let a = fun x => () ;;"))
    [ NonRecursiveBinding ("a", [], None, FunDefExpr ([ UntypedParam "x" ], None, UnitExpr)) ]

let test_typed_lambda _ =
  assert_equal
    (parse (tokenize "let a = fun x : unit => () ;;"))
    [ NonRecursiveBinding ("a", [], None, FunDefExpr ([ UntypedParam "x" ], Some UnitType, UnitExpr)) ]

let test_lambda_typed_param _ =
  assert_equal
    (parse (tokenize "let a = fun (x : int) => () ;;"))
    [ NonRecursiveBinding ("a", [], None, FunDefExpr ([ TypedParam ("x", IntType) ], None, UnitExpr)) ]

let test_lambda_unty_params _ =
  assert_equal
    (parse (tokenize "let a = fun x y z => () ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          FunDefExpr ([ UntypedParam "x"; UntypedParam "y"; UntypedParam "z" ], None, UnitExpr) );
    ]

let test_lambda_ty_params _ =
  assert_equal
    (parse (tokenize "let a = fun (x : int -> string) (y : bool) => () ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          Lambda
            ( [ ("x", Some (FunctionType (IntType, StringType))); TypedParam ("y", BoolType) ],
              None,
              UnitExpr ) );
    ]

let test_lambda_complex_params _ =
  assert_equal
    (parse (tokenize "let a = fun (w : int) x (y : bool * unit) z => () ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          Lambda
            ( [
                TypedParam ("w", IntType);
                UntypedParam "x";
                TypedParam ("y", TupleType [ BoolType; UnitType ]);
                UntypedParam "z";
              ],
              None,
              UnitExpr ) );
    ]

let test_lambda_complex _ =
  assert_equal
    (parse
       (tokenize
          "let a = fun w x (y : unit * unit) (z : int -> string) : unit => () ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          Lambda
            ( [
                UntypedParam "w";
                UntypedParam "x";
                TypedParam ("y", TupleType [ UnitType; UnitType ]);
                TypedParam ("z", FunctionType (IntType, StringType));
              ],
              Some UnitType,
              UnitExpr ) );
    ]

let test_lambda_nested _ =
  assert_equal
    (parse (tokenize "let a = fun x => fun y => () ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          FunDefExpr ([ UntypedParam "x" ], None, FunDefExpr ([ UntypedParam "y" ], None, UnitExpr))
        );
    ]

(* TODO: Expressions w/i funcall *)

let test_simple_funcall _ =
  assert_equal
    (parse (tokenize "let a = b c ;;"))
    [ NonRecursiveBinding ("a", [], None, FunAppExpr(VarExpr "b", VarExpr "c")) ]

let test_multiple_funcall _ =
  assert_equal
    (parse (tokenize "let a = b c d e ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          FunAppExpr(FunAppExpr(FunAppExpr(VarExpr "b", VarExpr "c"), VarExpr "d"), VarExpr "e") );
    ]

let test_nested_funcall _ =
  assert_equal
    (parse (tokenize "let a = (b c) (d e) ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          FunAppExpr(FunAppExpr(VarExpr "b", VarExpr "c"), FunAppExpr(VarExpr "d", VarExpr "e")) );
    ]

let test_funcall_fun _ =
  assert_equal
    (parse (tokenize "let a = (fun x => ()) y ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          FunAppExpr(FunDefExpr ([ UntypedParam "x" ], None, UnitExpr), VarExpr "y") );
    ]

let test_simple_tuple _ =
  assert_equal
    (parse (tokenize "let a = (b, c) ;;"))
    [ NonRecursiveBinding ("a", [], None, TupleExpr[ VarExpr "b"; VarExpr "c" ]) ]

let test_long_tuple _ =
  assert_equal
    (parse (tokenize "let a = (b, c, d, e, f, g) ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          TupleExpr[ VarExpr "b"; VarExpr "c"; VarExpr "d"; VarExpr "e"; VarExpr "f"; VarExpr "g" ] );
    ]

let test_nested_tuple _ =
  assert_equal
    (parse (tokenize "let a = ((b, c), d, ((e, f, g), h)) ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          TupleExpr
            [
              TupleExpr[ VarExpr "b"; VarExpr "c" ];
              VarExpr "d";
              TupleExpr[ TupleExpr[ VarExpr "e"; VarExpr "f"; VarExpr "g" ]; VarExpr "h" ];
            ] );
    ]

let test_tuple_funcall _ =
  assert_equal
    (parse (tokenize "let a = (b c, d) ;;"))
    [
      NonRecursiveBinding ("a", [], None, TupleExpr[ FunAppExpr(VarExpr "b", VarExpr "c"); VarExpr "d" ]);
    ]

let test_let_in_tuple _ =
  assert_equal
    (parse (tokenize "let a = (let b = () in c, let rec d = () in f) ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          TupleExpr
            [
              LetExpr ("b", [], None, UnitExpr, VarExpr "c");
              LetRecExpr ("d", [], None, UnitExpr, VarExpr "f");
            ] );
    ]

let test_lambda_tuple _ =
  assert_equal
    (parse (tokenize "let a = (fun x => (), fun y => y) ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          TupleExpr
            [
              FunDefExpr ([ UntypedParam "x" ], None, UnitExpr);
              FunDefExpr ([ UntypedParam "y" ], None, VarExpr "y");
            ] );
    ]

let test_tuple_in_paren _ =
  assert_equal
    (parse (tokenize "let a = ((b, c)) ;;"))
    [ NonRecursiveBinding ("a", [], None, TupleExpr[ VarExpr "b"; VarExpr "c" ]) ]

let test_basic_addition _ =
  assert_equal
    (parse (tokenize "let a = b + c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BPlus, VarExpr "b", VarExpr "c")) ]

let test_addition_assoc _ =
  assert_equal
    (parse (tokenize "let a = b + c + d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BPlus, BinopExpr (BPlus, VarExpr "b", VarExpr "c"), VarExpr "d") );
    ]

let test_basic_subtraction _ =
  assert_equal
    (parse (tokenize "let a = b - c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BMinus, VarExpr "b", VarExpr "c")) ]

let test_subtraction_assoc _ =
  assert_equal
    (parse (tokenize "let a = b - c - d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BMinus, BinopExpr (BMinus, VarExpr "b", VarExpr "c"), VarExpr "d") );
    ]

let test_mixed_add_sub _ =
  assert_equal
    (parse (tokenize "let a = b + c - d + e ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr
            ( BPlus,
              BinopExpr (BMinus, BinopExpr (BPlus, VarExpr "b", VarExpr "c"), VarExpr "d"),
              VarExpr "e" ) );
    ]

let test_basic_multiplication _ =
  assert_equal
    (parse (tokenize "let a = b * c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BTimes, VarExpr "b", VarExpr "c")) ]

let test_mult_assoc _ =
  assert_equal
    (parse (tokenize "let a = b * c * d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BTimes, BinopExpr (BTimes, VarExpr "b", VarExpr "c"), VarExpr "d") );
    ]

let test_basic_division _ =
  assert_equal
    (parse (tokenize "let a = b / c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BDiv, VarExpr "b", VarExpr "c")) ]

let test_mixed_mult_div _ =
  assert_equal
    (parse (tokenize "let a = b * c / d mod e ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr
            ( BMod,
              BinopExpr (BDiv, BinopExpr (BTimes, VarExpr "b", VarExpr "c"), VarExpr "d"),
              VarExpr "e" ) );
    ]

let test_div_assoc _ =
  assert_equal
    (parse (tokenize "let a = b / c / d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BDiv, BinopExpr (BDiv, VarExpr "b", VarExpr "c"), VarExpr "d") );
    ]

let test_basic_modulo _ =
  assert_equal
    (parse (tokenize "let a = b mod c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BMod, VarExpr "b", VarExpr "c")) ]

let test_mod_assoc _ =
  assert_equal
    (parse (tokenize "let a = b mod c mod d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BMod, BinopExpr (BMod, VarExpr "b", VarExpr "c"), VarExpr "d") );
    ]

let test_simple_uminus _ =
  assert_equal
    (parse (tokenize "let a = ~b ;;"))
    [ NonRecursiveBinding ("a", [], None, UnopExpr (UBitNot, VarExpr "b")) ]

let test_nested_uminus _ =
  assert_equal
    (parse (tokenize "let a = ~~b ;;"))
    [ NonRecursiveBinding ("a", [], None, UnopExpr (UBitNot, UnopExpr (UBitNot, VarExpr "b"))) ]

let test_uminus_funcall _ =
  assert_equal
    (parse (tokenize "let a = ~b c ;;"))
    [ NonRecursiveBinding ("a", [], None, UnopExpr (UBitNot, FunAppExpr(VarExpr "b", VarExpr "c"))) ]

let test_complex_arithmetic _ =
  assert_equal
    (parse (tokenize "let a = b * c + d mod e / ~f - g ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr
            ( BMinus,
              BinopExpr
                ( BPlus,
                  BinopExpr (BTimes, VarExpr "b", VarExpr "c"),
                  BinopExpr
                    ( BDiv,
                      BinopExpr (BMod, VarExpr "d", VarExpr "e"),
                      UnopExpr (UBitNot, VarExpr "f") ) ),
              VarExpr "g" ) );
    ]

let test_basic_lt _ =
  assert_equal
    (parse (tokenize "let a = b < c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BLessThan, VarExpr "b", VarExpr "c")) ]

let test_basic_eq _ =
  assert_equal
    (parse (tokenize "let a = b = c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BEquals, VarExpr "b", VarExpr "c")) ]

let test_basic_concat _ =
  assert_equal
    (parse (tokenize "let a = b ^ c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BConcat, VarExpr "b", VarExpr "c")) ]

let test_concat_assoc _ =
  assert_equal
    (parse (tokenize "let a = b ^ c ^ d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BConcat, BinopExpr (BConcat, VarExpr "b", VarExpr "c"), VarExpr "d") );
    ]

(* TODO: Mix < and = with &&, || *)

let test_basic_logand _ =
  assert_equal
    (parse (tokenize "let a = b && c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BLogAnd, VarExpr "b", VarExpr "c")) ]

let test_logand_assoc _ =
  assert_equal
    (parse (tokenize "let a = b && c && d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BLogAnd, BinopExpr (BLogAnd, VarExpr "b", VarExpr "c"), VarExpr "d") );
    ]

let test_basic_logor _ =
  assert_equal
    (parse (tokenize "let a = b || c ;;"))
    [ NonRecursiveBinding ("a", [], None, BinopExpr (BLogOr, VarExpr "b", VarExpr "c")) ]

let test_logor_assoc _ =
  assert_equal
    (parse (tokenize "let a = b || c || d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BLogOr, BinopExpr (BLogOr, VarExpr "b", VarExpr "c"), VarExpr "d") );
    ]

let test_bool_precedence _ =
  assert_equal
    (parse (tokenize "let a = b || c && d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BLogOr, VarExpr "b", BinopExpr (BLogAnd, VarExpr "c", VarExpr "d")) );
    ];
  assert_equal
    (parse (tokenize "let a = b && c || d ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BLogOr, BinopExpr (BLogAnd, VarExpr "b", VarExpr "c"), VarExpr "d") );
    ]

let test_simple_lognot _ =
  assert_equal
    (parse (tokenize "let a = not b ;;"))
    [ NonRecursiveBinding ("a", [], None, UnopExpr (ULogNot, VarExpr "b")) ]

let test_nested_lognot _ =
  assert_equal
    (parse (tokenize "let a = not not not b ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          UnopExpr (ULogNot, UnopExpr (ULogNot, UnopExpr (ULogNot, VarExpr "b"))) );
    ]

let test_lognot_precedence _ =
  assert_equal
    (parse (tokenize "let a = not b || not c ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BLogOr, UnopExpr (ULogNot, VarExpr "b"), UnopExpr (ULogNot, VarExpr "c")) );
    ];
  assert_equal
    (parse (tokenize "let a = not b && not c ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr (BLogAnd, UnopExpr (ULogNot, VarExpr "b"), UnopExpr (ULogNot, VarExpr "c")) );
    ]

(* NOTE: This is not valid OCaml syntax (where `not` is treated as a normal
   function), but it is valid according to the rules given for OCaml-lite. *)
let test_lognot_funcall _ =
  assert_equal
    (parse (tokenize "let a = not b c ;;"))
    [ NonRecursiveBinding ("a", [], None, UnopExpr (ULogNot, FunAppExpr(VarExpr "b", VarExpr "c"))) ]

let test_complex_log_ops _ =
  assert_equal
    (parse (tokenize "let a = b || not c && not d && e || f || g ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr
            ( BLogOr,
              BinopExpr
                ( BLogOr,
                  BinopExpr
                    ( BLogOr,
                      VarExpr "b",
                      BinopExpr
                        ( BLogAnd,
                          BinopExpr
                            ( BLogAnd,
                              UnopExpr (ULogNot, VarExpr "c"),
                              UnopExpr (ULogNot, VarExpr "d") ),
                          VarExpr "e" ) ),
                  VarExpr "f" ),
              VarExpr "g" ) );
    ]

let test_cmp_with_log _ =
  assert_equal
    (parse (tokenize "let a = b && c < d || e = f || g ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          BinopExpr
            ( BLogOr,
              BinopExpr
                ( BLogOr,
                  BinopExpr (BLogAnd, VarExpr "b", BinopExpr (BLessThan, VarExpr "c", VarExpr "d")),
                  BinopExpr (BEquals, VarExpr "e", VarExpr "f") ),
              VarExpr "g" ) );
    ]

let test_numbers _ =
  List.iter
    (fun x ->
      assert_equal
        (parse (tokenize ("let a = " ^ string_of_int x ^ " ;;")))
        [ NonRecursiveBinding ("a", [], None, IntLiteralExpr x) ])
    (range_inc 1 20)

let test_bools _ =
  List.iter
    (fun x ->
      assert_equal
        (parse (tokenize ("let a = " ^ string_of_bool x ^ " ;;")))
        [ NonRecursiveBinding ("a", [], None, BoolLiteralExpr x) ])
    [ true; false ]

let test_strings _ =
  assert_equal
    (parse (tokenize "let a = \"abc\" ;;"))
    [ NonRecursiveBinding ("a", [], None, StringLiteralExpr "abc") ]

let test_simple_match _ =
  assert_equal
    (parse (tokenize "let a = match b with | c => d ;;"))
    [ NonRecursiveBinding ("a", [], None, EMatch (VarExpr "b", [ ("c", None, VarExpr "d") ])) ]

let test_multiarm_match _ =
  assert_equal
    (parse (tokenize "let a = match b with | c => d | e => f ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          EMatch (VarExpr "b", [ ("c", None, VarExpr "d"); ("e", None, VarExpr "f") ]) );
    ]

let test_simple_match_pat _ =
  assert_equal
    (parse (tokenize "let a = match b with | c d => e ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          EMatch (VarExpr "b", [ ("c", Some (BarePat "d"), VarExpr "e") ]) );
    ]

let test_tuple_match_pat _ =
  assert_equal
    (parse (tokenize "let a = match b with | c (d, e) => f ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          EMatch (VarExpr "b", [ ("c", Some (TuplePat [ "d"; "e" ]), VarExpr "f") ]) );
    ]

let test_long_tuple_match _ =
  assert_equal
    (parse (tokenize "let a = match b with | c (d, e, f, g) => h ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          EMatch
            (VarExpr "b", [ ("c", Some (TuplePat [ "d"; "e"; "f"; "g" ]), VarExpr "h") ])
        );
    ]

let test_multi_tup_match _ =
  assert_equal
    (parse
       (tokenize "let a = match b with | c (d, e) => f | g (h, i, j) => k ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          EMatch
            ( VarExpr "b",
              [
                ("c", Some (TuplePat [ "d"; "e" ]), VarExpr "f");
                ("g", Some (TuplePat [ "h"; "i"; "j" ]), VarExpr "k");
              ] ) );
    ]

let test_complex_match_arms _ =
  assert_equal
    (parse
       (tokenize
          "let a = match b with | c (d, e, f) => g | h => i | j k => l | m => n ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          EMatch
            ( VarExpr "b",
              [
                ("c", Some (TuplePat [ "d"; "e"; "f" ]), VarExpr "g");
                ("h", None, VarExpr "i");
                ("j", Some (BarePat "k"), VarExpr "l");
                ("m", None, VarExpr "n");
              ] ) );
    ]

let test_nested_match_param _ =
  assert_equal
    (parse (tokenize "let a = match match b with | c => d with | e => f ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          EMatch
            ( EMatch (VarExpr "b", [ ("c", None, VarExpr "d") ]),
              [ ("e", None, VarExpr "f") ] ) );
    ]

let test_match_in_match_arm _ =
  assert_equal
    (parse
       (tokenize "let a = match b with | c => match d with | e => f | g => h ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          EMatch
            ( VarExpr "b",
              [
                ( "c",
                  None,
                  EMatch
                    (VarExpr "d", [ ("e", None, VarExpr "f"); ("g", None, VarExpr "h") ]) );
              ] ) );
    ]

let test_factorial _ =
  assert_equal
    (parse
       (tokenize
          "let rec fact n = if n = 0 || n = 1 then 1 else (fact (n - 1)) + (fact (n - 2)) ;;"))
    [
      RecursiveBinding
        ( "fact",
          [ UntypedParam "n" ],
          None,
          IfExpr
            ( BinopExpr
                ( BLogOr,
                  BinopExpr (BEquals, VarExpr "n", IntLiteralExpr 0),
                  BinopExpr (BEquals, VarExpr "n", IntLiteralExpr 1) ),
              IntLiteralExpr 1,
              BinopExpr
                ( BPlus,
                  FunAppExpr(VarExpr "fact", BinopExpr (BMinus, VarExpr "n", IntLiteralExpr 1)),
                  FunAppExpr(VarExpr "fact", BinopExpr (BMinus, VarExpr "n", IntLiteralExpr 2)) ) ) );
    ]

let test_list_len _ =
  assert_equal
    (parse
       (tokenize
          ("type int_list = | Nil | Val of int * int_list ;;\n"
         ^ "let rec len l = match l with | Nil => 0 | Val (_, rest) => 1 + len rest ;;"
          )))
    [
      TypeDefBinding
        ( "int_list",
          [ ("Nil", None); ("Val", Some (TupleType [ IntType; UserDeclaredType "int_list" ])) ]
        );
      RecursiveBinding
        ( "len",
          [ UntypedParam "l" ],
          None,
          EMatch
            ( VarExpr "l",
              [
                ("Nil", None, IntLiteralExpr 0);
                ( "Val",
                  Some (TuplePat [ "_"; "rest" ]),
                  BinopExpr (BPlus, IntLiteralExpr 1, FunAppExpr(VarExpr "len", VarExpr "rest")) );
              ] ) );
    ]

let test_nil_comment _ =
  assert_equal
    (parse (tokenize "let a = ((**)) ;;"))
    [ NonRecursiveBinding ("a", [], None, UnitExpr) ]

let test_parenthetopia _ =
  assert_equal
    (parse (tokenize "let a = (()((()()((()((())))())))()()) ;;"))
    (* (nil (nil nil ((nil nil) nil)) nil nil) *)
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          Funcall
            ( Funcall
                ( Funcall
                    ( UnitExpr,
                      Funcall
                        ( FunAppExpr(UnitExpr, UnitExpr),
                          FunAppExpr(FunAppExpr(UnitExpr, UnitExpr), UnitExpr) ) ),
                  UnitExpr ),
              UnitExpr ) );
    ]

let test_loss_expr _ =
  assert_equal
    (parse (tokenize "let a = match b with | c => d || e || f |_ => g ;;"))
    [
      NonRecursiveBinding
        ( "a",
          [],
          None,
          EMatch
            ( VarExpr "b",
              [
                ( "c",
                  None,
                  BinopExpr (BLogOr, BinopExpr (BLogOr, VarExpr "d", VarExpr "e"), VarExpr "f") );
                ("_", None, VarExpr "g");
              ] ) );
    ]

(* TODO: Cursed ideas *)
(* Over-parenthesized exprs (besides nil) *)
(* Horribly-nested match/if/let statements *)

let basic_types =
  [ (TNInt, IntType); (TNBool, BoolType); (TNString, StringType); (TNUnit, UnitType) ]

let basic_tys = List.map snd basic_types
let basic_tynames = List.map fst basic_types

let print_parse_ty_result : ty * token list -> string = function
  | t, [] -> ty_to_string t
  | _ -> "Token list was not empty"

let test_type_basic _ =
  assert_equal
    (parse_ty (tokenize "int"))
    (IntType, []) ~printer:print_parse_ty_result;
  assert_equal
    (parse_ty (tokenize "bool"))
    (BoolType, []) ~printer:print_parse_ty_result;
  assert_equal
    (parse_ty (tokenize "string"))
    (StringType, []) ~printer:print_parse_ty_result;
  assert_equal
    (parse_ty (tokenize "unit"))
    (UnitType, []) ~printer:print_parse_ty_result

let test_type_arrow _ =
  List.iter
    (fun ((tn, t), (un, u)) ->
      assert_equal
        (parse_ty [ tn; Arrow; un ])
        (FunctionType (t, u), [])
        ~printer:print_parse_ty_result)
    (cartesian basic_types basic_types)

let test_type_product _ =
  List.iter
    (fun ((tn, t), (un, u)) ->
      assert_equal
        (parse_ty [ tn; Times; un ])
        (TupleType [ t; u ], [])
        ~printer:print_parse_ty_result)
    (cartesian basic_types basic_types)

let test_associative_arrow _ =
  assert_equal
    (parse_ty (tokenize "a -> b -> c"))
    (FunctionType (UserDeclaredType "a", FunctionType (UserDeclaredType "b", UserDeclaredType "c")), [])
    ~printer:print_parse_ty_result

let test_associative_prod _ =
  assert_equal
    (parse_ty (tokenize "a * b * c"))
    (TupleType [ UserDeclaredType "a"; UserDeclaredType "b"; UserDeclaredType "c" ], [])
    ~printer:print_parse_ty_result

let test_type_precedence _ =
  assert_equal
    (parse_ty (tokenize "a -> b * c"))
    (FunctionType (UserDeclaredType "a", TupleType [ UserDeclaredType "b"; UserDeclaredType "c" ]), [])
    ~printer:print_parse_ty_result;
  assert_equal
    (parse_ty (tokenize "a * b -> c"))
    (FunctionType (TupleType [ UserDeclaredType "a"; UserDeclaredType "b" ], UserDeclaredType "c"), [])
    ~printer:print_parse_ty_result

let test_long_type_precedence _ =
  assert_equal
    (parse_ty (tokenize "a * b * c -> d * e -> f * g * h"))
    ( FunctionType
        ( TupleType [ UserDeclaredType "a"; UserDeclaredType "b"; UserDeclaredType "c" ],
          FunctionType
            ( TupleType [ UserDeclaredType "d"; UserDeclaredType "e" ],
              TupleType [ UserDeclaredType "f"; UserDeclaredType "g"; UserDeclaredType "h" ] ) ),
      [] )
    ~printer:print_parse_ty_result

let test_type_parens _ =
  assert_equal
    (parse_ty (tokenize "(a -> b) * (c -> d)"))
    (TupleType [ FunctionType (UserDeclaredType "a", UserDeclaredType "b"); FunctionType (UserDeclaredType "c", UserDeclaredType "d") ], [])
    ~printer:print_parse_ty_result

let test_nil_not_type _ =
  assert_raises (ParseError "Invalid type name") (fun _ ->
      parse_ty (tokenize "()"))

(* TODO: More type checks *)

let test_lispified_types _ =
  assert_equal
    (parse_ty (tokenize "((((((((a))))))))"))
    (UserDeclaredType "a", []) ~printer:print_parse_ty_result

let parse_tests =
  "test suite for parser"
  >::: [
         (* Type declarations *)
         "empty file" >:: test_empty;
         "simple type declaration" >:: test_simple_type_decl;
         "empty types are illegal" >:: test_empty_type_illegal;
         "multiple simple type decls" >:: test_multiple_type_decl;
         "single complex type decl" >:: test_type_of_decl;
         "multiple complex type decl" >:: test_multiple_of_decl;
         "complex type declaration" >:: test_mixed_ty_decl;
         (* Let statements *)
         "simple let statement" >:: test_untyped_let;
         "let statement with type" >:: test_typed_let_val;
         "let statement with one untyped parameter" >:: test_let_untyped_param;
         "let statement with one typed parameter" >:: test_let_typed_param;
         "let statement with multiple untyped params" >:: test_let_unty_params;
         "let statement with multiple typed params" >:: test_let_ty_params;
         "let statement with mixed-typed params" >:: test_let_complex_params;
         "let statement with mixed params and return" >:: test_let_complex;
         (* Let-in statements *)
         "simple let-in statement" >:: test_simple_let_in;
         "let-in with type" >:: test_typed_let_in_val;
         "let-in with one untyped param" >:: test_let_in_untyped_param;
         "let-in with one typed param" >:: test_let_in_typed_param;
         "let-in with multiple untyped params" >:: test_let_in_unty_params;
         "let-in with multiple typed params" >:: test_let_in_ty_params;
         "let-in with mixed params" >:: test_let_in_complex_params;
         "let-in with mixed params and return" >:: test_let_in_complex;
         "let-in whose value is a let-in" >:: test_nested_let_in_param;
         "let-in whose result is a let-in" >:: test_nested_let_in_value;
         (* Conditional statements *)
         "simple conditional" >:: test_simple_cond;
         "cond with cond in if" >:: test_nested_if_cond;
         "cond with cond in then" >:: test_nested_then_cond;
         "cond with cond in else" >:: test_nested_else_cond;
         "cond with conds everywhere" >:: test_super_nested_cond;
         (* Anonymous functions *)
         "nullary fun" >:: test_nullary_lambda;
         "simple fun" >:: test_simple_lambda;
         "fun with return type" >:: test_typed_lambda;
         "fun with single typed param" >:: test_lambda_typed_param;
         "fun with multiple untyped params" >:: test_lambda_unty_params;
         "fun with multiple typed params" >:: test_lambda_ty_params;
         "fun with mixed params" >:: test_lambda_complex_params;
         "fun with mixed params and return" >:: test_lambda_complex;
         "nested fun" >:: test_lambda_nested;
         (* Function calls *)
         "simple funcall" >:: test_simple_funcall;
         "multi-arg funcall" >:: test_multiple_funcall;
         "nested funcalls" >:: test_nested_funcall;
         "funcall of lambda" >:: test_funcall_fun;
         (* Tuples *)
         "simple tuple" >:: test_simple_tuple;
         "tuple with many values" >:: test_long_tuple;
         "nested tuples" >:: test_nested_tuple;
         "funcall in tuple" >:: test_tuple_funcall;
         "let-in inside tuple" >:: test_let_in_tuple;
         "fun inside tuple" >:: test_lambda_tuple;
         "tuple inside parens" >:: test_tuple_in_paren;
         (* Arithmetic operations *)
         "simple addition" >:: test_basic_addition;
         "associativity of addition" >:: test_addition_assoc;
         "simple subtraction" >:: test_basic_subtraction;
         "associativity of subtraction" >:: test_subtraction_assoc;
         "mixed addition & subtraction" >:: test_mixed_add_sub;
         "simple multiplication" >:: test_basic_multiplication;
         "associativity of multiplication" >:: test_mult_assoc;
         "simple division" >:: test_basic_division;
         "associativity of division" >:: test_div_assoc;
         "mixed mult & div" >:: test_mixed_mult_div;
         "simple modulo " >:: test_basic_modulo;
         "associativity of modulo" >:: test_mod_assoc;
         "unary minus" >:: test_simple_uminus;
         "nested unary minus" >:: test_nested_uminus;
         "unary minus and funcall" >:: test_uminus_funcall;
         "complex arithmetic expressions" >:: test_complex_arithmetic;
         (* Comparison operations *)
         "simple less-than" >:: test_basic_lt;
         "simple equality" >:: test_basic_eq;
         (* String concatenation *)
         "simple concatenation" >:: test_basic_concat;
         "associativity of concat" >:: test_concat_assoc;
         (* Logical operators *)
         "simple logical and" >:: test_basic_logand;
         "associativity of logand" >:: test_logand_assoc;
         "simple logical or" >:: test_basic_logor;
         "associativity of logor" >:: test_logor_assoc;
         "boolean operator precedence" >:: test_bool_precedence;
         "logical not" >:: test_simple_lognot;
         "precedence of logical not" >:: test_lognot_precedence;
         "logical not and funcall" >:: test_lognot_funcall;
         "complex logical operations" >:: test_complex_log_ops;
         "comparisons and logical ops" >:: test_cmp_with_log;
         (* Simple exprs *)
         "basic numbers" >:: test_numbers;
         "basic bools" >:: test_bools;
         "basic strings" >:: test_strings;
         (* Match statements *)
         "simple match" >:: test_simple_match;
         "multi-armed match" >:: test_multiarm_match;
         "bare match pattern" >:: test_simple_match_pat;
         "tuple match pattern" >:: test_tuple_match_pat;
         "long tuple match pattern" >:: test_long_tuple_match;
         "multiple tuple patterns" >:: test_multi_tup_match;
         "match with complex arms" >:: test_complex_match_arms;
         "match with match before with" >:: test_nested_match_param;
         "match with match in arm" >:: test_match_in_match_arm;
         (* TODO: Useful/practical examples *)
         "factorial function" >:: test_factorial;
         "length of list" >:: test_list_len;
         (* TODO: Cursed/unintuitive expressions *)
         "unit with comment" >:: test_nil_comment;
         "overly-nested parentheses" >:: test_parenthetopia;
         "logical or inside match" >:: test_loss_expr;
         (* Type syntax *)
         "basic types" >:: test_type_basic;
         "arrow types" >:: test_type_arrow;
         "product types" >:: test_type_product;
         "associativity of arrow" >:: test_associative_arrow;
         "associativity of product" >:: test_associative_prod;
         "operator precedence in types" >:: test_type_precedence;
         "complex precedence in types" >:: test_long_type_precedence;
         "parens overriding precedence" >:: test_type_parens;
         "() is not a type" >:: test_nil_not_type;
         "types with lots of parens" >:: test_lispified_types;
       ]
