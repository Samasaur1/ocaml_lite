open OUnit2
open Util
open Ocaml_lite.Ast
open Ocaml_lite.Lexer
open Ocaml_lite.Parser

(* `type` statements *)

let test_empty _ =
  assert_equal (parse [ EOF ]) [];
  assert_equal (parse []) []

let test_simple_type_decl _ =
  assert_equal
    (parse (tokenize "type a = | b;;"))
    [ TyDecl ("a", [ ("b", None) ]) ]

let test_empty_type_illegal _ =
  assert_raises (ParseError "Type list cannot be empty") (fun _ ->
      parse (tokenize "type a = ;;"))

let test_multiple_type_decl _ =
  assert_equal
    (parse (tokenize "type a = | b | c ;;"))
    [ TyDecl ("a", [ ("b", None); ("c", None) ]) ]

let test_type_of_decl _ =
  assert_equal
    (parse (tokenize "type a = | b of int ;;"))
    [ TyDecl ("a", [ ("b", Some TInt) ]) ]

let test_multiple_of_decl _ =
  assert_equal
    (parse (tokenize "type a = | b of string | c of int -> int ;;"))
    [ TyDecl ("a", [ ("b", Some TString); ("c", Some (TArrow (TInt, TInt))) ]) ]

let test_mixed_ty_decl _ =
  assert_equal
    (parse (tokenize "type a = | b of int -> string | c | d | e of bool ;;"))
    [
      TyDecl
        ( "a",
          [
            ("b", Some (TArrow (TInt, TString)));
            ("c", None);
            ("d", None);
            ("e", Some TBool);
          ] );
    ]

(* Top-level `let` statements *)

let test_untyped_let _ =
  assert_equal
    (parse (tokenize "let a = () ;;"))
    [ Let (false, "a", [], None, ENil) ];
  assert_equal
    (parse (tokenize "let rec a = () ;;"))
    [ Let (true, "a", [], None, ENil) ]

let test_typed_let_val _ =
  assert_equal
    (parse (tokenize "let a : unit = () ;;"))
    [ Let (false, "a", [], Some TUnit, ENil) ];
  assert_equal
    (parse (tokenize "let rec a : unit = () ;;"))
    [ Let (true, "a", [], Some TUnit, ENil) ]

let test_let_untyped_param _ =
  assert_equal
    (parse (tokenize "let a b = () ;;"))
    [ Let (false, "a", [ ("b", None) ], None, ENil) ];
  assert_equal
    (parse (tokenize "let rec a b = () ;;"))
    [ Let (true, "a", [ ("b", None) ], None, ENil) ]

let test_let_typed_param _ =
  assert_equal
    (parse (tokenize "let a (b : int) = () ;;"))
    [ Let (false, "a", [ ("b", Some TInt) ], None, ENil) ];
  assert_equal
    (parse (tokenize "let rec a (b : int) = () ;;"))
    [ Let (true, "a", [ ("b", Some TInt) ], None, ENil) ]

let test_let_unty_params _ =
  assert_equal
    (parse (tokenize "let a b c = () ;;"))
    [ Let (false, "a", [ ("b", None); ("c", None) ], None, ENil) ];
  assert_equal
    (parse (tokenize "let rec a b c = () ;;"))
    [ Let (true, "a", [ ("b", None); ("c", None) ], None, ENil) ]

let test_let_ty_params _ =
  assert_equal
    (parse (tokenize "let a (b : int -> unit) (c : string) = () ;;"))
    [
      Let
        ( false,
          "a",
          [ ("b", Some (TArrow (TInt, TUnit))); ("c", Some TString) ],
          None,
          ENil );
    ];
  assert_equal
    (parse (tokenize "let rec a (b : int -> unit) (c : string) = () ;;"))
    [
      Let
        ( true,
          "a",
          [ ("b", Some (TArrow (TInt, TUnit))); ("c", Some TString) ],
          None,
          ENil );
    ]

let test_let_complex_params _ =
  assert_equal
    (parse (tokenize "let a (b : int * string) c d (e : bool) = () ;;"))
    [
      Let
        ( false,
          "a",
          [
            ("b", Some (TProduct [ TInt; TString ]));
            ("c", None);
            ("d", None);
            ("e", Some TBool);
          ],
          None,
          ENil );
    ];
  assert_equal
    (parse (tokenize "let rec a (b : int * string) c d (e : bool) = () ;;"))
    [
      Let
        ( true,
          "a",
          [
            ("b", Some (TProduct [ TInt; TString ]));
            ("c", None);
            ("d", None);
            ("e", Some TBool);
          ],
          None,
          ENil );
    ]

let test_let_complex _ =
  assert_equal
    (parse
       (tokenize
          "let a b (c : (int * string) -> unit) d (e : unit) : int -> string = () ;;"))
    [
      Let
        ( false,
          "a",
          [
            ("b", None);
            ("c", Some (TArrow (TProduct [ TInt; TString ], TUnit)));
            ("d", None);
            ("e", Some TUnit);
          ],
          Some (TArrow (TInt, TString)),
          ENil );
    ];
  assert_equal
    (parse
       (tokenize
          "let rec a b (c : (int * string) -> unit) d (e : unit) : int -> string = () ;;"))
    [
      Let
        ( true,
          "a",
          [
            ("b", None);
            ("c", Some (TArrow (TProduct [ TInt; TString ], TUnit)));
            ("d", None);
            ("e", Some TUnit);
          ],
          Some (TArrow (TInt, TString)),
          ENil );
    ]

let test_simple_let_in _ =
  assert_equal
    (parse (tokenize "let a = let b = c in d ;;"))
    [
      Let (false, "a", [], None, LetIn (false, "b", [], None, EId "c", EId "d"));
    ];
  assert_equal
    (parse (tokenize "let a = let rec b = c in d ;;"))
    [
      Let (false, "a", [], None, LetIn (true, "b", [], None, EId "c", EId "d"));
    ]

let test_typed_let_in_val _ =
  assert_equal
    (parse (tokenize "let a = let b : unit = () in c ;;"))
    [
      Let
        (false, "a", [], None, LetIn (false, "b", [], Some TUnit, ENil, EId "c"));
    ];
  assert_equal
    (parse (tokenize "let a = let rec b : unit = () in c ;;"))
    [
      Let
        (false, "a", [], None, LetIn (true, "b", [], Some TUnit, ENil, EId "c"));
    ]

let test_let_in_untyped_param _ =
  assert_equal
    (parse (tokenize "let a = let b c = () in d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn (false, "b", [ ("c", None) ], None, ENil, EId "d") );
    ];
  assert_equal
    (parse (tokenize "let a = let rec b c = () in d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn (true, "b", [ ("c", None) ], None, ENil, EId "d") );
    ]

let test_let_in_typed_param _ =
  assert_equal
    (parse (tokenize "let a = let b (c : int) = () in d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn (false, "b", [ ("c", Some TInt) ], None, ENil, EId "d") );
    ];
  assert_equal
    (parse (tokenize "let a = let rec b (c : int) = () in d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn (true, "b", [ ("c", Some TInt) ], None, ENil, EId "d") );
    ]

let test_let_in_unty_params _ =
  assert_equal
    (parse (tokenize "let a = let b c d = () in e ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn (false, "b", [ ("c", None); ("d", None) ], None, ENil, EId "e")
        );
    ];
  assert_equal
    (parse (tokenize "let a = let rec b c d = () in e ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn (true, "b", [ ("c", None); ("d", None) ], None, ENil, EId "e")
        );
    ]

let test_let_in_ty_params _ =
  assert_equal
    (parse
       (tokenize "let a = let b (c : int) (d : string -> bool) = () in e ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn
            ( false,
              "b",
              [ ("c", Some TInt); ("d", Some (TArrow (TString, TBool))) ],
              None,
              ENil,
              EId "e" ) );
    ];
  assert_equal
    (parse
       (tokenize "let a = let rec b (c : int) (d : string -> bool) = () in e ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn
            ( true,
              "b",
              [ ("c", Some TInt); ("d", Some (TArrow (TString, TBool))) ],
              None,
              ENil,
              EId "e" ) );
    ]

let test_let_in_complex_params _ =
  assert_equal
    (parse
       (tokenize "let a = let b (c : string) d e (f : unit * bool) = () in g ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn
            ( false,
              "b",
              [
                ("c", Some TString);
                ("d", None);
                ("e", None);
                ("f", Some (TProduct [ TUnit; TBool ]));
              ],
              None,
              ENil,
              EId "g" ) );
    ];
  assert_equal
    (parse
       (tokenize
          "let a = let rec b (c : string) d e (f : unit * bool) = () in g ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn
            ( true,
              "b",
              [
                ("c", Some TString);
                ("d", None);
                ("e", None);
                ("f", Some (TProduct [ TUnit; TBool ]));
              ],
              None,
              ENil,
              EId "g" ) );
    ]

let test_let_in_complex _ =
  assert_equal
    (parse
       (tokenize
          "let a = let b (c : int * bool) d (e : unit -> unit) f : string = () in g ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn
            ( false,
              "b",
              [
                ("c", Some (TProduct [ TInt; TBool ]));
                ("d", None);
                ("e", Some (TArrow (TUnit, TUnit)));
                ("f", None);
              ],
              Some TString,
              ENil,
              EId "g" ) );
    ];
  assert_equal
    (parse
       (tokenize
          "let a = let rec b (c : int * bool) d (e : unit -> unit) f : string = () in g ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn
            ( true,
              "b",
              [
                ("c", Some (TProduct [ TInt; TBool ]));
                ("d", None);
                ("e", Some (TArrow (TUnit, TUnit)));
                ("f", None);
              ],
              Some TString,
              ENil,
              EId "g" ) );
    ]

let test_nested_let_in_param _ =
  assert_equal
    (parse (tokenize "let a = let b = let rec c = () in d in e ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn
            ( false,
              "b",
              [],
              None,
              LetIn (true, "c", [], None, ENil, EId "d"),
              EId "e" ) );
    ]

let test_nested_let_in_value _ =
  assert_equal
    (parse (tokenize "let a = let rec b = () in let c = () in d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          LetIn
            ( true,
              "b",
              [],
              None,
              ENil,
              LetIn (false, "c", [], None, ENil, EId "d") ) );
    ]

let test_simple_cond _ =
  assert_equal
    (parse (tokenize "let a = if b then c else d ;;"))
    [ Let (false, "a", [], None, Cond (EId "b", EId "c", EId "d")) ]

let test_nested_if_cond _ =
  assert_equal
    (parse (tokenize "let a = if if b then c else d then e else f ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Cond (Cond (EId "b", EId "c", EId "d"), EId "e", EId "f") );
    ]

let test_nested_then_cond _ =
  assert_equal
    (parse (tokenize "let a = if b then if c then d else e else f ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Cond (EId "b", Cond (EId "c", EId "d", EId "e"), EId "f") );
    ]

let test_nested_else_cond _ =
  assert_equal
    (parse (tokenize "let a = if b then c else if d then e else f ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Cond (EId "b", EId "c", Cond (EId "d", EId "e", EId "f")) );
    ]

let test_super_nested_cond _ =
  assert_equal
    (parse
       (tokenize
          "let a = if if b then c else d then if e then f else g else if h then i else j ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Cond
            ( Cond (EId "b", EId "c", EId "d"),
              Cond (EId "e", EId "f", EId "g"),
              Cond (EId "h", EId "i", EId "j") ) );
    ]

(* Remember that nullary functions are illegal *)
let test_nullary_lambda _ =
  assert_raises (ParseError "'fun' cannot have empty parameter list") (fun () ->
      parse (tokenize "let a = fun => () ;;"))

let test_simple_lambda _ =
  assert_equal
    (parse (tokenize "let a = fun x => () ;;"))
    [ Let (false, "a", [], None, Lambda ([ ("x", None) ], None, ENil)) ]

let test_typed_lambda _ =
  assert_equal
    (parse (tokenize "let a = fun x : unit => () ;;"))
    [ Let (false, "a", [], None, Lambda ([ ("x", None) ], Some TUnit, ENil)) ]

let test_lambda_typed_param _ =
  assert_equal
    (parse (tokenize "let a = fun (x : int) => () ;;"))
    [ Let (false, "a", [], None, Lambda ([ ("x", Some TInt) ], None, ENil)) ]

let test_lambda_unty_params _ =
  assert_equal
    (parse (tokenize "let a = fun x y z => () ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Lambda ([ ("x", None); ("y", None); ("z", None) ], None, ENil) );
    ]

let test_lambda_ty_params _ =
  assert_equal
    (parse (tokenize "let a = fun (x : int -> string) (y : bool) => () ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Lambda
            ( [ ("x", Some (TArrow (TInt, TString))); ("y", Some TBool) ],
              None,
              ENil ) );
    ]

let test_lambda_complex_params _ =
  assert_equal
    (parse (tokenize "let a = fun (w : int) x (y : bool * unit) z => () ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Lambda
            ( [
                ("w", Some TInt);
                ("x", None);
                ("y", Some (TProduct [ TBool; TUnit ]));
                ("z", None);
              ],
              None,
              ENil ) );
    ]

let test_lambda_complex _ =
  assert_equal
    (parse
       (tokenize
          "let a = fun w x (y : unit * unit) (z : int -> string) : unit => () ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Lambda
            ( [
                ("w", None);
                ("x", None);
                ("y", Some (TProduct [ TUnit; TUnit ]));
                ("z", Some (TArrow (TInt, TString)));
              ],
              Some TUnit,
              ENil ) );
    ]

let test_lambda_nested _ =
  assert_equal
    (parse (tokenize "let a = fun x => fun y => () ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Lambda ([ ("x", None) ], None, Lambda ([ ("y", None) ], None, ENil))
        );
    ]

(* TODO: Expressions w/i funcall *)

let test_simple_funcall _ =
  assert_equal
    (parse (tokenize "let a = b c ;;"))
    [ Let (false, "a", [], None, Funcall (EId "b", EId "c")) ]

let test_multiple_funcall _ =
  assert_equal
    (parse (tokenize "let a = b c d e ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Funcall (Funcall (Funcall (EId "b", EId "c"), EId "d"), EId "e") );
    ]

let test_nested_funcall _ =
  assert_equal
    (parse (tokenize "let a = (b c) (d e) ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Funcall (Funcall (EId "b", EId "c"), Funcall (EId "d", EId "e")) );
    ]

let test_funcall_fun _ =
  assert_equal
    (parse (tokenize "let a = (fun x => ()) y ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Funcall (Lambda ([ ("x", None) ], None, ENil), EId "y") );
    ]

let test_simple_tuple _ =
  assert_equal
    (parse (tokenize "let a = (b, c) ;;"))
    [ Let (false, "a", [], None, Tuple [ EId "b"; EId "c" ]) ]

let test_long_tuple _ =
  assert_equal
    (parse (tokenize "let a = (b, c, d, e, f, g) ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Tuple [ EId "b"; EId "c"; EId "d"; EId "e"; EId "f"; EId "g" ] );
    ]

let test_nested_tuple _ =
  assert_equal
    (parse (tokenize "let a = ((b, c), d, ((e, f, g), h)) ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Tuple
            [
              Tuple [ EId "b"; EId "c" ];
              EId "d";
              Tuple [ Tuple [ EId "e"; EId "f"; EId "g" ]; EId "h" ];
            ] );
    ]

let test_tuple_funcall _ =
  assert_equal
    (parse (tokenize "let a = (b c, d) ;;"))
    [
      Let (false, "a", [], None, Tuple [ Funcall (EId "b", EId "c"); EId "d" ]);
    ]

let test_let_in_tuple _ =
  assert_equal
    (parse (tokenize "let a = (let b = () in c, let rec d = () in f) ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Tuple
            [
              LetIn (false, "b", [], None, ENil, EId "c");
              LetIn (true, "d", [], None, ENil, EId "f");
            ] );
    ]

let test_lambda_tuple _ =
  assert_equal
    (parse (tokenize "let a = (fun x => (), fun y => y) ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          Tuple
            [
              Lambda ([ ("x", None) ], None, ENil);
              Lambda ([ ("y", None) ], None, EId "y");
            ] );
    ]

let test_tuple_in_paren _ =
  assert_equal
    (parse (tokenize "let a = ((b, c)) ;;"))
    [ Let (false, "a", [], None, Tuple [ EId "b"; EId "c" ]) ]

let test_basic_addition _ =
  assert_equal
    (parse (tokenize "let a = b + c ;;"))
    [ Let (false, "a", [], None, BinOp (BPlus, EId "b", EId "c")) ]

let test_addition_assoc _ =
  assert_equal
    (parse (tokenize "let a = b + c + d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BPlus, BinOp (BPlus, EId "b", EId "c"), EId "d") );
    ]

let test_basic_subtraction _ =
  assert_equal
    (parse (tokenize "let a = b - c ;;"))
    [ Let (false, "a", [], None, BinOp (BMinus, EId "b", EId "c")) ]

let test_subtraction_assoc _ =
  assert_equal
    (parse (tokenize "let a = b - c - d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BMinus, BinOp (BMinus, EId "b", EId "c"), EId "d") );
    ]

let test_mixed_add_sub _ =
  assert_equal
    (parse (tokenize "let a = b + c - d + e ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp
            ( BPlus,
              BinOp (BMinus, BinOp (BPlus, EId "b", EId "c"), EId "d"),
              EId "e" ) );
    ]

let test_basic_multiplication _ =
  assert_equal
    (parse (tokenize "let a = b * c ;;"))
    [ Let (false, "a", [], None, BinOp (BTimes, EId "b", EId "c")) ]

let test_mult_assoc _ =
  assert_equal
    (parse (tokenize "let a = b * c * d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BTimes, BinOp (BTimes, EId "b", EId "c"), EId "d") );
    ]

let test_basic_division _ =
  assert_equal
    (parse (tokenize "let a = b / c ;;"))
    [ Let (false, "a", [], None, BinOp (BDiv, EId "b", EId "c")) ]

let test_mixed_mult_div _ =
  assert_equal
    (parse (tokenize "let a = b * c / d mod e ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp
            ( BMod,
              BinOp (BDiv, BinOp (BTimes, EId "b", EId "c"), EId "d"),
              EId "e" ) );
    ]

let test_div_assoc _ =
  assert_equal
    (parse (tokenize "let a = b / c / d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BDiv, BinOp (BDiv, EId "b", EId "c"), EId "d") );
    ]

let test_basic_modulo _ =
  assert_equal
    (parse (tokenize "let a = b mod c ;;"))
    [ Let (false, "a", [], None, BinOp (BMod, EId "b", EId "c")) ]

let test_mod_assoc _ =
  assert_equal
    (parse (tokenize "let a = b mod c mod d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BMod, BinOp (BMod, EId "b", EId "c"), EId "d") );
    ]

let test_simple_uminus _ =
  assert_equal
    (parse (tokenize "let a = ~b ;;"))
    [ Let (false, "a", [], None, UnOp (UBitNot, EId "b")) ]

let test_nested_uminus _ =
  assert_equal
    (parse (tokenize "let a = ~~b ;;"))
    [ Let (false, "a", [], None, UnOp (UBitNot, UnOp (UBitNot, EId "b"))) ]

let test_uminus_funcall _ =
  assert_equal
    (parse (tokenize "let a = ~b c ;;"))
    [ Let (false, "a", [], None, UnOp (UBitNot, Funcall (EId "b", EId "c"))) ]

let test_complex_arithmetic _ =
  assert_equal
    (parse (tokenize "let a = b * c + d mod e / ~f - g ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp
            ( BMinus,
              BinOp
                ( BPlus,
                  BinOp (BTimes, EId "b", EId "c"),
                  BinOp
                    ( BDiv,
                      BinOp (BMod, EId "d", EId "e"),
                      UnOp (UBitNot, EId "f") ) ),
              EId "g" ) );
    ]

let test_basic_lt _ =
  assert_equal
    (parse (tokenize "let a = b < c ;;"))
    [ Let (false, "a", [], None, BinOp (BLessThan, EId "b", EId "c")) ]

let test_basic_eq _ =
  assert_equal
    (parse (tokenize "let a = b = c ;;"))
    [ Let (false, "a", [], None, BinOp (BEquals, EId "b", EId "c")) ]

let test_basic_concat _ =
  assert_equal
    (parse (tokenize "let a = b ^ c ;;"))
    [ Let (false, "a", [], None, BinOp (BConcat, EId "b", EId "c")) ]

let test_concat_assoc _ =
  assert_equal
    (parse (tokenize "let a = b ^ c ^ d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BConcat, BinOp (BConcat, EId "b", EId "c"), EId "d") );
    ]

(* TODO: Mix < and = with &&, || *)

let test_basic_logand _ =
  assert_equal
    (parse (tokenize "let a = b && c ;;"))
    [ Let (false, "a", [], None, BinOp (BLogAnd, EId "b", EId "c")) ]

let test_logand_assoc _ =
  assert_equal
    (parse (tokenize "let a = b && c && d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BLogAnd, BinOp (BLogAnd, EId "b", EId "c"), EId "d") );
    ]

let test_basic_logor _ =
  assert_equal
    (parse (tokenize "let a = b || c ;;"))
    [ Let (false, "a", [], None, BinOp (BLogOr, EId "b", EId "c")) ]

let test_logor_assoc _ =
  assert_equal
    (parse (tokenize "let a = b || c || d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BLogOr, BinOp (BLogOr, EId "b", EId "c"), EId "d") );
    ]

let test_bool_precedence _ =
  assert_equal
    (parse (tokenize "let a = b || c && d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BLogOr, EId "b", BinOp (BLogAnd, EId "c", EId "d")) );
    ];
  assert_equal
    (parse (tokenize "let a = b && c || d ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BLogOr, BinOp (BLogAnd, EId "b", EId "c"), EId "d") );
    ]

let test_simple_lognot _ =
  assert_equal
    (parse (tokenize "let a = not b ;;"))
    [ Let (false, "a", [], None, UnOp (ULogNot, EId "b")) ]

let test_nested_lognot _ =
  assert_equal
    (parse (tokenize "let a = not not not b ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          UnOp (ULogNot, UnOp (ULogNot, UnOp (ULogNot, EId "b"))) );
    ]

let test_lognot_precedence _ =
  assert_equal
    (parse (tokenize "let a = not b || not c ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BLogOr, UnOp (ULogNot, EId "b"), UnOp (ULogNot, EId "c")) );
    ];
  assert_equal
    (parse (tokenize "let a = not b && not c ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp (BLogAnd, UnOp (ULogNot, EId "b"), UnOp (ULogNot, EId "c")) );
    ]

(* NOTE: This is not valid OCaml syntax (where `not` is treated as a normal
   function), but it is valid according to the rules given for OCaml-lite. *)
let test_lognot_funcall _ =
  assert_equal
    (parse (tokenize "let a = not b c ;;"))
    [ Let (false, "a", [], None, UnOp (ULogNot, Funcall (EId "b", EId "c"))) ]

let test_complex_log_ops _ =
  assert_equal
    (parse (tokenize "let a = b || not c && not d && e || f || g ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp
            ( BLogOr,
              BinOp
                ( BLogOr,
                  BinOp
                    ( BLogOr,
                      EId "b",
                      BinOp
                        ( BLogAnd,
                          BinOp
                            ( BLogAnd,
                              UnOp (ULogNot, EId "c"),
                              UnOp (ULogNot, EId "d") ),
                          EId "e" ) ),
                  EId "f" ),
              EId "g" ) );
    ]

let test_cmp_with_log _ =
  assert_equal
    (parse (tokenize "let a = b && c < d || e = f || g ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          BinOp
            ( BLogOr,
              BinOp
                ( BLogOr,
                  BinOp (BLogAnd, EId "b", BinOp (BLessThan, EId "c", EId "d")),
                  BinOp (BEquals, EId "e", EId "f") ),
              EId "g" ) );
    ]

let test_numbers _ =
  List.iter
    (fun x ->
      assert_equal
        (parse (tokenize ("let a = " ^ string_of_int x ^ " ;;")))
        [ Let (false, "a", [], None, EInt x) ])
    (range_inc 1 20)

let test_bools _ =
  List.iter
    (fun x ->
      assert_equal
        (parse (tokenize ("let a = " ^ string_of_bool x ^ " ;;")))
        [ Let (false, "a", [], None, EBool x) ])
    [ true; false ]

let test_strings _ =
  assert_equal
    (parse (tokenize "let a = \"abc\" ;;"))
    [ Let (false, "a", [], None, EStr "abc") ]

let test_simple_match _ =
  assert_equal
    (parse (tokenize "let a = match b with | c => d ;;"))
    [ Let (false, "a", [], None, EMatch (EId "b", [ ("c", None, EId "d") ])) ]

let test_multiarm_match _ =
  assert_equal
    (parse (tokenize "let a = match b with | c => d | e => f ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          EMatch (EId "b", [ ("c", None, EId "d"); ("e", None, EId "f") ]) );
    ]

let test_simple_match_pat _ =
  assert_equal
    (parse (tokenize "let a = match b with | c d => e ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          EMatch (EId "b", [ ("c", Some (BarePat "d"), EId "e") ]) );
    ]

let test_tuple_match_pat _ =
  assert_equal
    (parse (tokenize "let a = match b with | c (d, e) => f ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          EMatch (EId "b", [ ("c", Some (TuplePat [ "d"; "e" ]), EId "f") ]) );
    ]

let test_long_tuple_match _ =
  assert_equal
    (parse (tokenize "let a = match b with | c (d, e, f, g) => h ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          EMatch
            (EId "b", [ ("c", Some (TuplePat [ "d"; "e"; "f"; "g" ]), EId "h") ])
        );
    ]

let test_multi_tup_match _ =
  assert_equal
    (parse
       (tokenize "let a = match b with | c (d, e) => f | g (h, i, j) => k ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          EMatch
            ( EId "b",
              [
                ("c", Some (TuplePat [ "d"; "e" ]), EId "f");
                ("g", Some (TuplePat [ "h"; "i"; "j" ]), EId "k");
              ] ) );
    ]

let test_complex_match_arms _ =
  assert_equal
    (parse
       (tokenize
          "let a = match b with | c (d, e, f) => g | h => i | j k => l | m => n ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          EMatch
            ( EId "b",
              [
                ("c", Some (TuplePat [ "d"; "e"; "f" ]), EId "g");
                ("h", None, EId "i");
                ("j", Some (BarePat "k"), EId "l");
                ("m", None, EId "n");
              ] ) );
    ]

let test_nested_match_param _ =
  assert_equal
    (parse (tokenize "let a = match match b with | c => d with | e => f ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          EMatch
            ( EMatch (EId "b", [ ("c", None, EId "d") ]),
              [ ("e", None, EId "f") ] ) );
    ]

let test_match_in_match_arm _ =
  assert_equal
    (parse
       (tokenize "let a = match b with | c => match d with | e => f | g => h ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          EMatch
            ( EId "b",
              [
                ( "c",
                  None,
                  EMatch
                    (EId "d", [ ("e", None, EId "f"); ("g", None, EId "h") ]) );
              ] ) );
    ]

let test_factorial _ =
  assert_equal
    (parse
       (tokenize
          "let rec fact n = if n = 0 || n = 1 then 1 else (fact (n - 1)) + (fact (n - 2)) ;;"))
    [
      Let
        ( true,
          "fact",
          [ ("n", None) ],
          None,
          Cond
            ( BinOp
                ( BLogOr,
                  BinOp (BEquals, EId "n", EInt 0),
                  BinOp (BEquals, EId "n", EInt 1) ),
              EInt 1,
              BinOp
                ( BPlus,
                  Funcall (EId "fact", BinOp (BMinus, EId "n", EInt 1)),
                  Funcall (EId "fact", BinOp (BMinus, EId "n", EInt 2)) ) ) );
    ]

let test_list_len _ =
  assert_equal
    (parse
       (tokenize
          ("type int_list = | Nil | Val of int * int_list ;;\n"
         ^ "let rec len l = match l with | Nil => 0 | Val (_, rest) => 1 + len rest ;;"
          )))
    [
      TyDecl
        ( "int_list",
          [ ("Nil", None); ("Val", Some (TProduct [ TInt; TId "int_list" ])) ]
        );
      Let
        ( true,
          "len",
          [ ("l", None) ],
          None,
          EMatch
            ( EId "l",
              [
                ("Nil", None, EInt 0);
                ( "Val",
                  Some (TuplePat [ "_"; "rest" ]),
                  BinOp (BPlus, EInt 1, Funcall (EId "len", EId "rest")) );
              ] ) );
    ]

let test_nil_comment _ =
  assert_equal
    (parse (tokenize "let a = ((**)) ;;"))
    [ Let (false, "a", [], None, ENil) ]

let test_parenthetopia _ =
  assert_equal
    (parse (tokenize "let a = (()((()()((()((())))())))()()) ;;"))
    (* (nil (nil nil ((nil nil) nil)) nil nil) *)
    [
      Let
        ( false,
          "a",
          [],
          None,
          Funcall
            ( Funcall
                ( Funcall
                    ( ENil,
                      Funcall
                        ( Funcall (ENil, ENil),
                          Funcall (Funcall (ENil, ENil), ENil) ) ),
                  ENil ),
              ENil ) );
    ]

let test_loss_expr _ =
  assert_equal
    (parse (tokenize "let a = match b with | c => d || e || f |_ => g ;;"))
    [
      Let
        ( false,
          "a",
          [],
          None,
          EMatch
            ( EId "b",
              [
                ( "c",
                  None,
                  BinOp (BLogOr, BinOp (BLogOr, EId "d", EId "e"), EId "f") );
                ("_", None, EId "g");
              ] ) );
    ]

(* TODO: Cursed ideas *)
(* Over-parenthesized exprs (besides nil) *)
(* Horribly-nested match/if/let statements *)

let basic_types =
  [ (TNInt, TInt); (TNBool, TBool); (TNString, TString); (TNUnit, TUnit) ]

let basic_tys = List.map snd basic_types
let basic_tynames = List.map fst basic_types

let print_parse_ty_result : ty * token list -> string = function
  | t, [] -> ty_to_string t
  | _ -> "Token list was not empty"

let test_type_basic _ =
  assert_equal
    (parse_ty (tokenize "int"))
    (TInt, []) ~printer:print_parse_ty_result;
  assert_equal
    (parse_ty (tokenize "bool"))
    (TBool, []) ~printer:print_parse_ty_result;
  assert_equal
    (parse_ty (tokenize "string"))
    (TString, []) ~printer:print_parse_ty_result;
  assert_equal
    (parse_ty (tokenize "unit"))
    (TUnit, []) ~printer:print_parse_ty_result

let test_type_arrow _ =
  List.iter
    (fun ((tn, t), (un, u)) ->
      assert_equal
        (parse_ty [ tn; Arrow; un ])
        (TArrow (t, u), [])
        ~printer:print_parse_ty_result)
    (cartesian basic_types basic_types)

let test_type_product _ =
  List.iter
    (fun ((tn, t), (un, u)) ->
      assert_equal
        (parse_ty [ tn; Times; un ])
        (TProduct [ t; u ], [])
        ~printer:print_parse_ty_result)
    (cartesian basic_types basic_types)

let test_associative_arrow _ =
  assert_equal
    (parse_ty (tokenize "a -> b -> c"))
    (TArrow (TId "a", TArrow (TId "b", TId "c")), [])
    ~printer:print_parse_ty_result

let test_associative_prod _ =
  assert_equal
    (parse_ty (tokenize "a * b * c"))
    (TProduct [ TId "a"; TId "b"; TId "c" ], [])
    ~printer:print_parse_ty_result

let test_type_precedence _ =
  assert_equal
    (parse_ty (tokenize "a -> b * c"))
    (TArrow (TId "a", TProduct [ TId "b"; TId "c" ]), [])
    ~printer:print_parse_ty_result;
  assert_equal
    (parse_ty (tokenize "a * b -> c"))
    (TArrow (TProduct [ TId "a"; TId "b" ], TId "c"), [])
    ~printer:print_parse_ty_result

let test_long_type_precedence _ =
  assert_equal
    (parse_ty (tokenize "a * b * c -> d * e -> f * g * h"))
    ( TArrow
        ( TProduct [ TId "a"; TId "b"; TId "c" ],
          TArrow
            ( TProduct [ TId "d"; TId "e" ],
              TProduct [ TId "f"; TId "g"; TId "h" ] ) ),
      [] )
    ~printer:print_parse_ty_result

let test_type_parens _ =
  assert_equal
    (parse_ty (tokenize "(a -> b) * (c -> d)"))
    (TProduct [ TArrow (TId "a", TId "b"); TArrow (TId "c", TId "d") ], [])
    ~printer:print_parse_ty_result

let test_nil_not_type _ =
  assert_raises (ParseError "Invalid type name") (fun _ ->
      parse_ty (tokenize "()"))

(* TODO: More type checks *)

let test_lispified_types _ =
  assert_equal
    (parse_ty (tokenize "((((((((a))))))))"))
    (TId "a", []) ~printer:print_parse_ty_result

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
