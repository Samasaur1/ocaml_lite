open Ast
open Lexer

exception ParseError of string

let rec parse_program (lst: token list): program * token list = 
  let rec help (rr: binding list) (toks: token list): binding list * token list =
    match toks with
    | [] -> (rr, toks)
    | _ -> let (b, r) = parse_binding toks in
      match r with
      | DoubleSemicolon :: r2 -> help (b :: rr) r2
      | x :: _ -> raise (ParseError ("Expected `;;`, got " ^ tok_to_str x ^ " (`" ^ (List.map tok_to_str r |> String.concat " ") ^ "`)"))
      | [] -> raise (ParseError ("Expected `;;`, got end of input (prog: " ^ (string_of_program 0 (Program (List.rev (b :: rr))))))
  in
    let (bds, rest) = help [] lst in
      (Program (List.rev bds), rest)

and parse_binding (lst: token list): binding * token list =
  match lst with
    (* | Type :: Id x :: Eq :: r ->  *)
  | Let :: Id _ :: _ -> parse_nonrec_binding lst
  | Let :: Rec :: _ -> parse_rec_binding lst
  | Type :: _ -> parse_type_binding lst
  | x :: _ -> raise (ParseError ("Expected binding, got " ^ tok_to_str x))
  | [] -> failwith "There must be at least one binding"
and parse_param_list (lst: token list): param list * token list =
  match lst with
  | Id p :: r -> let (subsequent, r2) = parse_param_list r in
    (UntypedParam p :: subsequent, r2)
  | LParen :: Id p :: Colon :: r ->
    let (t, r2) = parse_type r in
    (match r2 with
      | RParen :: r3 -> let (subsequent, rest) = parse_param_list r3 in
        (TypedParam (p, t) :: subsequent, rest)
      | x :: _ -> raise (ParseError ("Expected closing paren, got " ^ tok_to_str x))
      | [] -> raise (ParseError ("Expected closing paren, got end of input"))
    )
  | _ -> ([], lst)
and parse_let_binding_common (r: token list): param list * typ option * expr * token list =
    let (params, r2) = parse_param_list r in
      match r2 with
      | Colon :: r3 ->
        let (t, r4) = parse_type r3 in
          (match r4 with
          | Eq :: r5 ->
            let (e, rest) = parse_expr r5 in
              (params, Some(t), e, rest)
          | x :: _ -> raise (ParseError ("Expected `=`, got " ^ tok_to_str x))
          | [] -> raise (ParseError ("Expected `=`, got end of input")))
      | Eq :: r3 ->
        let (e, rest) = parse_expr r3 in
          (params, None, e, rest)
      | x :: _ -> raise (ParseError ("Expected either `:` or `=`, got " ^ tok_to_str x))
      | [] -> raise (ParseError ("Expected either `:` or `=`, got end of input"))
and parse_nonrec_binding (lst: token list): binding * token list =
  match lst with
  | Let :: Id x :: r -> let (params, ty, ex, rest) = parse_let_binding_common r in
    (NonRecursiveBinding (x, params, ty, ex), rest)
  | _ -> failwith "Unreachable"
and parse_rec_binding (lst: token list): binding * token list =
  match lst with
  | Let :: Rec :: Id x :: r -> let (params, ty, ex, rest) = parse_let_binding_common r in
    (RecursiveBinding (x, params, ty, ex), rest)
  | _ -> failwith "Unreachable"
and parse_type_binding (lst: token list): binding * token list =
  match lst with
  | Type :: Id x :: Eq :: r -> (
      let rec help (rr: (string * typ option) list) (toks: token list): (string * typ option) list * token list =
        match toks with
        | DoubleSemicolon :: _ -> (rr, toks)
        | Pipe :: Id c :: Of :: r2 ->
          let (t, r3) = parse_type r2 in
            (* ((c, Some t) :: rr, r3) *)
            help ((c, Some t) :: rr) r3
        | Pipe :: Id c :: r2 ->
          (* ((c, None) :: rr, r2) *)
          help ((c, None) :: rr) r2
        | Pipe :: x :: _ -> raise (ParseError ("Expected constructor name, got " ^ tok_to_str x))
        | x :: _ -> raise (ParseError ("Expected `|`, got " ^ tok_to_str x))
        | [] -> raise (ParseError ("Expected `|`, got end of input"))
      in
        let (brs, rest) = help [] r in
          match brs with
          | [] -> raise (ParseError "Type list cannot be empty")
          | _ -> (TypeDefBinding (x, List.rev brs), rest)
  )
  | Type :: Id _ :: x :: _ -> raise (ParseError ("Expected `=`, got " ^ tok_to_str x))
  | Type :: x :: _ -> raise (ParseError ("Expected type name, got " ^ tok_to_str x))
  | _ -> failwith "Unreachable"
(*
The binary operators are all left-associative (except for < and =, which are non-associative) and all operators have their normal precedences:

(Highest precedence)
not
~
*, /, mod
+, -, ^
<, =
&&
||
(Lowest precedence)

  *)
and parse_expr (lst: token list): expr * token list =
  let rec parse_expr_toplevel (s: token list): expr * token list =
  (*   let (e1, r) = parse_expr_binops s in *)
  (*   try *)
  (*     let (e2, r2) = parse_expr_binops r in *)
  (*     (FunAppExpr (e1, e2), r2) *)
  (*   with *)
  (*     | ParseError _ -> (e1, r) *)
  parse_expr_binops s
  and parse_expr_binops (s: token list): expr * token list =
    let rec help ex = function
      | Or :: r ->
        let (e, rest) = prenot r in
        help (BinopExpr (ex, Or, e)) rest
      | ts -> (ex, ts) in
    let (e, r) = prenot s in
    help e r
  and prenot (s: token list): expr * token list =
    let rec help ex = function
      | And :: r ->
        let (e, rest) = comp r in
        help (BinopExpr (ex, And, e)) rest
      | ts -> (ex, ts) in
    let (e, r) = comp s in
    help e r
  and comp (s: token list): expr * token list =
    let rec help ex  = function
      | Lt :: r ->
        let (e, rest) = addition r in
        help (BinopExpr (ex, LessThan, e)) rest
      | Eq :: r ->
        let (e, rest) = addition r in
        help (BinopExpr (ex, Equal, e)) rest
      | ts -> (ex, ts) in
    let (e, r) = addition s in
    help e r
  and addition (s: token list): expr * token list =
    let rec help ex  = function
      | Plus :: r ->
        let (e, rest) = term r in
        help (BinopExpr (ex, Plus, e)) rest
      | Minus :: r ->
        let (e, rest) = term r in
        help (BinopExpr (ex, Minus, e)) rest
      | Concat :: r ->
        let (e, rest) = term r in
        help (BinopExpr (ex, Concat, e)) rest
      | ts -> (ex, ts) in
    let (e, r) = term s in
    help e r
  and term (s: token list): expr * token list =
    let rec help ex  = function
      | Times :: r ->
        let (e, rest) = factor r in
        help (BinopExpr (ex, Times, e)) rest
      | Divide :: r ->
        let (e, rest) = factor r in
        help (BinopExpr (ex, Divide, e)) rest
      | Mod :: r ->
        let (e, rest) = factor r in
        help (BinopExpr (ex, Modulo, e)) rest
      | ts -> (ex, ts) in
    let (e, r) = factor s in
    help e r
  and factor (s: token list): expr * token list =
    (* let rec help ex  = function
    (* | Not :: r -> *)
    (*   let (e, rest) = addition r in *)
    (*   help (LessThan (ex, e)) rest *)
    | ts -> (ex, ts) in
  let (e, r) = atom s in
  help e r *)
    match s with
    | Negate :: r ->
      let (e, r) = factor r in
      (UnopExpr (NegateInt, e), r)
    | _ -> atom' s
  and atom' (s: token list): expr * token list =
    match s with
    | Not :: r ->
      let (e, r) = atom' r in
      (UnopExpr (InvertBool, e), r)
    | _ -> atom'' s
  and atom'' (s: token list): expr * token list =
    let rec help (rr: expr) (toks: token list): expr * token list =
      try
        let (base', r) = atom toks in
        help (FunAppExpr (rr, base')) r
      with
        ParseError _ -> (rr, toks)
    in
    let (base, rest) = atom s in
    help base rest
  and atom (s: token list): expr * token list =
    (* match s with *)
    (* | LParen :: r -> *)
    (*   let (e, r2) = parse_expr r in *)
    (*   (match r2 with *)
    (*     | RParen :: rest -> (e, rest) *)
    (*     | [] -> raise (ParseError "Expected ), got end of input") *)
    (*     | t :: _ -> raise (ParseError ("Expected ), got " ^ tok_to_str t))) *)
    (* | Lit i :: r -> (Int i, r) *)
    (* | True :: r -> (Bool true, r) *)
    (* | False :: r -> (Bool false, r) *)
    (* | Var v :: r -> (Var v, r) *)
    (* | If :: r -> *)
    (*   let (cond, r2) = parse_expr r in *)
    (*   (match r2 with *)
    (*     | Then :: r3 -> *)
    (*       let (iftrue, r4) = parse_expr r3 in *)
    (*       (match r4 with *)
    (*         | Else :: r5 -> *)
    (*           let (iffalse, rest) = parse_expr r5 in *)
    (*           (If (cond, iftrue, iffalse), rest) *)
    (*         | [] -> raise (ParseError "Expected `else`, got end of input") *)
    (*         | t :: _ -> raise (ParseError ("Expected `else`, got `" ^ tok_to_str t ^ "`"))) *)
    (*     | [] -> raise (ParseError "Expected `then`, got end of input") *)
    (*     | t :: _ -> raise (ParseError ("Expected `then`, got `" ^ tok_to_str t ^ "`"))) *)
    (* | Let :: (Var id :: (Eq :: r)) -> *)
    (*   let (value, r2) = parse_expr r in *)
    (*   (match r2 with *)
    (*     | In :: r3 -> *)
    (*       let (scope, rest) = parse_expr r3 in *)
    (*       (Let (id, value, scope), rest) *)
    (*     | [] -> raise (ParseError "Expected `in`, got end of input") *)
    (*     | t :: _ -> raise (ParseError ("Expected `in`, got `" ^ tok_to_str t ^ "`"))) *)
    (* | [] -> raise (ParseError "Expected <int> or (, got end of input") *)
    (* | t :: _ -> raise (ParseError ("Expected <int> or (, got " ^ tok_to_str t)) *)
    match s with
    | Let :: Id x :: r -> let (params, ty, ex, r2) = parse_let_binding_common r in
      (match r2 with
        | In :: r3 ->
            let (body, rest) = parse_expr_toplevel r3 in
              (LetExpr (x, params, ty, ex, body), rest)
        | tok :: _ -> raise (ParseError ("Expected `in`, got " ^ tok_to_str tok))
        | [] -> raise (ParseError ("Expected `in`, got end of input"))
      )
    | Let :: Rec :: Id x :: r -> let (params, ty, ex, r2) = parse_let_binding_common r in
      (match r2 with
        | In :: r3 ->
            let (body, rest) = parse_expr_toplevel r3 in
              (LetRecExpr (x, params, ty, ex, body), rest)
        | tok :: _ -> raise (ParseError ("Expected `in`, got " ^ tok_to_str tok))
        | [] -> raise (ParseError ("Expected `in`, got end of input"))
      )
    | If :: r -> let (c, r2) = parse_expr r in
      (match r2 with
        | Then :: r3 -> let (t, r4) = parse_expr r3 in
          (match r4 with
            | Else :: r5 -> let (f, rest) = parse_expr r5 in
              (IfExpr (c, t, f), rest)
            | x :: _ -> raise (ParseError ("Expected `else`, got " ^ tok_to_str x))
            | [] -> raise (ParseError ("Expected `else`, got end of input")))
        | x :: _ -> raise (ParseError ("Expected `then`, got " ^ tok_to_str x))
        | [] -> raise (ParseError ("Expected `then`, got end of input")))
    | Fun :: r -> let (params, r2) = parse_param_list r in
      (match params with
        | [] -> raise (ParseError ("'fun' cannot have empty parameter list"))
        | _ -> 
          (match r2 with
            | DoubleArrow :: r3 -> let (body, rest) = parse_expr r3 in
              (FunDefExpr (params, None, body), rest)
            | Colon :: r3 -> let (t, r4) = parse_type r3 in
              (match r4 with
                | DoubleArrow :: r5 -> let (body, rest) = parse_expr r5 in
                  (FunDefExpr (params, Some (t), body), rest)
                | x :: _ -> raise (ParseError ("Expected `=>`, got " ^ tok_to_str x))
                | [] -> raise (ParseError ("Expected `=>`, got end of input"))
              )
            | x :: _ -> raise (ParseError ("Expected `:` or `=>`, got " ^ tok_to_str x))
            | [] -> raise (ParseError ("Expected `:` or `=>`, got end of input"))
          ))
    | LParen :: RParen :: rest -> (UnitExpr, rest)
    | LParen :: r -> let (e, r2) = parse_expr_toplevel r in
      (match r2 with
        | RParen :: rest -> (e, rest) (* expr in parens *)
        | Comma :: _ -> let (members, rest) = parse_tuple_expr r2 in
            (TupleExpr (e :: members), rest)
        | x :: _ -> raise (ParseError ("Expected `,` or `)`, got " ^ tok_to_str x))
        | [] -> raise (ParseError ("Expected `,` or `)`, got end of input")))
    | Int i :: rest -> (IntLiteralExpr i, rest)
    | True :: rest -> (BoolLiteralExpr true, rest)
    | False :: rest -> (BoolLiteralExpr false, rest)
    | String s :: rest -> (StringLiteralExpr s, rest)
    | Id x :: rest -> (VarExpr x, rest)
    | Match :: r -> let (e, r2) = parse_expr_toplevel r in
      (match r2 with
        | With :: r3 -> let (brs, rest) = parse_match_branches [] r3 in
          (MatchExpr (e, List.rev brs), rest)
        | x :: _ -> raise (ParseError ("Expected `with`, got " ^ tok_to_str x))
        | [] -> raise (ParseError ("Expected `with`, got end of input")))
    | x :: _ -> raise (ParseError ("Expected expr, got " ^ tok_to_str x))
    | [] -> raise (ParseError ("Expected expr, got end of input"))
  and parse_tuple_expr (toks: token list): expr list * token list =
    match toks with
    | RParen :: rest -> ([], rest)
    | Comma :: r -> let (e, r2) = parse_expr_toplevel r in
        let (subsequent, rest) = parse_tuple_expr r2 in
          (e :: subsequent, rest)
    | x :: _ -> raise (ParseError ("Expected `,` or `)`, got " ^ tok_to_str x))
    | [] -> raise (ParseError ("Expected `,` or `)`, got end of input"))
  in
    parse_expr_toplevel lst
(* match lst with *)
(*   | Let :: _ -> failwith "stub" *)
(*   | If :: r -> let (c, r2) = parse_expr r in *)
(*     (match r2 with *)
(*       | Then :: r3 -> let (t, r4) = parse_expr r3 in *)
(*         (match r4 with *)
(*           | Else :: r5 -> let (f, rest) = parse_expr r5 in *)
(*             (IfExpr (c, t, f), rest) *)
(*           | x :: _ -> raise (ParseError ("Expected `else`, got " ^ tok_to_str x)) *)
(*           | [] -> raise (ParseError ("Expected `else`, got end of input"))) *)
(*       | x :: _ -> raise (ParseError ("Expected `then`, got " ^ tok_to_str x)) *)
(*       | [] -> raise (ParseError ("Expected `then`, got end of input"))) *)
(*   | Fun :: _ -> failwith "stub" *)
(*   (* applicaiton *) *)
(*   (* tuples *) *)
(*   (* binops *) *)
(*   | Not :: r -> let (e, rest) = parse_expr r in (UnopExpr (Not, e), rest) *)
(*   | Negate :: r -> let (e, rest) = parse_expr r in (UnopExpr (Negate, e), rest) *)
(*   (* expr in parens *) *)
(*   | Int i :: rest -> (IntLiteralExpr i, rest) *)
(*   | True :: rest -> (BoolLiteralExpr true, rest) *)
(*   | False :: rest -> (BoolLiteralExpr false, rest) *)
(*   | String s :: rest -> (StringLiteralExpr s, rest) *)
(*   | Id x :: rest -> (VarExpr x, rest) *)
(*   | LParen :: RParen :: rest -> (UnitExpr, rest) *)
(*   | Match :: r -> let (e, r2) = parse_expr r in *)
(*     (match r2 with *)
(*       | With :: r3 -> let (brs, rest) = parse_match_branches [] r3 in *)
(*         (MatchExpr (e, List.rev brs), rest) *)
(*       | x :: _ -> raise (ParseError ("Expected `with`, got " ^ tok_to_str x)) *)
(*       | [] -> raise (ParseError ("Expected `with`, got end of input"))) *)
(*   | x :: _ -> raise (ParseError ("Expected expr, got " ^ tok_to_str x)) *)
(*   | [] -> raise (ParseError ("Expected expr, got end of input")) *)
and parse_match_branches (branches: match_branch list) (lst: token list): match_branch list * token list =
  match lst with
  | Pipe :: Id x :: Id y :: DoubleArrow :: r ->
      let (e, rest) = parse_expr r in
        parse_match_branches (MatchBranch (x, Some(SinglePatternVar y), e) :: branches) rest
  | Pipe :: Id x :: LParen :: r ->
      let rec help (toks: token list): string list * token list =
        match toks with
        | RParen :: rest -> ([], rest)
        | Comma :: Id x :: r -> let (subsequent, rest) = help r in
            (x :: subsequent, rest)
        | Id x :: r -> let (subsequent, rest) = help r in
            (x :: subsequent, rest)
        | x :: _ -> raise (ParseError ("Token " ^ tok_to_str x ^ " is invalid inside the pattern vars of a match branch"))
        | [] -> raise (ParseError ("Pattern vars in a match branch must be closed by `)`"))
      in
        let (pv, r2) = help r in
          (match r2 with
          | DoubleArrow :: r3 -> let (e, rest) = parse_expr r3 in
            parse_match_branches (MatchBranch (x, Some(MultiplePatternVars pv), e) :: branches) rest
          | x :: _ -> raise (ParseError ("Expected `=>`, got " ^ tok_to_str x))
          | [] -> raise (ParseError ("Expected `=>`, got end of input")))
  | Pipe :: Id x :: DoubleArrow :: r ->
      let (e, rest) = parse_expr r in
        parse_match_branches (MatchBranch (x, None, e) :: branches) rest
  | Pipe :: Id _ :: x :: _ -> raise (ParseError ("Expected either pattern vars or `=>`, got " ^ tok_to_str x))
  | Pipe :: Id _ :: _ -> raise (ParseError ("Expected either pattern vars or `=>`, got end of input"))
  | Pipe :: x :: _ -> raise (ParseError ("Expected match case, got " ^ tok_to_str x))
  | [Pipe] -> raise (ParseError ("Expected match case, got end of input"))
  | _ -> (branches, lst)
and parse_type (lst: token list): typ * token list =
  let rec parse_function_type (toks: token list): typ * token list =
    let (first, r) = parse_tuple_type toks in
      match r with
      | Arrow :: r2 -> let (others, rest) = parse_function_type r2 in
        (FunctionType (first, others), rest)
      | _ -> (first, r)
    (* let rec help ex = function *)
    (*   | Arrow :: r -> *)
    (*     let (e, rest) = parse_tuple_type r in *)
    (*     help (FunctionType (ex, e)) rest *)
    (*   | ts -> (ex, ts) in *)
    (* let (e, r) = parse_tuple_type toks  in *)
    (* help e r *)
  and parse_tuple_type (toks: token list): typ * token list =
    (* let rec help ex = function *)
    (*   | Times :: r -> *)
    (*     let (e, rest) = parse_tuple_type r in *)
    (*     help (FunctionType (ex, e)) rest (* TODO: actually use tuple type *) *)
    (*   | ts -> (ex, ts) in *)
    (* let (e, r) = parse_base_type toks  in *)
    (* help e r *)
    let rec help (s: token list): typ list * token list =
      match s with
      | Times :: r ->
          let (t, r2) = parse_base_type r in
            let (subsequent, rest) = help r2 in
              (t :: subsequent, rest)
      | _ -> ([], s)
    in
      let (first, r) = parse_base_type toks in
        let (subtypes, rest) = help r in
          match subtypes with
            | [] -> (first, rest)
            | _ -> (TupleType (first :: subtypes), rest)
  and parse_base_type (toks: token list): typ * token list =
    match toks with
    | LParen :: r -> let (t, r2) = parse_function_type r in
      (match r2 with
        | RParen :: rest -> (t, rest)
        | x :: _ -> raise (ParseError ("Expected `)`, got " ^ tok_to_str x))
        | [] -> raise (ParseError ("Expected `)`, got end of input")))
    | TInt :: rest -> (IntType, rest)
    | TBool :: rest -> (BoolType, rest)
    | TString :: rest -> (StringType, rest)
    | TUnit :: rest -> (UnitType, rest)
    | Id x :: rest -> (UserDeclaredType x, rest)
    | x :: _ -> raise (ParseError ("Expected type, got " ^ tok_to_str x))
    | [] -> raise (ParseError ("Expected type, got end of input"))
  in
    parse_function_type lst

let parse (lst: token list): program =
  match lst with
  | [] -> raise (ParseError ("Cannot parse an empty program"))
  | _ ->
    let (prog, rest) = parse_program lst in
      match rest with
      | [] -> prog
      | x :: _ -> raise (ParseError ("Expected end of file, got " ^ tok_to_str x))
