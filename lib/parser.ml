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
      | x :: _ -> raise (ParseError ("Expected `;;`, got " ^ tok_to_str x))
      | [] -> raise (ParseError ("Expected `;;`, got end of input"))
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
and parse_let_binding_common (x: string) (r: token list): binding * token list =
  let rec help (rr: param list) (toks: token list): param list * token list =
    match toks with
    | Colon :: _ | Eq :: _ -> (rr, toks)
    | Id p :: r2 -> help ((UntypedParam p) :: rr) r2
    (* | Id p :: r2 -> ((UntypedParam p) :: rr, r2) *)
    | LParen :: Id p :: Colon :: r2 ->
      let (t, r3) = parse_type r2 in
        (match r3 with
        | RParen :: r4 -> help (TypedParam (p, t) :: rr) r4
        | x :: _ -> raise (ParseError ("Expected closing paren, got " ^ tok_to_str x))
        | [] -> raise (ParseError ("Expected closing paren, got end of input")))
    | x :: _ -> raise (ParseError ("Expected param, got " ^ tok_to_str x))
    | [] -> raise (ParseError ("Expected param, got end of input"))
  in
    let (params, r2) = help [] r in
      match r2 with
      | Colon :: r3 ->
        let (t, r4) = parse_type r3 in
          (match r4 with
          | Eq :: r5 ->
            let (e, rest) = parse_expr r5 in
              (NonRecursiveBinding (x, params, Some(t), e), rest)
          | x :: _ -> raise (ParseError ("Expected `=`, got " ^ tok_to_str x))
          | [] -> raise (ParseError ("Expected `=`, got end of input")))
      | Eq :: r3 ->
        let (e, rest) = parse_expr r3 in
          (NonRecursiveBinding (x, params, None, e), rest)
      | x :: _ -> raise (ParseError ("Expected either `:` or `=`, got " ^ tok_to_str x))
      | [] -> raise (ParseError ("Expected either `:` or `=`, got end of input"))
and parse_nonrec_binding (lst: token list): binding * token list =
  match lst with
  | Let :: Id x :: r -> parse_let_binding_common x r
  | _ -> failwith "Unreachable"
and parse_rec_binding (lst: token list): binding * token list =
  match lst with
  | Let :: Rec :: Id x :: r -> parse_let_binding_common x r
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
          (TypeDefBinding (x, List.rev brs), rest)
  )
  | Type :: Id _ :: x :: _ -> raise (ParseError ("Expected `=`, got " ^ tok_to_str x))
  | Type :: x :: _ -> raise (ParseError ("Expected type name, got " ^ tok_to_str x))
  | _ -> failwith "Unreachable"
and parse_expr (lst: token list): expr * token list =
  match lst with
    | Let :: _ -> failwith "stub"
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
    | Fun :: _ -> failwith "stub"
    (* applicaiton *)
    (* tuples *)
    (* binops *)
    | Not :: r -> let (e, rest) = parse_expr r in (UnopExpr (Not, e), rest)
    | Negate :: r -> let (e, rest) = parse_expr r in (UnopExpr (Negate, e), rest)
    (* expr in parens *)
    | Int i :: rest -> (IntLiteralExpr i, rest)
    | True :: rest -> (BoolLiteralExpr true, rest)
    | False :: rest -> (BoolLiteralExpr false, rest)
    | String s :: rest -> (StringLiteralExpr s, rest)
    | Id x :: rest -> (VarExpr x, rest)
    | LParen :: RParen :: rest -> (UnitExpr, rest)
    | Match :: r -> let (e, r2) = parse_expr r in
      (match r2 with
        | With :: r3 -> let (brs, rest) = parse_match_branches [] r3 in
          (MatchExpr (e, List.rev brs), rest)
        | x :: _ -> raise (ParseError ("Expected `with`, got " ^ tok_to_str x))
        | [] -> raise (ParseError ("Expected `with`, got end of input")))
    | x :: _ -> raise (ParseError ("Expected expr, got " ^ tok_to_str x))
    | [] -> raise (ParseError ("Expected expr, got end of input"))
and parse_match_branches (branches: match_branch list) (lst: token list): match_branch list * token list =
  match lst with
  | Pipe :: Id x :: Id y :: DoubleArrow :: r ->
      let (e, rest) = parse_expr r in
        parse_match_branches (MatchBranch (x, Some(SinglePatternVar y), e) :: branches) rest
  | Pipe :: Id x :: LParen :: r ->
      let rec help (rr: string list) (toks: token list): string list * token list =
        match toks with
        | RParen :: rest -> (rr, rest)
        | Comma :: Id x :: rest -> help (x :: rr) rest
        | Id x :: rest -> help (x :: rr) rest
        | x :: _ -> raise (ParseError ("Token " ^ tok_to_str x ^ " is invalid inside the pattern vars of a match branch"))
        | [] -> raise (ParseError ("Pattern vars in a match branch must be closed by `)`"))
      in
        let (pv, r2) = help [] r in
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
    let rec help ex = function
      | Arrow :: r ->
        let (e, rest) = parse_tuple_type r in
        help (FunctionType (ex, e)) rest
      | ts -> (ex, ts) in
    let (e, r) = parse_tuple_type toks  in
    help e r
  and parse_tuple_type (toks: token list): typ * token list =
    let rec help ex = function
      | Times :: r ->
        let (e, rest) = parse_tuple_type r in
        help (FunctionType (ex, e)) rest
      | ts -> (ex, ts) in
    let (e, r) = parse_base_type toks  in
    help e r
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
