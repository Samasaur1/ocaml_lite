open Ast

type value =
  | IntLiteral of int
  | StringLiteral of string
  | BoolLiteral of bool
  | UnitValue
  | TupleValue of value list
  | ClosureValue of string list * environment * expr * string option
  | UserValue of string * value list
  | ConstructorValue of string
  | BuiltinValue of (value -> value)
and environment = (string * value) list

let rec interpret (p: program): environment =
  let Program(bds) = p in

  let env = List.fold_left
    interpret_binding
    [("string_of_int", BuiltinValue (fun x -> let IntLiteral i = x in StringLiteral (string_of_int i))); ("int_of_string", BuiltinValue (fun x -> let StringLiteral s = x in IntLiteral (int_of_string s))); ("print_string", BuiltinValue (fun x -> let StringLiteral s = x in let _ = print_endline s in UnitValue))]
    bds
  in
  env
and interpret_binding (env: environment) (b: binding): environment =
  match b with
  | NonRecursiveBinding (name, params, ty, value) ->
    let evaluated_value = 
      match params with
      | [] -> interpret_expr env value
      | _ -> ClosureValue (List.map (fun x -> match x with UntypedParam p -> p | TypedParam (p, _) -> p) params, env, value, None)
    in
      (name, evaluated_value) :: env
  | RecursiveBinding (name, params, ty, value) ->
    let evaluated_value =
      match params with
      | [] -> interpret_expr env value
      | _ -> ClosureValue (List.map (fun x -> match x with UntypedParam p -> p | TypedParam (p, _) -> p) params, env, value, Some name)
    in
     (name, evaluated_value) :: env
  | TypeDefBinding (_name, constructors) ->
    (List.map
      (fun x -> match x with
        | (cons, None) -> (cons, UserValue (cons, []))
        | (cons, Some _ty) -> (cons, ConstructorValue cons)
      )
      constructors
    ) @ env
and interpret_expr (env: environment) (e: expr): value =
  match e with
  | LetExpr (name, params, _ty, value, body) ->
    let evaluated_value = 
      match params with
      | [] -> interpret_expr env value
      | _ -> ClosureValue (List.map (fun x -> match x with UntypedParam p -> p | TypedParam (p, _) -> p) params, env, value, None)
      (* | first :: rest -> *)
      (*   let param_name = match first with *)
      (*     | UntypedParam x -> x *)
      (*     | TypedParam (x, _) -> x *)
      (*   in *)
      (*   ClosureValue (param_name, env, value, None) *)
    in
    interpret_expr ((name, evaluated_value) :: env) body
  | LetRecExpr (name, params, _ty, value, body) ->
    let evaluated_value =
      match params with
      | [] -> interpret_expr env value
      | _ -> ClosureValue (List.map (fun x -> match x with UntypedParam p -> p | TypedParam (p, _) -> p) params, env, value, Some name)
    in
    interpret_expr ((name, evaluated_value) :: env) body
  | IfExpr (cond, iftrue, iffalse) ->
    let cond_val = interpret_expr env cond in
    let BoolLiteral b = cond_val in
    if b then interpret_expr env iftrue else interpret_expr env iffalse
  | FunDefExpr (params, ty, body) ->
    ClosureValue (List.map (fun x -> match x with UntypedParam p -> p | TypedParam (p, _) -> p) params, env, body, None)
  | FunAppExpr (l, r) ->
    let fn = interpret_expr env l in
    let arg = interpret_expr env r in
    (match fn with
      | BuiltinValue f -> f arg
      | ClosureValue (params, closure_env, body_expr, rec_name) -> (match params with
        | [] -> failwith "Function does not accept any params"
        | [p] -> interpret_expr ((p, interpret_expr env r) :: (match rec_name with None -> [] | Some n -> [(n, fn)]) @ closure_env @ env) body_expr
        | first :: rest -> ClosureValue (rest, (first, arg) :: closure_env, body_expr, rec_name)
      )
      | ConstructorValue name -> (match interpret_expr env r with
        | TupleValue lst -> UserValue (name, lst)
        | v -> UserValue (name, [v])
      )
      | _ -> failwith "Not a function type"
    )
  | TupleExpr (elements) ->
    TupleValue (List.map (interpret_expr env) elements)
  | BinopExpr (l, op, r) -> let l = interpret_expr env l in let r = interpret_expr env r in
    (match op with
      | Plus -> let IntLiteral l = l in let IntLiteral r = r in IntLiteral (l + r)
      | Minus -> let IntLiteral l = l in let IntLiteral r = r in IntLiteral (l - r)
      | Times -> let IntLiteral l = l in let IntLiteral r = r in IntLiteral (l * r)
      | Divide -> let IntLiteral l = l in let IntLiteral r = r in IntLiteral (l / r)
      | Modulo -> let IntLiteral l = l in let IntLiteral r = r in IntLiteral (l mod r)
      | LessThan -> let IntLiteral l = l in let IntLiteral r = r in BoolLiteral (l < r)
      | Equal -> (match (l, r) with
        | IntLiteral l, IntLiteral r -> BoolLiteral (l = r)
        | BoolLiteral l, BoolLiteral r -> BoolLiteral (l = r)
        | StringLiteral l, StringLiteral r -> BoolLiteral (l = r)
        | _ -> failwith "stub"
      )
      | Concat -> let StringLiteral l = l in let StringLiteral r = r in StringLiteral (l ^ r)
      | And -> let BoolLiteral l = l in let BoolLiteral r = r in BoolLiteral (l && r)
      | Or -> let BoolLiteral l = l in let BoolLiteral r = r in BoolLiteral (l || r)
    )
  | UnopExpr (op, arg) -> let arg = interpret_expr env arg in
    (match op with
      | NegateInt -> let IntLiteral i = arg in IntLiteral (-i)
      | InvertBool -> let BoolLiteral b = arg in BoolLiteral (not b)
    )
  | IntLiteralExpr i -> IntLiteral i
  | BoolLiteralExpr b -> BoolLiteral b
  | StringLiteralExpr s -> StringLiteral s
  | VarExpr v -> 
    (match List.assoc_opt v env with
      | None -> failwith ("Variable  " ^ v ^ " is not defined")
      | Some v -> v
    )
  | UnitExpr -> UnitValue
  | MatchExpr (matchval, branches) ->
    (match interpret_expr env matchval with
      | UserValue (constructor, value_list) -> (
        let mapped_branches = List.map (fun b -> let MatchBranch (cons, plo, rhs) = b in (cons, (plo, rhs))) branches in
        let (pattern_vars_option, rhs) = match List.assoc_opt constructor mapped_branches with
          | None -> failwith "No matching match branch"
          | Some (pvs', rhs) -> (pvs', rhs)
        in
        match (pattern_vars_option, value_list) with
        | (None, []) -> interpret_expr env rhs
        | (None, _) -> failwith "Invalid match branch case"
        | (Some (SinglePatternVar pv), [v]) -> interpret_expr ((pv, v) :: env) rhs
        | (Some (SinglePatternVar _), _) -> failwith "Invalid match branch case"
        | (Some (MultiplePatternVars _), []) -> failwith "Invalid match branch case"
        | (Some (MultiplePatternVars _), [_]) -> failwith "Invalid match branch case"
        | (Some (MultiplePatternVars pvs), vs) -> interpret_expr ((List.combine pvs vs) @ env) rhs
      )
      | _ -> failwith "You can only match on user-defined types"
    )
