type program = 
  | Program of binding list

and binding =
  | NonRecursiveBinding of string * param list * typ option * expr
  | RecursiveBinding of string * param list * typ option * expr
  | TypeDefBinding of string * (string * typ option) list

and param =
  | UntypedParam of string
  | TypedParam of string * typ

and expr =
  | LetExpr of string * param list * typ option * expr * expr
  | LetRecExpr of string * param list * typ option * expr * expr
  | IfExpr of expr * expr * expr
  | FunDefExpr of param list * typ option * expr
  | FunAppExpr of expr * expr
  | TupleExpr of expr list (* must have two or more items *)
  | BinopExpr of expr * binop * expr
  | UnopExpr of unop * expr
  (* | ParenExpr of expr (* unnecessary — the nested expr goes in the AST directly *) *)
  | IntLiteralExpr of int
  | BoolLiteralExpr of bool (* handles both true and false *)
  | StringLiteralExpr of string
  | VarExpr of string
  | UnitExpr
  | MatchExpr of expr * match_branch list

and binop =
  | Plus
  | Minus
  | Times
  | Divide
  | Modulo
  | LessThan
  | Equal
  | Concat
  | And
  | Or

and unop =
  (* | Not (* `not` — inverting booleans *) *)
  (* | Negate (* `~` — negating integers *) *)
  | InvertBool (* `not` *)
  | NegateInt (* `~` *)

and typ =
  | FunctionType of typ * typ
  (* | ParenType of type (* unnecessary — the nested typ goes in the AST directly *) *)
  | TupleType of typ list (* must have two or more items *)
  | IntType
  | BoolType
  | StringType
  | UnitType
  | UserDeclaredType of string
  | TypeVariable of int
  | Polytype of int * typ

and match_branch =
  | MatchBranch of string * pattern_vars option * expr
  (* If I want to support matching on literals, this needs to not be a string *)

and pattern_vars =
  | SinglePatternVar of string
  | MultiplePatternVars of string list

let repeat n s = 
  let rec helper s1 n1 = 
    if n1 = 0 then s1 else helper (s1 ^ s) (n1 - 1)
  in helper "" n

let rec string_of_typ (t: typ): string =
  match t with
  | FunctionType (arg, out) -> "(" ^ string_of_typ arg ^ ") -> (" ^ string_of_typ out ^ ")"
  | TupleType lst -> List.map (function a -> "(" ^ string_of_typ a ^ ")") lst |> String.concat " * "
  | IntType -> "int"
  | BoolType -> "bool"
  | StringType -> "string"
  | UnitType -> "unit"
  | UserDeclaredType x -> x
  | TypeVariable i -> "t" ^ string_of_int i
  | Polytype (i, p) -> "forall t" ^ string_of_int i ^ ". " ^ string_of_typ p


let rec string_of_program (indent: int) (p: program): string =
  match p with
  | Program bds -> "Program [\n" ^ ((List.map (string_of_binding 1) bds) |> (String.concat ",\n")) ^ "\n]"
and string_of_binding (indent: int) (bd: binding): string =
  match bd with
  | NonRecursiveBinding (name, params, ty, value) ->
      (repeat indent " ") ^ "let " ^ name ^ " " ^ ((List.map string_of_param params) |> (String.concat " ")) ^ ": <type> = " ^ string_of_expr value ^ ";;"
  | RecursiveBinding (name, params, ty, value) ->
      (repeat indent " ") ^ "let rec " ^ name ^ " " ^ ((List.map string_of_param params) |> (String.concat " ")) ^ ": <type> = " ^ string_of_expr value ^ ";;"
  | TypeDefBinding (name, constructors) ->
      (repeat indent " ") ^ "type " ^ name ^ " = " ^ ((List.map (function | (s, None) -> "| " ^ s | (s, Some t) -> "| " ^ s ^ " of " ^ string_of_typ t) constructors) |> (String.concat " ")) ^ ";;"
and string_of_param (p: param): string =
  match p with
  | UntypedParam x -> x
  | TypedParam (x, t) -> "(" ^ x ^ ": " ^ string_of_typ t ^ ")"
and string_of_expr (e: expr): string =
  match e with
  | LetExpr (name', params', type', value', in') -> "let " ^ name' ^ " " ^ ((List.map string_of_param params') |> String.concat " ") ^ ": <type> = " ^ string_of_expr value' ^ " in " ^ string_of_expr in'
  | LetRecExpr (name', params', type', value', in') -> "let rec " ^ name' ^ " " ^ ((List.map string_of_param params') |> String.concat " ") ^ ": <type> = " ^ string_of_expr value' ^ " in " ^ string_of_expr in'
  | IfExpr (c, t, f) -> "if " ^ string_of_expr c ^ " then " ^ string_of_expr t ^ " else " ^ string_of_expr f
  | FunDefExpr (params, ty, body) -> "fun " ^ (List.map string_of_param params |> String.concat ", ") ^ ": <type> => " ^ string_of_expr body
  | FunAppExpr (fn, arg) -> "(" ^ string_of_expr fn ^ ") (" ^ string_of_expr arg ^ ")"
  | TupleExpr (members) -> "(" ^ (List.map string_of_expr members |> String.concat ", ") ^ ")"
  | BinopExpr (l, op, r) -> "(" ^ string_of_expr l ^ ") op (" ^ string_of_expr r ^ ")"
  | UnopExpr (op, e) -> "op (" ^ string_of_expr e ^ ")"
  | IntLiteralExpr i -> string_of_int i
  | BoolLiteralExpr b -> string_of_bool b
  | StringLiteralExpr s -> "\"" ^ s ^ "\""
  | VarExpr v -> v
  | UnitExpr -> "()"
  | MatchExpr (e, branches) -> "match " ^ string_of_expr e ^ " with " ^ ((List.map string_of_branch branches) |> (String.concat " "))
and string_of_branch (b: match_branch): string = 
  match b with
    | MatchBranch (first, None, value) -> "| " ^ first ^ " => " ^ string_of_expr value
    | MatchBranch (first, Some (SinglePatternVar s), value) -> "| " ^ first ^ " " ^ s ^ " => " ^ string_of_expr value
  | MatchBranch (first, Some (MultiplePatternVars ss), value) -> "| " ^ first ^ " (" ^ (String.concat ", " ss) ^ ") => " ^ string_of_expr value

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
