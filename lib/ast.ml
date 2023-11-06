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
  | Exp
  | And
  | Or

and unop =
  | Not
  | Negate

and typ =
  | FunctionType of typ * typ
  (* | ParenType of type (* unnecessary — the nested typ goes in the AST directly *) *)
  | TupleType of typ list (* must have two or more items *)
  | IntType
  | BoolType
  | StringType
  | UnitType
  | UserDeclaredType of string

and match_branch =
  | MatchBranch of string * pattern_vars option * expr
  (* If I want to support matching on literals, this needs to not be a string *)

and pattern_vars =
  | SinglePatternVar of string
  | MultiplePatternVars of string list

let rec string_of_typ (t: typ): string =
  match t with
  | FunctionType (arg, out) -> "(" ^ string_of_typ arg ^ ") -> (" ^ string_of_typ out ^ ")"
  | TupleType lst -> List.map (function a -> "(" ^ string_of_typ a ^ ")") lst |> String.concat " * "
  | IntType -> "int"
  | BoolType -> "bool"
  | StringType -> "string"
  | UnitType -> "unit"
  | UserDeclaredType x -> x

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
