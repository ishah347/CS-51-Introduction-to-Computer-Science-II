(* 
                         CS 51 Final Project
                        MiniML -- Expressions
                             Spring 2018
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
;;

type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Bool of bool                         (* booleans *)
  | Unit of unit                         (* units *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
 and varid = string 
 ;;
  
(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let rec free_vars (exp : expr) : varidset =
  let open SS in
    match exp with
    | Var(v) -> add v empty
    | Unop(_, e) -> free_vars e
    | Binop(_, e1, e2) | App(e1, e2) -> union (free_vars e1) (free_vars e2)
    | Conditional(e1, e2, e3) -> union (union (free_vars e1) (free_vars e2)) (free_vars e3)
    | Fun (v, e) -> remove v (free_vars e)
    | Let(v, e1, e2) ->
        union (free_vars e1) (remove v (free_vars e2))
    | Letrec(v, e1, e2) -> 
        remove v (union (free_vars e1) (free_vars e2))
    | _ -> empty ;;     
      
(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)
let new_varname : unit -> varid =
  let ctr = ref 0 in
  fun () -> 
    let v = "var" ^ string_of_int (!ctr) in
    incr ctr;
    v ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let fresh = new_varname () in
  let rec subst' exp' =
    match exp' with
    | Var(v) -> if v = var_name then repl else exp'
    | Unop(u, e) -> Unop(u, subst' e) 
    | Binop(bi, e1, e2) ->
        let subst1 = subst' e1 in
        let subst2 = subst' e2 in
        Binop(bi, subst1, subst2)
    | Conditional(e1, e2, e3) ->
        let subst1 = subst' e1 in
        let subst2 = subst' e2 in
        let subst3 = subst' e3 in
        Conditional(subst1, subst2, subst3)
    | Fun(v, e) -> 
        if v = var_name then exp'
        else if not (SS.mem v (free_vars repl)) then Fun(v, subst' e)
        else Fun(fresh, subst' (subst v (Var(fresh)) e))
    | Let(v, e1, e2) -> 
        if v = var_name then Let(v, subst' e1, e2)
        else if not (SS.mem v (free_vars repl)) then 
          Let(v, subst' e1, subst' e2)
        else Let(fresh, subst' e1, 
                 subst' (subst v (Var(fresh)) e2))
    | Letrec(v, e1, e2) ->
        if v = var_name then Letrec(v, subst' e1, e2)
        else if not (SS.mem v (free_vars repl)) then 
          Letrec(v, subst' e1, subst' e2)
        else Letrec(fresh, subst' e1, 
                    subst' (subst v (Var(fresh)) e2))
    | App (e1, e2) -> App(subst' e1, subst' e2)
    | _ -> exp' in 
subst' exp ;;

(*......................................................................
  String representations of expressions
 *)
   
    
(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let exp_to_concrete_string (exp : expr) : string =
  let rec exp_to_concrete_string' exp' = 
    match exp' with
    | Var(v) -> v
    | Num(i) -> string_of_int i
    | Bool(b) -> string_of_bool b
    | Unit(_) -> "()"
    | Unop(u, e) -> 
        let unop_string = 
          match u with
          | Negate -> "~- " in
        unop_string ^ "(" ^ exp_to_concrete_string' e ^ ")"
    | Binop(bi, e1, e2) ->
        let binop_string = 
          match bi with
          | Plus -> " + "
          | Minus -> " - "
          | Times -> " * "
          | Equals -> " = "
          | LessThan -> " < " in
        let exp_string e = "(" ^ exp_to_concrete_string' e ^ ")" in  
        exp_string e1 ^ binop_string ^ exp_string e2
    | Conditional(e1, e2, e3) -> 
        let exp1 = exp_to_concrete_string' e1 in
        let exp2 = exp_to_concrete_string' e2 in
        let exp3 = exp_to_concrete_string' e3 in 
        "if " ^ exp1 ^ " then " ^ exp2 ^ " else " ^ exp3
    | Fun(v, e) -> "fun " ^ v ^ " -> " ^ exp_to_concrete_string' e
    | Let(v, e1, e2) -> 
        let exp1 = exp_to_concrete_string' e1 in
        let exp2 = exp_to_concrete_string' e2 in
        "let " ^ v ^ " = " ^ exp1 ^ " in " ^ exp2
    | Letrec(v, e1, e2) -> exp_to_concrete_string' (Let(("rec " ^ v), e1, e2))
    | Raise -> "raise"
    | Unassigned -> "unassigned"
    | App(e1, e2) -> 
        exp_to_concrete_string' e1 ^ " " ^ exp_to_concrete_string' e2 in
  exp_to_concrete_string' exp ^ " ;;" ;;       

(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  let exp_to_abstract_string' exp' =
    match exp' with
    | Var(v) -> "Var(" ^ v
    | Num(i) -> "Num(" ^ string_of_int i
    | Bool(b) -> "Bool(" ^ string_of_bool b
    | Unit(_) -> "Unit(()"
    | Unop(u, e) -> 
        let unop_string = 
          match u with
          | Negate -> "Negate, " in
        "Unop(" ^ unop_string ^ exp_to_abstract_string e
    | Binop(bi, e1, e2) ->
        let binop_string = 
          match bi with
          | Plus -> "Plus"
          | Minus -> "Minus"
          | Times -> "Times"
          | Equals -> "Equals"
          | LessThan -> "LessThan" in
        let exp1 = exp_to_abstract_string e1 in
        let exp2 = exp_to_abstract_string e2 in  
        "Binop(" ^ binop_string ^ ", " ^ exp1 ^ ", " ^ exp2
    | Conditional(e1, e2, e3) ->     
        let exp1 = exp_to_abstract_string e1 in
        let exp2 = exp_to_abstract_string e2 in 
        let exp3 = exp_to_abstract_string e3 in
        "Conditional(" ^ exp1 ^ ", " ^ exp2 ^ ", " ^ exp3
    | Fun(v, e) -> "Fun(" ^ v ^ ", " ^ exp_to_abstract_string e
    | Let(v, e1, e2) -> 
        let exp1 = exp_to_abstract_string e1 in
        let exp2 = exp_to_abstract_string e2 in 
        "Let(" ^ v ^ ", " ^ exp1 ^ ", " ^ exp2
    | Letrec(v, e1, e2) -> 
        let exp1 = exp_to_abstract_string e1 in
        let exp2 = exp_to_abstract_string e2 in 
        "Letrec(" ^ v ^ ", " ^ exp1 ^ ", " ^ exp2 
    | Raise -> "(Raise"
    | Unassigned -> "(Unassigned"
    | App(e1, e2) ->
        let exp1 = exp_to_abstract_string e1 in
        let exp2 = exp_to_abstract_string e2 in 
        "App(" ^ exp1 ^ ", " ^ exp2 in
  exp_to_abstract_string' exp ^ ")" ;;