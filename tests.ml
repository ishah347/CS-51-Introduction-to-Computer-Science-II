(* 
                         CS 51 Final Project
                        MiniML -- Expressions
                             Spring 2018
*)

(*......................................................................
  Testing for the final project 
 *)

open Expr ;;
open Evaluation ;;
open Miniml_parse ;;
open Miniml_lex ;;
open Miniml ;; 

let _ =
  assert(exp_to_concrete_string (Var("x")) = "x ;;"); 
  assert(exp_to_concrete_string (Num(1)) = "1 ;;"); 
  assert(exp_to_concrete_string (Bool(false)) = "false ;;"); 
  assert(exp_to_concrete_string (Unit(())) = "() ;;"); 
  assert(exp_to_concrete_string (Unop(Negate, Num(1))) = "~- (1) ;;");
  assert(exp_to_concrete_string (Binop(Plus, Num(2), Num(3))) 
  	= "(2) + (3) ;;");
  assert(exp_to_concrete_string (Conditional(Bool(true), Num(5), Num(6))) 
  	= "if true then 5 else 6 ;;");
  assert(exp_to_concrete_string (Fun("x", Num(7))) = "fun x -> 7 ;;");
  assert(exp_to_concrete_string (Let("x", Num(7), Bool(true)))
    = "let x = 7 in true ;;");
  assert(exp_to_concrete_string (Letrec("x", Num(7), Bool(true))) 
  	= "let rec x = 7 in true ;;");
  assert(exp_to_concrete_string (Raise) = "raise ;;");
  assert(exp_to_concrete_string (Unassigned) = "unassigned ;;");
  assert(exp_to_concrete_string (App(Var("y"), Num(1111))) = "y 1111 ;;");
  assert(exp_to_abstract_string (Var("x")) = "Var(x)"); 
  assert(exp_to_abstract_string (Num(1)) = "Num(1)"); 
  assert(exp_to_abstract_string (Bool(false)) = "Bool(false)"); 
  assert(exp_to_abstract_string (Unit(())) = "Unit(())"); 
  assert(exp_to_abstract_string (Unop(Negate, Num(1))) 
  	= "Unop(Negate, Num(1))");
  assert(exp_to_abstract_string (Binop(Plus, Num(2), Num(3))) 
  	= "Binop(Plus, Num(2), Num(3))");
  assert(exp_to_abstract_string (Conditional(Bool(true), Num(5), Num(6))) 
  	= "Conditional(Bool(true), Num(5), Num(6))");
  assert(exp_to_abstract_string (Fun("x", Num(7))) = "Fun(x, Num(7))");
  assert(exp_to_abstract_string (Let("x", Num(7), Bool(true)))
    = "Let(x, Num(7), Bool(true))");
  assert(exp_to_abstract_string (Letrec("x", Num(7), Bool(true))) 
  	= "Letrec(x, Num(7), Bool(true))");
  assert(exp_to_abstract_string (Raise) = "(Raise)");
  assert(exp_to_abstract_string (Unassigned) = "(Unassigned)");
  assert(exp_to_abstract_string (App(Var("y"), Num(1111))) = 
  	"App(Var(y), Num(1111))");
  assert(same_vars (free_vars (Var("x"))) (vars_of_list ["x"])); 
  assert(same_vars (free_vars (Unop(Negate, Var("x")))) (vars_of_list ["x"]));
  assert(same_vars (free_vars (Binop(Plus, Var("x"), Var("y")))) 
  	                          (vars_of_list ["x"; "y"]));
  assert(same_vars (free_vars (Conditional(Var("x"), Var("y"), Var("z"))))
  	                          (vars_of_list ["x"; "y"; "z"]));
  assert(same_vars (free_vars (Fun("x", Binop(Plus, Var("x"), Var("y")))))
  	                          (vars_of_list ["y"]));
  assert(same_vars (free_vars (Fun("x", Unop(Negate, Var("x")))))
  	                          (vars_of_list []));
  assert(same_vars (free_vars (Let("x", Unop(Negate, Var("x")), 
  	                           Unop(Negate, Var("x"))))) (vars_of_list ["x"]));
  assert(same_vars (free_vars (Let("x", Unop(Negate, Var("y")), 
  	                           Unop(Negate, Var("x"))))) (vars_of_list ["y"]));
  assert(same_vars (free_vars (Letrec("x", Unop(Negate, Var("x")), 
  	                            Unop(Negate, Var("x"))))) (vars_of_list []));
  assert(same_vars (free_vars (Letrec("x", Binop(Plus, Var("x"), Var("y")), 
  	                           Unop(Negate, Var("x"))))) (vars_of_list ["y"]));
  assert(same_vars (free_vars (Num(1))) (vars_of_list [])); 
  let varlist = ["x"; "y"; "z"] in
  let repl = Var("z") in 
  assert(List.map (fun v -> subst v repl (Var("x"))) varlist
    = [(Var("z")); (Var("x")); (Var("x"))]);
  assert(List.map (fun v -> subst v repl (Unop(Negate, Var("x")))) varlist
    = [(Unop(Negate, Var("z"))); (Unop(Negate, Var("x"))); 
       (Unop(Negate, Var("x")))]);
  assert(List.map (fun v -> 
  	                 subst v repl (Binop(Plus, Var("x"), Var("y")))) varlist
    = [(Binop(Plus, Var("z"), Var("y"))); (Binop(Plus, Var("x"), Var("z"))); 
       (Binop(Plus, Var("x"), Var("y")))]);
  assert(List.map 
  	      (fun v -> 
  	        subst v repl (Conditional(Var("x"), Var("y"), Var("z")))) varlist
    = [(Conditional(Var("z"), Var("y"), Var("z"))); 
       (Conditional(Var("x"), Var("z"), Var("z"))); 
       (Conditional(Var("x"), Var("y"), Var("z")))]);
  assert(List.map (fun v -> 
  	                 subst v repl (Fun("x", Var("y")))) varlist
    = [(Fun("x", Var("y"))); (Fun("x", Var("z"))); (Fun("x", Var("y")))]);
  assert(List.map (fun v -> 
  	                 subst v repl (Let("x", Var("y"), Var("z")))) varlist
    = [(Let("x", Var("y"), Var("z"))); (Let("x", Var("z"), Var("z")));
       (Let("x", Var("y"), Var("z")))]);
  assert(List.map (fun v -> 
  	                 subst v repl (Letrec("x", Var("y"), Var("z")))) varlist
    = [(Letrec("x", Var("y"), Var("z"))); (Letrec("x", Var("z"), Var("z")));
       (Letrec("x", Var("y"), Var("z")))]); 
  assert(List.map (fun v -> subst v repl (Num(1))) varlist
    = [(Num(1)); (Num(1)); (Num(1))]);
  let open Env in
  let env0 = create () in
  assert(close (Var("x")) env0 = Closure((Var("x")), env0));
  let a = extend env0 "x" (ref (Val(Num(1)))) in
  let b = extend a "y" (ref (Val(Num(2)))) in
  let c = extend b "z" (ref (Val(Num(3)))) in
  assert(lookup c "x" = Val(Num(1)));
  assert(lookup c "y" = Val(Num(2)));
  assert(lookup c "z" = Val(Num(3)));
  assert(value_to_string (Val(Num(1))) = "Val(Num(1))");
  let env1 = create () in
  assert(value_to_string ~printenvp:false (Closure((Num(1)), env1)) 
  	= "Val(Num(1))");
  assert(value_to_string (Val(Num(1))) = "Val(Num(1))");
  assert(env_to_string env1 = "[]");
  let eval_list = [eval_s; eval_d; eval_l] in
  assert(List.map(fun x -> value_to_exp(x (Num(1)) env1)) eval_list = 
    [Num(1); Num(1); Num(1)])

       