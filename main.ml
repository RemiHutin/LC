(* Example of file when using the compiles mode *) 

open Lib
open Formulas
open Prop
open Bdd



let make t ht i l h = 
    if member ht i l h then
        lookup ht i l h
    else if l = h then
        l
    else let u = add t i l h in
        insert ht i l h u;
        u
    ;;
    
    
let rec apply_neg t ht u = 
    match u with
    | u when isZero u -> one
    | u when isOne u -> zero
    | u -> make t ht (var t u) (apply_neg t ht (low t u)) (apply_neg t ht (high t u));;
    
    
let rec apply t ht op u1 u2 = 
    match op, u1, u2 with
    | Ou,    u1, _ when isZero u1 -> u2
    | Ou,    u1, _ when isOne u1  -> one
    | Et,    u1, _ when isZero u1 -> zero
    | Et,    u1, _ when isOne u1  -> u2
    | Impl,  u1, _ when isZero u1 -> one
    | Impl,  u1, _ when isOne u1  -> u2
    | Equiv, u1, _ when isZero u1 -> apply_neg t ht u2
    | Equiv, u1, _ when isOne u1  -> u2
    | _, u1, u2 when var t u1 = var t u2  -> make t ht (var t u1) (apply t ht op (low t u1) (low t u2)) (apply t ht op (high t u1) (high t u2))
    | _, u1, u2 when var t u1 <> var t u2 -> make t ht (var t u1) (apply t ht op (low t u1) u2) (apply t ht op (high t u1) u2)
    | _, _, _ -> zero
    ;;


let rec build t ht f =
    match f with
    | False -> zero
    | True -> one
    | Atom (P x) -> make t ht x zero one
    | Not f1 -> apply_neg t ht (build t ht f1)
    | And (f1, f2) -> apply t ht Et (build t ht f1) (build t ht f2)
    | Or (f1, f2) -> apply t ht Ou (build t ht f1) (build t ht f2)
    | Imp (f1, f2) -> apply t ht Impl (build t ht f1) (build t ht f2)
    | Iff (f1, f2) -> apply t ht Equiv (build t ht f1) (build t ht f2)
    ;;


(* Pretty-printer for formulas, to be used with compiled mode *)
let print_formula fm = print_prop_formula fm; print_newline();;

let f = << ( 1 <=> 2 ) /\ ( 3 <=> 4 )>>;;
print_formula f;;

let taille = 100 in
(* initialization of tables*)
let t = init_t taille in
let ht = init_ht taille in
(* Adding a node for variable x_1, with low son 0 and high son 1 *)
let u = make t ht 2 0 0 in

  (* Adding a node for variable x_2, with low son 1 and high son u *)
  let v = make t ht 2 1 u in
    debug_print_t t;
    debug_print_h ht 10 10;
    print_t t v "bla.dot";;

