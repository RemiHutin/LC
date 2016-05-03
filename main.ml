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


let sat t i = 
    let rec sat' i l = 
        let rec seen j l' =
            match l' with
            | [] -> (false, false)
            | (x, b)::_ when x = j -> (true, b)
            | _::q -> seen j q
        in
        match i with
        | i when isZero i -> false
        | i when isOne i -> true
        | i -> let r = seen (var t i) l in 
            begin match r with
                | (true, true) -> sat' (high t i) l
                | (true, false) -> sat' (low t i) l
                | (false, _) -> sat' (low t i) ((i, false)::l) || 
                                sat' (high t i) ((i, true)::l)
            end
in sat' i [];;

let valid t i =
    let rec valid' i l = 
        let rec seen j l' =
            match l' with
            | [] -> (false, false)
            | (x, b)::_ when x = j -> (true, b)
            | _::q -> seen j q
        in
        match i with
        | i when isZero i -> true
        | i when isOne i -> false
        | i -> let r = seen (var t i) l in 
            begin match r with
                | (true, true) -> valid' (high t i) l
                | (true, false) -> valid' (low t i) l
                | (false, _) -> valid' (low t i) ((i, false)::l) || 
                                valid' (high t i) ((i, true)::l)
            end
in not (valid' i []);;


let anysat t i = 
    let rec anysat' i l = 
        let rec seen j l' =
            match l' with
            | [] -> (false, false)
            | (x, b)::_ when x = j -> (true, b)
            | _::q -> seen j q
        in
        match i with
        | i when isZero i -> []
        | i when isOne i -> l
        | i -> let r = seen (var t i) l in 
            begin match r with
                | (true, true) -> anysat' (high t i) l
                | (true, false) -> anysat' (low t i) l
                | (false, _) -> if Random.int 2 = 1 then 
                                    begin
                                    let w = anysat' (low t i) (((var t i), false)::l) in if w <> [] then w else 
                                    anysat' (high t i) (((var t i), true)::l)
                                    end
                                else
                                    begin
                                    let w = anysat' (high t i) (((var t i), true)::l) in if w <> [] then w else 
                                    anysat' (low t i) (((var t i), false)::l)
                                    end
            end
in anysat' i [];;




let queens t ht n =
    let atom p =
        if 0 <= p && p < n*n then
            Atom (P p) 
        else
            False
    in
    let row i k = atom (i*n + k) in
    let col i k = atom (k*n + i) in
    let diag1 i k = if i+k >= n-1 && i+k < 2*n-1 then atom (k*(n+1) + i - (n-1)) else False in
    let diag2 i k = if i-k >= 0 && i-k < n then atom (k*(n-1) + i) else False in
    (*
    i : current serie (row, col, diag...)
    j : pos in the serie
    *)
    let rec cond f i j k opt =
        match i, j, k with
        | -1, _, _           -> True
        | _, -2, _           -> False
        | _, -1, _ when not opt -> False
        | _, _, -1           -> True
        | i, j, k when k = n -> And (cond f (i-1) (n-1) n opt, Or (cond f i (j-1) n opt, cond f i j (k-1) opt))
        | i, j, k when k = j -> And (cond f i j (k-1) opt, f i k)
        | i, j, k            -> And (cond f i j (k-1) opt, Not (f i k))
    in
    
    print_string "building formula";
    print_newline();
    let f = And (And (And (cond row (n-1) (n-1) n false, cond col (n-1) (n-1) n false), cond diag1 (2*n-2) (n-1) n true), cond diag2 (2*n-2) (n-1) n true) in
    print_string "building BDD";
    print_newline();
    build t ht f;;
        
        

    
let rec print_list l =
    match l with
    | [] -> ();
    | (p, b)::q ->  print_int p; 
                    if b then 
                        (print_string " True") 
                    else 
                        (print_string " False"); 
                    print_newline(); 
                    print_list q;;

let rec print_board l n =
    let a = Array.make (n*n) false
    in
    let rec fill l =
        match l with
        | [] -> ()
        | (p, b)::t -> a.(p)<-b; fill t;
    in
    fill l;
    for i=0 to (n*n-1) do
        if (i mod n = 0) then print_newline();
        print_char (if a.(i) then '#' else '.');
    done;
    print_newline();;
    
(* Pretty-printer for formulas, to be used with compiled mode *)
let print_formula fm = print_prop_formula fm; print_newline();;

let f = << ( 1 /\ 2 ) <=> (0 /\ 4) >>;;
print_formula f;;

(* initialization of tables*)
(* Adding a node for variable x_1, with low son 0 and high son 1 *)

(*
let u = make t ht 2 0 0 in

  let v = make t ht 2 1 u in
    debug_print_t t;
    debug_print_h ht 10 10;
    print_t t v "bla.dot";;
    *)

    
    
(*

let taille = 100 in
let t = init_t taille in
let ht = init_ht taille in
let u = build t ht f in 
    debug_print_t t;
    debug_print_h ht 10 10;
    print_t t u "graph.dot";
        
    if sat t u then print_list (anysat t u);
    if valid t u then print_string "I'm legit, bitch";
    print_int ((abs (2 - 10)) mod 8);;
    
    
    let allowed i j n = (i = j) || 
                      (((abs (i - j)) / n <> 0) && 
                      ((abs (i - j)) mod n <> 0));;
*)
Random.self_init ();

let taille = 100 in
let n = 4 in
let t = init_t taille in
let ht = init_ht taille in
let u = queens t ht n in 
    print_string "solving";
    print_newline();
    if sat t u then print_board (anysat t u) n;;
