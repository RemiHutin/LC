(* Example of file when using the compiles mode *) 

open Lib
open Formulas
open Prop
open Bdd



    
(* Pretty-printer for formulas, to be used with compiled mode *)
let print_formula fm = print_prop_formula fm; print_newline();;



(* make : tableT -> tableH -> variable -> id -> id -> id 
 *
 * This function creates a new node.
 * Utility and uniqueness conditions are respected.
 *) 
let make t ht i l h = 
    if member ht i l h then
        lookup ht i l h
    else if l = h then
        l
    else let u = add t i l h in
        insert ht i l h u;
        u
    ;;
    
    
(* apply_neg : tableT -> tableH -> id -> id
 *
 * This function computes the negation of a BBD.
 * Dynamic programming with hash table is used to
 * improve performances.
 *) 
let apply_neg t ht u = 
    let tab = Hashtbl.create 100 in
    let rec aux u =
        match u with
        | u when isZero u -> one
        | u when isOne u -> zero
        | u ->
            try 
                Hashtbl.find tab u
            with
            Not_found ->        
                let r = make t ht (var t u) (aux (low t u)) (aux (high t u))
                in
                Hashtbl.add tab u r; r
    in aux u;;
    
    
(* apply : tableT -> tableH -> op -> id -> id -> id 
 *
 * This function applies a logical operation to 2 BDD and
 * returns a new BDD.
 * Dynamic programming with hash table is used to
 * improve performances.
 *) 
let rec apply t ht op u1 u2 = 
    let tab = Hashtbl.create 100 in
    let rec aux op u1 u2 =
        match op, u1, u2 with
        | Ou,    u1, _ when isZero u1 -> u2
        | Ou,    u1, _ when isOne u1  -> one
        | Et,    u1, _ when isZero u1 -> zero
        | Et,    u1, _ when isOne u1  -> u2
        | Impl,  u1, _ when isZero u1 -> one
        | Impl,  u1, _ when isOne u1  -> u2
        | Equiv, u1, _ when isZero u1 -> apply_neg t ht u2
        | Equiv, u1, _ when isOne u1  -> u2
        | _, _, _ ->   
            try 
                Hashtbl.find tab (op, u1, u2) 
            with
            Not_found ->
                let v1 = var t u1 in
                let v2 = var t u2 in
                let r =
                    if v1 = v2 then
                        make t ht v1 (aux op (low t u1) (low t u2)) (aux op (high t u1) (high t u2))
                    else if v1 < v2 then
                        make t ht v1 (aux op (low t u1) u2) (aux op (high t u1) u2)
                    else
                        make t ht v2 (aux op (low t u2) u1) (aux op (high t u2) u1)
                in
                Hashtbl.add tab (op, u1, u2) r; r
    in aux op u1 u2;;


(* build : tableT -> tableH -> prop formula -> id
 *
 * This function builds a new ROBBD from a prop formula.
 * Dynamic programming with hash table is used to
 * improve performances.
 *) 
let rec build t ht f =
    let tab = Hashtbl.create 1000 in
        let rec aux f = 
            try 
                Hashtbl.find tab f
            with
            Not_found ->
            let r =
                match f with
                | False        -> zero
                | True         -> one
                | Atom (P x)   -> make t ht x zero one
                | Not f1       -> apply_neg t ht (aux f1)
                | And (f1, f2) -> apply t ht Et (aux f1) (aux f2)
                | Or  (f1, f2) -> apply t ht Ou (aux f1) (aux f2)
                | Imp (f1, f2) -> apply t ht Impl (aux f1) (aux f2)
                | Iff (f1, f2) -> apply t ht Equiv (aux f1) (aux f2)
            in
                Hashtbl.add tab f r; r
    in aux f;;

    
(* sat : id -> bool 
 *
 * This function returns true if the ROBDD is satisfiable 
 * (ie not reduced to zero) and false otherwise.
 *)
let sat i = not (isZero i);;


(* valid : id -> bool 
 *
 * This function returns true if the ROBDD is valid 
 * (ie reduced to one) and false otherwise.
 *)
let valid = isOne;;


(* anysat : tableT -> id -> (variable * bool) list
 *
 * If the BDD is satisfiable, this function returns a 
 * valuation satisfying the corresponding boolean function.
 * An empty list is returned otherwise.
 *)
let anysat t i =
    let rec aux i acc =
        match i with
        | i when isZero i -> []
        | i when isOne i -> acc
        | i -> let w = aux (low t i) (((var t i), false)::acc) in 
               if w <> [] then w 
               else aux (high t i) (((var t i), true)::acc);
    in aux i [];;

(* anysat_rand : tableT -> id -> (variable * bool) list
 *
 * If the BDD is satisfiable, this function returns a random
 * valuation satisfying the corresponding boolean function.
 * An empty list is returned otherwise.
 *)
let anysat_rand t i =
    let rec aux i acc =
        match i with
        | i when isZero i -> []
        | i when isOne i -> acc
        | i ->  if Random.int 2 = 0 then
                    let w = aux (low t i) (((var t i), false)::acc) in 
                    if w <> [] then w 
                    else aux (high t i) (((var t i), true)::acc);
                else
                    let w = aux (high t i) (((var t i), true)::acc) in 
                    if w <> [] then w 
                    else aux (low t i) (((var t i), false)::acc);
    in aux i [];;
                
                



(* dames : int -> prop formula 
 *
 * This function build a prop formula, corresponding
 * to the problem of n queens.
 *)
let dames n =

    (* int -> prop formula
     *
     * f i k (for f = row/col/...) must return the variable of the k-th cell of the i-th serie (i.e row/column...). 
     *)
    let row i k = Atom (P (i*n + k)) in
    let col i k = Atom (P (k*n + i)) in
    let diag1 i k = if i+k >= n-1 && i+k < 2*n-1 then Atom (P (k*(n+1) + i - (n-1))) else False in
    let diag2 i k = if i-k >= 0 && i-k < n then Atom (P (k*(n-1) + i)) else False in
    
    
    (* cond : (int -> int -> prop formula) -> int -> int -> bool -> prop formula
     * 
     * "cond f nb_series size_serie opt" builds the prop formula of series (i.e. rows, a columns, a diagonals...)
     * if opt is true, a proposition with the negation of every variable will be added (for diagonals)
     *
     * ex : cond row 3 3 false will create :
     *
     * ((x0 ^ ~x1 ^ ~x2) v (~x0 ^ x1 ^ ~x2) v (~x0 ^ ~x1 ^ x2)) ^
     * ((x3 ^ ~x4 ^ ~x5) v (~x3 ^ x4 ^ ~x5) v (~x3 ^ ~x4 ^ x5)) ^
     * ((x6 ^ ~x7 ^ ~x8) v (~x6 ^ x7 ^ ~x8) v (~x6 ^ ~x7 ^ x8)) 
     *)
    let cond f nb_series size_serie opt =
        let rec series i = 
            let rec serie j =
                let rec serie_aux k =
                    match k with
                    | 0 -> True
                    | k when k = j -> And (serie_aux (k-1), f (i-1) (k-1))
                    | k            -> And (serie_aux (k-1), Not (f (i-1) (k-1)))
                in
                match j with
                | -1 -> False
                | 0 when not opt -> False
                | j -> Or (serie (j-1), serie_aux size_serie)
            in
            match i with
            | 0 -> True
            | i -> And (series (i-1), serie size_serie)
        in series nb_series
    in
    And (And (And (cond row n n false, cond col n n false), cond diag1 (2*n-1) n true), cond diag2 (2*n-1) n true);;
        

    

             
(* board_of_list : (variable * bool) list -> int -> bool array
 *
 * This function converts a valuation to a chess board.
 *)       
let board_of_list l n =
    let board = Array.make (n*n) false
    in
    let rec fill l =
        match l with
        | [] -> ()
        | (p, b)::t -> board.(p)<-b; fill t;
    in
    fill l;
    board;;
               
(* print_board : bool array -> int -> unit
 *
 * This prints a chess board.
 *)            
let print_board board n =
    for i=0 to (n*n-1) do
        if (i mod n = 0) then print_newline();
        print_char (if board.(i) then '#' else '.');
    done;
    print_newline();;
    
    
    
(* svg_of_board : bool array -> int -> string -> unit
 *
 * This saves a chess board to a pretty svg file.
 *
 * https://commons.wikimedia.org/wiki/Category:SVG_chess_pieces
 *)            
let svg_of_board board n filename =
    let f = open_out filename in
    output_string f ("<?xml version='1.0' encoding='utf-8'?>
    <svg xmlns='http://www.w3.org/2000/svg' version='1.1' width='" ^ (string_of_int (n*45)) ^ "' height='" ^ (string_of_int (n*45)) ^ "'>");
    for i=0 to (n-1) do
        for j=0 to (n-1) do
            output_string f ("<g transform='translate(" ^ (string_of_int (i*45)) ^ "," ^ (string_of_int (j*45)) ^ ")'>");
            if ((i+j) mod 2) = 0 then
                output_string f "<rect x='0' y='0' width='45' height='45' style='fill:#ffce9e; stroke:none;'/>"
            else
                output_string f "<rect x='0' y='0' width='45' height='45' style='fill:#d18b47; stroke:none;'/>";
            if board.(i + j*n) then
                output_string f "<g style='opacity:1; fill:#ffffff; fill-opacity:1; fill-rule:evenodd; stroke:#000000; stroke-width:1.5; stroke-linecap:round;stroke-linejoin:round;stroke-miterlimit:4; stroke-dasharray:none; stroke-opacity:1;'>
                <path d='M 9 13 A 2 2 0 1 1  5,13 A 2 2 0 1 1  9 13 z' transform='translate(-1,-1)' />
                <path d='M 9 13 A 2 2 0 1 1  5,13 A 2 2 0 1 1  9 13 z' transform='translate(15.5,-5.5)' />
                <path d='M 9 13 A 2 2 0 1 1  5,13 A 2 2 0 1 1  9 13 z' transform='translate(32,-1)' />
                <path d='M 9 13 A 2 2 0 1 1  5,13 A 2 2 0 1 1  9 13 z' transform='translate(7,-4.5)' />
                <path d='M 9 13 A 2 2 0 1 1  5,13 A 2 2 0 1 1  9 13 z' transform='translate(24,-4)' />
                <path d='M 9,26 C 17.5,24.5 30,24.5 36,26 L 38,14 L 31,25 L 31,11 L 25.5,24.5 L 22.5,9.5 L 19.5,24.5 L 14,10.5 L 14,25 L 7,14 L 9,26 z ' style='stroke-linecap:butt;' />
                <path d='M 9,26 C 9,28 10.5,28 11.5,30 C 12.5,31.5 12.5,31 12,33.5 C 10.5,34.5 10.5,36 10.5,36 C 9,37.5 11,38.5 11,38.5 C 17.5,39.5 27.5,39.5 34,38.5 C 34,38.5 35.5,37.5 34,36 C 34,36 34.5,34.5 33,33.5 C 32.5,31 32.5,31.5 33.5,30 C 34.5,28 36,28 36,26 C 27.5,24.5 17.5,24.5 9,26 z ' style='stroke-linecap:butt;' />
                <path d='M 11.5,30 C 15,29 30,29 33.5,30' style='fill:none;' />
                <path d='M 12,33.5 C 18,32.5 27,32.5 33,33.5' style='fill:none;' />
            </g>";
            output_string f "</g>";
        done
    done;
    output_string f "</svg>";
    close_out f;
    print_string ("Board saved to " ^ filename);
    print_newline();
    ;;
    
    



Random.self_init ();

let taille = 100 in
let n = 10 in
let t = init_t taille in
let ht = init_ht taille in

print_string "building formula";
print_newline();
let f = (dames n) in
    
print_string "building BDD";
print_newline();
let u = time (build t ht) f in 

print_string "solving";
print_newline();
let sol = anysat_rand t u in
let board = board_of_list sol n in
print_board board n;
svg_of_board board n "board.svg";;
