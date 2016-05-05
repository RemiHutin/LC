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
    
    
let apply_neg t ht u = 
    let tab = Hashtbl.create 100 in
    let rec aux u =
        try 
            let r = Hashtbl.find tab u in
            print_string "Goog";
            print_newline();
            r;
        with
        Not_found ->
            let r =
            match u with
            | u when isZero u -> one
            | u when isOne u -> zero
            | u ->  make t ht (var t u) (aux (low t u)) (aux (high t u))
            in
            Hashtbl.add tab u r; r
        
    in aux u;;
    
    
let rec apply t ht op u1 u2 = 
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
        | _, u1, u2 when var t u1 = var t u2 -> make t ht (var t u1) (aux op (low t u1) (low t u2)) (aux op (high t u1) (high t u2))
        | _, u1, u2 when var t u1 < var t u2 -> make t ht (var t u1) (aux op (low t u1) u2) (aux op (high t u1) u2)
        | _, u1, u2                          -> make t ht (var t u2) (aux op (low t u2) u1) (aux op (high t u2) u1)
    in
    aux op u1 u2;;


let rec build t ht f =
    match f with
    | False        -> zero
    | True         -> one
    | Atom (P x)   -> make t ht x zero one
    | Not f1       -> apply_neg t ht (build t ht f1)
    | And (f1, f2) -> apply t ht Et (build t ht f1) (build t ht f2)
    | Or  (f1, f2) -> apply t ht Ou (build t ht f1) (build t ht f2)
    | Imp (f1, f2) -> apply t ht Impl (build t ht f1) (build t ht f2)
    | Iff (f1, f2) -> apply t ht Equiv (build t ht f1) (build t ht f2)
    ;;

    
let sat t i = not (isZero i);;
let valid t = isOne;;

let anysat t i =
    let rec aux i acc =
        match i with
        | i when isZero i -> []
        | i when isOne i -> acc
        | i -> let w = aux (low t i) (((var t i), false)::acc) in 
               if w <> [] then w 
               else aux (high t i) (((var t i), true)::acc);
    in aux i [];;
                
                



let dames n =
    let row i k = Atom (P (i*n + k)) in
    let col i k = Atom (P (k*n + i)) in
    let diag1 i k = if i+k >= n-1 && i+k < 2*n-1 then Atom (P (k*(n+1) + i - (n-1))) else False in
    let diag2 i k = if i-k >= 0 && i-k < n then Atom (P (k*(n-1) + i)) else False in
    
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
    print_string "building formula";
    print_newline();
    
    let f = And (And (And (cond row n n false, cond col n n false), cond diag1 (2*n-1) n true), cond diag2 (2*n-1) n true) in
    
    print_string "building BDD";
    print_newline();
    f;;
        
    
    
        

    
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
                    
let print_board board n =
    for i=0 to (n*n-1) do
        if (i mod n = 0) then print_newline();
        print_char (if board.(i) then '#' else '.');
    done;
    print_newline();;
    
(* https://commons.wikimedia.org/wiki/Category:SVG_chess_pieces *)
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
    ;;
    
(* Pretty-printer for formulas, to be used with compiled mode *)
let print_formula fm = print_prop_formula fm; print_newline();;

let f = << ( 1 /\ 2 ) <=> (2 /\ 3) <=> (1 /\ 3) >>;;
print_formula f;;




Random.self_init ();

let taille = 100 in
let n = 8 in
let t = init_t taille in
let ht = init_ht taille in
let f = (dames n) in
let buildt = build t ht in
let u = time buildt f in 
    print_string "solving";
    print_newline();
    print_t t u "graph.dot";
    let sol = anysat t u in
    let board = board_of_list sol n in
    print_board board n;
    svg_of_board board n "board3.svg";;
