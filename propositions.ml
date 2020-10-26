
(*------------- helping functions ----------------------------*)

(*Member function *)
(*T.C = O(n), S.C = O(1) if recursive calls space not considered*)
let rec member x s = 
match s with
| [] -> false
| hd :: xs ->
if hd = x then true
else
member x xs
;;


(*Remove duplicate from the list *)
(*T.C = O(n^2) S.C = O(n) to store distinct elements*)
let rec call_set l s = 
	match l with
    | [] -> s
    | h1::t1 -> 
          if member h1 s = true then 
              call_set t1 s
          else
              call_set t1 (h1::s)
;;

(*Set calling function*)
let set l = call_set l [];;


(*Union function *)
(*T.C = O(m*n)  S.C = O(1) if recursive calls space not considered*)
let rec call_union l1 l2 = 
  match l1 with
  | [] -> l2
  | h1::t1-> 
   if member h1 l2 then 
    call_union t1 l2
   else
    call_union t1 (h1::l2)

let union l1 l2 =
	  match l1 with 
	  | [] -> set l2
	  | h1::t1 -> 
	  (
	    match l2 with
	    | [] -> set l1
	    | h2::t2 -> call_union (set l1) (set l2) 
	  )
(*---------------------- helping functions --------------------------*)

(*Data type for propositions*)

type prop = 
		| T
		| F
		| Letter of string
		| Not of prop
		| And of prop * prop
		| Or of prop * prop
		| Impl of prop * prop
		| Iff of prop * prop
;;


(* size of syntax tree in terms of nodes *)
(*which returns the number of nodes in a proposition (syntax tree)*)
let rec size p = 
		match p with
		T -> 1
		| F -> 1
		| Letter s -> 1
		| Not p1 -> 1 + (size p1)
		| And (p1, p2) -> 1 + (size p1) + (size p2)
		| Or (p1, p2) -> 1 + (size p1) + (size p2)
		| Impl (p1, p2) -> 1 + (size p1) + (size p2)
		| Iff (p1, p2) -> 1 + (size p1) + (size p2)
;;

(* height of syntax tree, counting from 0 *)
(*which returns the height of a proposition (syntax tree)*)
let rec ht p = 
		match p with
		| T -> 0
		| F -> 0
		| Letter s -> 0
		| Not p1 -> 1 + (ht p1)
		| And (p1, p2) -> 1 + (max (ht p1) (ht p2))
		| Or (p1, p2) -> 1 + (max (ht p1) (ht p2))
		| Impl (p1, p2) -> 1 + (max (ht p1) (ht p2))
		| Iff (p1, p2) -> 1 + (max (ht p1) (ht p2))
;;

(* Semantics: Truth functions *)

let rec truth p rho = match p with
		| T -> true
		| F -> false
		| Letter s -> rho s
		| Not p1 -> not (truth p1 rho)
		| And (p1, p2) -> (truth p1 rho) && (truth p2 rho)
		| Or (p1, p2) -> (truth p1 rho) || (truth p2 rho)
		| Impl (p1, p2) -> (not (truth p1 rho)) || (truth p2 rho)
		| Iff (p1, p2) -> ((truth p1 rho) && (truth p2 rho)) ||
			(( not (truth p1 rho)) && (not (truth p2 rho)))
;;

let rec nnfpos p = 
		match p with
		| T -> p
		| F -> p
		| Letter s -> p
		| And (p1, p2) -> And (nnfpos p1, nnfpos p2)
		| Or (p1, p2) -> Or (nnfpos p1, nnfpos p2)
		| Impl (p1, p2) -> Or (nnfneg p1, nnfpos p2)
		| Iff (p1, p2) -> Or( And(nnfpos p1, nnfpos p2), And(nnfneg p1, nnfneg p2))
		| Not p1 -> nnfneg p1
and
	nnfneg p = 
		match p with
		| T -> F
		| F -> T
		| Letter s -> Not( Letter s)
		| Not p1 -> nnfpos p1
		| And (p1, p2) -> Or (nnfneg p1, nnfneg p2)
		| Or (p1, p2) -> And (nnfneg p1, nnfneg p2)
		| Impl (p1, p2) -> And (nnfpos p1, nnfneg p2)
		| Iff (p1, p2) -> Or( And(nnfneg p1, nnfpos p2), And(nnfpos p1, nnfneg p2))
;;

(*----------------Already implemented functions : end---------------------------*)

(*Que 1:- vars: prop -> string set, which returns the set of propositional letters that appear in a proposition.*)
(*Time Complexity : O(n^2) because of union  operation though we need to scan the whole proposition only once.*)
(*(Space Complexity is O(1) if we don't consider recursive calls space)*)
let rec vars p = 
	match p with 
	| T -> []
	| F -> []
	| Letter str -> [str]
	| And (p1, p2) -> 
	(
		let e1 = vars p1 in
		let e2 = vars p2 in 
		union (e1) (e2) 
	)
	| Not (p1) -> vars p1
	| Or (p1, p2) -> 
	(
		let e1 = vars p1 in
		let e2 = vars p2 in 
		union (e1) (e2) 
	)
	| Impl (p1, p2) -> 
	(
		let e1 = vars p1 in
		let e2 = vars p2 in 
		union (e1) (e2) 
	)
	| Iff (p1, p2) -> 
	(
		let e1 = vars p1 in
		let e2 = vars p2 in 
		union (e1) (e2) 
	)
;;

(*Que 2:- cnf: prop -> prop set set, which converts a proposition into conjunctive normal form (POS) as 
a set of clauses, each of*)
(*T.C = O(n) S.C = O(1)*)

(*Convert cnf  into list *)
let rec cnf_or_removal p =
  match p with
  | Or (p1, p2) -> 
  (
  		let e1 = cnf_or_removal p1 in
  		let e2 = cnf_or_removal p2 in
  		List.append e1 e2
  )
  | q -> [q]
;;

let rec cnf_and_removal p =
  match p with
  | And (p1, p2) -> 
  (
  		let e1 = cnf_and_removal p1 in
  		let e2 = cnf_and_removal p2 in
  		List.append e1 e2
  )
  | q  -> [cnf_or_removal q]
;;

let rec nnf_cnf p = match p with
              T -> p
            | F -> p
            | Letter str -> p
            | And (p1,p2) -> 
            (
            	let e1 = nnf_cnf p1 in 
            	let e2 = nnf_cnf p2 in
            	And(e1, e2)
            )
            | Or (p1,And(q1,q2)) ->  
            (
            	let  e1  = Or(nnf_cnf p1,nnf_cnf q1) in
            	let  e2  = Or(nnf_cnf p1,nnf_cnf q2) in
            	nnf_cnf (And(e1,e2))
            )
            | Or (And(q1,q2),p1) -> 
            (
            	let e1 = Or(nnf_cnf q1,nnf_cnf p1) in
            	let e2 = Or(nnf_cnf q2,nnf_cnf p1) in
             	nnf_cnf (And( e1, e2))
            )
            | Or (p1,p2) ->
            ( 
            	let e1 = nnf_cnf p1 in
            	let e2 = nnf_cnf p2 in
            	Or(e1,e2)
            )
            | Not p1 -> p
            | _ -> p
            ;;

(* First convert to nnf then to cnf then convert into list *)
let cnf p = set (cnf_and_removal (nnf_cnf(nnfpos(p))));;
let cnf_prop p = nnf_cnf(nnfpos(p));; (*cnf propositions*)
(*let cnf p = cnf_and_removal (nnf_cnf(nnfpos(p)));;*)

(*Que 3:- dnf: prop -> prop set set,  which converts a proposition into disjunctive normal form (SOP) 
as a set of terms, each of which is a set of literals. *)
(*T.C = O(n) S.C = O(1)*)
(*Convert cnf  into list *)
let rec dnf_and_removal p =
  match p with
  | And (p1, p2) -> 
  (
  		let e1 = dnf_and_removal p1 in
  		let e2 = dnf_and_removal p2 in
  		List.append e1 e2
  )
  | q -> [q]
;;

let rec dnf_or_removal p =
  match p with
  | Or (p1, p2) -> 
  (
  		let e1 = dnf_or_removal p1 in
  		let e2 = dnf_or_removal p2 in
  		List.append e1 e2
  )
  | q  -> [dnf_and_removal q]
;;

let rec nnf_dnf p = match p with
            | Letter str -> p
            | Not p1 -> p
            | T -> T
            | F -> F
            | Or (p1,p2) -> 
            (
            	let e1 = nnf_dnf p1 in
            	let e2 = nnf_dnf p2 in
            	Or (e1,e2)
            )
            | And (p1,Or(q1,q2)) ->  
            (
            	let e1 = And(nnf_dnf p1,nnf_dnf q1) in
            	let e2 = And(nnf_dnf p1,nnf_dnf q2) in
           		 nnf_dnf (Or(e1,e2))
            )
            | And (Or(q1,q2),p1) ->  
            (
            	let e1 = And(nnf_dnf q1,nnf_dnf p1) in
            	let e2 = And(nnf_dnf q2,nnf_dnf p1) in
            	nnf_dnf (Or(e1,e2))
            )
            | And (p1,p2) -> 
            (
            	let e1 = nnf_dnf p1 in
            	let e2 = nnf_dnf p2 in
            	And(e1,e2)
            )
            | _ -> p
            ;;

(* First convert to nnf then to cnf and convert into list *)
let dnf p = set (dnf_or_removal (nnf_dnf(nnfpos(p))));;
(*let dnf p = dnf_or_removal (nnf_dnf(nnfpos(p)));;*)

(*------------------------Semantic----------------*)

(*Que 4:- isTautology: prop -> bool, which checks if a proposition is a tautology.*)
(* Creates a set of product terms from SOP // splits proposition at ors into a set of clauses*)
(* Checking Given Proposition is Tautology or not *)
(*T.C = O(n) S.C = O(1)
*)
let rho str = 
  match str with
    |"p" -> false
    |"q" -> true
    |"r" -> true
    | _ -> false
    ;;


let rec split_and_terms p = 
	match p with 
    | And (p1,p2) -> 
    (
    	let e1 = split_and_terms p1 in
    	let e2 = split_and_terms p2 in
    	union e1 e2
    )
    | literal -> [literal]
 ;;

let rec split_or_terms p = 
	match p with 
    | Or (p1,p2) -> 
    (
    	let e1 = split_or_terms p1 in
    	let e2 = split_or_terms p2 in
    	union e1 e2
    )
    | literal -> [literal]
 ;;



let isClauseTautotlogy p = 
				let literals = split_or_terms p in 
        let e1  =  List.mem T literals in
        e1 || List.fold_left (fun c a -> (List.mem (nnfpos(Not a)) literals) || c) false literals 
;;

let p1 = T;;
let p2 = F;;

let isTautology_cal clauses_of_p_cnf = 
                    List.fold_left (fun c a -> isClauseTautotlogy a && c) true clauses_of_p_cnf;;  

let isTautology p = 
	let conf_prop_terms = cnf_prop p in
	let splitted_terms = split_and_terms conf_prop_terms in
	isTautology_cal  (splitted_terms)
;;

(*Que 4:- isContradiction: prop -> bool, which checks if a proposition is a tautology.*)
(*T.C = O(n) S.C = O(1)*)
let isContradiction p = 
	let not_p = Not p in
	isTautology (not_p)
;;

(*Que 5:- isSatisfiable: prop -> bool, which checks if a proposition is satisfiable, *)
(*T.C = O(n) S.C = O(1)*)
let isSatisfiable p = 
	let constradiction = isContradiction p in
	not (constradiction)
;;

(*Que 6:- isEquivalent: prop -> prop -> bool, which checks if two propositions are logically equivalent.*)
(*T.C = O(n) S.C = O(1)*)
let isEquivalent p1 p2 = 
	let iff_exp = Iff (p1,p2) in
	isTautology (iff_exp)
;;

(*Que 7:- isFalsifiable: prop -> bool, which checks if a proposition is satisfiable *)
(*T.C = O(n) S.C = O(1)*)
let isFalsifiable p = 
	let tautology = isTautology p in
	not (tautology)
;;

(*Que 8:- entails: prop set -> prop -> bool, which checks if a given proposition is a logical 
consequence of a given set of propositions.*)
(*Time Complexity depends on the total length of all the propositions as we and them all and then apply p ->q*)
let rec anded_props prop_set = List.fold_left (fun x y -> And(x,y)) T prop_set;;

let rec entails p_set p = 
	match p_set with 
	|[] -> true
	|h::t ->
	(
		let anded_prop_set = anded_props p_set in
		let impl_val = Impl(anded_prop_set, p) in

		isTautology impl_val
	)
;;

(*-------------------------models ------------------------------------*)
(*evaluate expression*)
let rec eval val_vars = function
    | Letter x -> List.assoc (Letter x) val_vars
    | Not p1 ->
    ( 
      let e1 = eval val_vars p1 in
        not(e1)
    )
    | And(p1, p2) -> 
    (
      let e1 = eval val_vars p1 in
      let e2 = eval val_vars p2 in
       e1 && e2
    )
    | Or(p1, p2) -> 
    (
      let e1 = eval val_vars p1 in
      let e2 = eval val_vars p2 in  
       e1 || e2 
    )
;;

(*val_vars = variables with truth values , vars = variables list; prop = proposition*)
let rec table_make val_vars vars prop =
    match vars with
    | [] -> 
    (
        let e1 = List.rev val_vars in
        let e2 = eval val_vars prop in
        (*[(e1,e2)]*)
        if e2 = true then 
          (*[(e1,e2)]*)
          [e1]
        else
          []

    )
    | v :: tl ->
    (
      let e1 = (( Letter v, true) :: val_vars) in
      let e2 = ((Letter v, false) :: val_vars) in
       table_make e1 tl prop
       @ table_make e2 tl prop
    )
;;  

  (*Vars = ["a"; "b"; "c"] prop = proposition*)
let table vars prop = table_make [] vars prop;;

(* Que 8:-models: prop -> valuation set, which returns the set of ``all valuations'' that satisfy a given prop.*)
(*T.C = O(2^n) S.C = n*2^n *)
let models prop  = table (vars (cnf_prop prop)) (cnf_prop prop);;

(*Que 9:- satisfier: prop -> valuation, which returns a satisfying truth assignment if it exists.*)
(*T.C = O(2^n) S.C = n*2^n *)
let satisfier prop = 
  let result = models prop in
    if result = [] then []
    else List.hd result
;;
(*Que 10:- falsifier: prop -> valuation, which returns a falsifying truth assignment if it exists.*)
(*T.C = O(2^n) S.C = n*2^n *)
let falsifier prop = 
  let result = models (Not (prop)) in
    if result = [] then []
    else List.hd result
;;
(*----------------------- test cases ---------------------------------------*)
print_string "\n\n-------------tests cases------------";;
print_string "\n-------------vars example------------";;
let x = Or (Letter "a", And (Letter "c", Not (Or (Not (Letter "d"), Letter "b"))));;
vars x;;
let x3 = And(Letter "a", Or(Letter "b", Letter "c"));;
vars x3;;
print_string "\n-------------cnf (POS) example------------";;
let x = Or (Letter "a", And (Letter "c", Not (Or (Not (Letter "d"), Letter "b"))));;
cnf x;;
print_string "\n-------------dnf (SOP) example------------";;
let x3 = And(Letter "a", Or(Letter "b", Letter "c"));;
dnf x3;;
print_string "\n-------------semantic exampls------------";;
print_string "\n-------------entails------------";;
print_string "\nentails [T;T] F;;";;
entails [T;T] F;;
print_string "\nentails [T;T;F] F;;";;
entails [T;T;F] F;; 
print_string "\nentails [T;T;F] T;;";;
entails [T;T;F] T;;
print_string "\nentails [T;T;T] T;;";;
entails [T;T;T] T;;
print_string "\n-------------isSatisfiable------------";;
let p = And(Or( F , F), And (T,T));;
isSatisfiable p;;
let p = (Or( T , F));;
isSatisfiable p;;
let x4 = And(T,F);;
isSatisfiable x4;;
print_string "\n-------------isContradiction------------";;
let p = And(Or( F , F), And (T,T));;
isContradiction p;;
let p = (Or( T , F));;
isContradiction p;;
let x4 = And(T,F);;
isContradiction x4;;
print_string "\n-------------isTautology------------";;
let p = And(Or( F , F), And (T,T));;
isTautology p;;
let p = (Or( Letter "a" , Not(Letter "a") ));;
isTautology p;;
let x4 = And(T,F);;
isTautology x4;;
print_string "\n-------------isEquivalent------------";;
let p1 = Or(Letter "b", Letter "a");;
let p2 = Or(Letter "a", Letter "b");;  
isEquivalent p1 p2;;
let p1 = Or(And(T,F),And(T,T));;
let p2 = Or(T,F);;  
isEquivalent p1 p2;;
let p1 = Or(And(T,F),And(T,T));;
let p2 = Or(F,F);;  
isEquivalent p1 p2;;
print_string "\n-------------isFalsifiable------------";;
let p = And(Or( F , F), And (T,T));;
isFalsifiable p;;
let p = (Or( T , F));;
isFalsifiable p;;
let x4 = And(T,F);;
isFalsifiable x4;;
print_string "\n-------------models------------";;
let x8 =(And(Letter "a", Or(Letter "a", Letter "b")));;
models x8;;
let x9  = let a = Letter "a" and b = Letter "b" and c = Letter "c" in
  (Or(And(a, Or(b,c)), Or(And(a,b), And(a,c))));;
models x9;;
print_string "\n-------------satisfier------------";;
let x11 = And(Letter "a", Letter "b");;
satisfier x11;;
let x12 = Or(Letter "a", Letter "b");;
satisfier x12;;
let x13 = And(Letter "a", Not(Letter "a"));; 
satisfier x13;;
print_string "\n-------------falsifier------------";;
let x11 = And(Letter "a", Letter "b");;
falsifier x11;;
let x12 = Or(Letter "a", Letter "b");;
falsifier x12;;
let x13 = And(Letter "a", Not(Letter "a"));; 
falsifier x13;;
let x14 = Or(Letter "a", Not(Letter "a"));;
falsifier x14;;