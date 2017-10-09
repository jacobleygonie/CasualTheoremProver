(*n=3*)

type term = private
| Variable of string
| Constant of string
| Operator of (string * term list)
type formula =
| Predicate of string * term list | And of formula * formula | True | Or of formula * formula | False
| Implies of formula * formula | Forall of string * formula
| Exists of string * formula


type theorem = { left : formula list; right : formula list ; }



let rec insert l (x:'a) (pos:int) =
assert (pos <= List.length l);
if (pos <= 0) then x::l
else
match l with
| [] -> [x]
| el :: l' -> el :: insert l' x (pos-1)

let rec equal_formula (f1:formula) (f2:formula) =
match f1 , f2 with
| (True,True) | (False,False) -> true
| (And(f1g,f1d) , And(f2g,f2d)) ->
if ( ((equal_formula f1g f2g) &&  (equal_formula f1d f2d)) || ( (equal_formula f1g f2d) &&  (equal_formula f1d f2g) ) ) then true else false
| (Or(f1g,f1d) , Or(f2g,f2d)) -> if ( ((equal_formula f1g f2g) &&  (equal_formula f1d f2d)) || ((equal_formula f1g f2d) &&  (equal_formula f1d f2g))) then true else false
| (Impl(f1g,f1d) , Impl(f2g,f2d)) -> if ( ((equal_formula f1g f2g) &&  (equal_formula f1d f2d))) then true else false
| (_,_) -> false 

let rec equal_formula_list l1 l2= match (l1,l2) with
|([],[])-> true
|((t::q),[])-> false
|([],(t::q))-> false
|((t1::q1),(t2::q2)) -> if (equal_formula t1 t2) then equal_formula_list q1 q2 else false ;;


let rec is_in (f:formula) (li:formula list)=
match li with
| [] -> false
| f0::li' when equal_formula f0 f -> true
| f0::li' -> is_in f li'



let get (f:formula) = match f with 
|And(f1,f2) ->("And",f1,f2)
|Or(f1,f2)->("Or",f1,f2)
|Implies(f1,f2)->("Implies",f1,f2)
|True -> ("True", f, f)
|False ->("False", f, f)
|_ -> failwith ("not a propositionnal formula");;

let make s f1 f2 = match s with
|"True"->  True
|"False"-> False
|"And"->  And (f1,f2)
|"Or" -> Or(f1,f2)
|"Implies"->   Implies (f1,f2)
|_ -> failwith("no matches found");;


let size l= let rec aux l acc= match l with 
		|[]-> acc
		|(t::q) -> aux q (acc+1)
	in aux l 0



let rec take_indice (l:'a list) (i:int) = match l with
| [] -> raise Invalid
| (t::q)-> if i=0 then (t,q) else let (a,b)=(take_indice q (i-1)) in (a,t::b)


let make_sublist (t:theorem):(formula * theorem) list= let (lleft,rright)= (t.left, t.right) in let (n_left,n_right)=((size lleft)-1,(size rright)-1) in
	let res=ref [] in for i=0 to n_left do
		let (f,sub_left)= (take_indice lleft i) 
		in (res := (f, {left=sub_left ; right=rright})::!res) done;
		for j=0 to n_right do
			let (f,sub_right)= (take_indice rright j) in res := ((f,  {left=lleft ; right=sub_right})::!res) done;
			 !res
			
			
let f= make "Or" True  False;;
let g =get f;;


