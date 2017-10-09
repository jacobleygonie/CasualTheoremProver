(*n=3*)

type term = private
| Variable of string
| Constant of string
| Operator of (string * term list)
type formula =
| Predicate of string * term list | And of formula * formula | True | Or of formula * formula | False
| Impl of formula * formula | Forall of string * formula
| Exists of string * formula


type theorem = { left : formula list; right : formula list ; }

	
exception Invalid

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
|((t1::q1),(t2::q2)) -> if (equal_formula t1 t2) then equal_formula_list q1 q2 else false 


let rec is_in (f:formula) (li:formula list)=
match li with
| [] -> false
| f0::li' when equal_formula f0 f -> true
| f0::li' -> is_in f li'



let get (f:formula) = match f with 
|And(f1,f2) ->("And",f1,f2)
|Or(f1,f2)->("Or",f1,f2)
|Impl(f1,f2)->("Impl",f1,f2)
|True -> ("True", f, f)
|False ->("False", f, f)
|_ -> failwith ("not a propositionnal formula");;

let make s f1 f2 = match s with
|"True"->  True
|"False"-> False
|"And"->  And (f1,f2)
|"Or" -> Or(f1,f2)
|"Impl"->   Impl (f1,f2)
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
			
			







let sel_left (t:theorem) (pos:int) (principal:formula) =
  if (pos > List.length t.left) then None
else let thg = insert t.left principal pos in Some({left = thg;right=t.right})


let sel_right (t:theorem) (pos:int) (principal:formula) =
if (pos > List.length t.right) then None
else let thd = insert t.right principal pos in Some({left=t.left;right = thd})

let init_left (t:theorem) (principal:formula) (pos:int) =
if (is_in principal t.right) then sel_left t pos principal
else None

let init_right (t:theorem) (principal:formula)(pos:int) =
if (is_in principal t.left) then sel_right t pos principal
else None


let and_left (t:theorem) =
match t.left with
| a::b::gamma -> Some((And(a,b) , {left = gamma;right = t.right}))
| _ -> None

let and_right (t1:theorem) (t2:theorem) =
if (equal_formula_list t1.left t2.left) then
  match t1.right , t2.right with
  | (c::delta1,d::delta2) when equal_formula_list delta1 delta2 -> Some(And(c,d),{left=t1.left; right = delta1})
  | (_,_) -> None
else None

let imp_left (t1:theorem) (t2:theorem) =
match t1.right , t2.left with
| (c::delta , a :: gamma) when (equal_formula_list t1.left gamma) && (equal_formula_list delta t2.right) -> Some((Impl(c,a) , {left = gamma ;right = delta}))
| (_,_) -> None

let imp_right (t:theorem) =
match t.left,t.right with
| (a::gamma,c::delta) -> Some((Impl(a,c) , {left = gamma ; right = delta}))
| (_,_) -> None

let or_left (t1:theorem) (t2:theorem) =
if (equal_formula_list t1.right t2.right) then
match t1.left , t2.left with
| (a::gamma1,b::gamma2) when equal_formula_list gamma1 gamma2 -> Some(Or(a,b),{left = gamma1 ; right = t1.right})
| _ -> None
else None

let or_right (t:theorem) =
match t.right with
| (c::d::delta) -> Some(Or(c,d),{left=t.left; right = delta})
| _ -> None

let true_left (t:theorem) = Some(True,t)
let true_right (t:theorem) = Some(True,t)

let false_left (t:theorem) = Some(False,t)
let false_right (t:theorem) = Some(False,t)



(**************************************************************************)


let rec search (th:theorem) (bound:int) : (theorem option) = match bound with
| 0 -> None
| _ -> match th with
	|{ left=[]; right=[] } ->None
	| { left=[]; right=r } ->None
(*	| { left=l; right=[] } ->None*)
	| _ ->  begin let (n_left, n_right)= (size th.left , size th.right) in let all_principals = (make_sublist th) in let found= ref [] in    (** found stocke le résultat**)
	  let j= ref 0 in while (!j<n_left+n_right) do 
			(*print_int !j;*)
		 let (fo,sub_th)= fst (take_indice all_principals !j) in
		  if !j<n_right then if ((is_in fo (sub_th.left))) then begin found:=[init_right sub_th fo !j]; j:=n_right +n_left end
		    								 else match fo with
				| And(f1,f2) ->begin let (prem1,prem2)= 
											((search {left=(sub_th.left) ; right= (f1::(sub_th.right))} (bound-1)),(search {left=sub_th.left ; right= (f2::sub_th.right)} (bound-1)) )
											in match (prem1,prem2) with
											| ( None,_) -> j:=(!j+1) 
											| (_, None ) -> j:=(!j+1)
											| (Some(t1),Some(t2)) -> let res = (and_right t1 t2) in begin match res with 
													|Some(f,t) -> found:=[sel_right t !j f]; (j:=n_right +n_left)  (** Problème d'indice??**)
													|None -> j:=(!j+1) end end
				| Or(f1,f2) ->let prem= 
											search {left=sub_th.left ; right= (f1::f2::(sub_th.right))} (bound-1) 
											in begin match prem with
											| None -> j:=(!j+1) 
											| Some(t) -> let res = (or_right t) in begin match res with
													| Some(f, t')->  found:=[sel_right t' !j f]; (j:=n_right +n_left)  
													| None-> j:=(!j+1) end end
				|Impl(f1,f2)->let prem= 
											(search {left=f1::sub_th.left ; right= (f2::sub_th.right)} (bound-1) )
											in begin match prem with
											| None -> j:=(!j+1) 
											| Some(t) -> let res = (imp_right t) in begin match res with
														|Some(f,t')-> found:=[sel_right t' !j f]; (j:=n_right +n_left); 
														|None ->   j:=(!j+1) end end
				|True -> let res = (true_right sub_th) in begin match res with 
									          | Some(f,t)->  found:=[sel_right t !j f]; (j:=n_right +n_left) 
											      | None -> j:=(!j+1) end
				|False ->let prem= 
											search {left=sub_th.left ; right= sub_th.right} (bound-1) 
											in begin match prem with
											| None -> j:=(!j+1) 
											| Some(t) -> let res = (false_right t) in begin match res with
											       |Some(f,t')->  found:=[sel_right t' !j f]; (j:=n_right +n_left) 
														 |None ->   j:=(!j+1) end end
				|_ -> raise Invalid
				
			else if ((is_in fo sub_th.right)) then begin found:=[init_left sub_th fo (!j-n_right)]; j:=n_right +n_left end
		    								 else match fo with
				|Or(f1,f2) ->let (prem1,prem2)= 
											((search {left=(f1::sub_th.left) ; right= sub_th.right} (bound-1) ),(search {left=(f2::sub_th.left) ; right= sub_th.right} (bound-1) ) )
											in begin match (prem1,prem2) with
											| ( None,_) -> j:=(!j+1) 
											| (_,None) -> j:=(!j+1)
											| (Some(t1),Some(t2)) -> let res = (or_left t1 t2) in begin match res with
											        |Some(f,t) ->found:=[sel_left t (!j-n_right) f]; (j:=n_right +n_left)  (** Problème d'indice??**)
															|None -> j:=(!j+1) end end 
				|And(f1,f2)->let prem= 
											search {left=(f1::f2::sub_th.left) ; right= sub_th.right} (bound-1) 
											in begin match prem with
											| None -> j:=(!j+1) 
											| Some(t) -> let res = (and_left t) in  begin match res with
											        | Some(f,t') ->found:=[sel_left t' (!j-n_right) f]; (j:=n_right +n_left)   
															| None -> j:=(!j+1) end end
				|Impl(f1,f2)->let (prem1,prem2)= 
											((search {left=sub_th.left ; right= (f1::sub_th.right)} (bound-1) ),(search {left=(f2::sub_th.left) ; right= sub_th.right} (bound-1) ) )
											in begin match (prem1,prem2) with
											| ( None,_) -> j:=(!j+1) 
											| (_,None) -> j:=(!j+1)
											| (Some(t1),Some(t2)) -> let res = (imp_left t1 t2) in begin match res with
											        |Some(f,t) -> found:=[sel_left t (!j-n_right) f]; (j:=n_right +n_left) 
															|None -> j:=(!j+1) end end
				|True ->     let prem= 
											search {left=sub_th.left ; right= sub_th.right} (bound-1) 
											in begin match prem with
											|None-> j:=(!j+1) 
											|Some(t) -> let res = (true_left t) in  begin match res with
										           |Some(f,t') ->found:=[sel_left t' (!j-n_right) f]; (j:=n_right +n_left)  
															 |None -> j:=(!j+1) end end 
				|False -> let res = (false_left sub_th) in begin match res with
				              |Some(f,t)->  found:=[sel_left t (!j-n_right) f]; (j:=n_right +n_left)
											|None -> j:=(!j+1) end 
				|_ -> raise Invalid
				done; 
				
				 match !found with 
				| [u] -> u
				| _ -> None end


let p= True
let q = And(True,False)
let r = Impl(Or(False,True),True)
let s=And(True,True)
let falso = { left=[True;True;True;True] ;  right= [Impl(False,p)]}
let excluded_middle = { left=[True] ;  right= [Or(p,Impl(p,False))]}
let law = {left=[Impl(Impl(p,q),p)] ;  right= [p]}
let elimination = {left=[True] ;  right= [Impl(Impl(Impl(p,False),False),p)]}
let hilbert= {left=[True] ;  right= [Impl(Impl(p,Impl(q,r)),Impl(Impl(p,q),Impl(p,r)))]}
let morgan = {left=[True] ;  right= [Impl(Impl(And(p,q),False),Or(Impl(p,False),Impl(q,False)))]}
let median = {left=[True] ;  right= [Impl(Or(And(p,r),And(q,s)),And(Or(p,q),Or(r,s)))]}





