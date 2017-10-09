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
else let thg = insert t.left principal pos in Some({left=thg ; right = t.right})


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
| (a::gamma,c::delta) -> Some((Impl(a,c) , {left= gamma ; right= delta}))
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

let rec is_in_th (th:theorem) (l: theorem list) : bool = match l with
| []-> false
| (t::q)-> if (equal_formula_list t.left th.left) && (equal_formula_list t.right th.right) then true else is_in_th th q


let rec search_debog (th:theorem) (bound:int) (proved:theorem list ref) : unit = match bound with
| 0 -> ()
| _ -> match th with
	|{ left=[]; right=[] } ->()
	(*| { left=[]; right=r } ->()*)
(*	| { left=l; right=[] } ->None*)
	| _ ->  let (n_left, n_right)= (size th.left , size th.right) in let all_principals = (make_sublist th) in    (** found stocke le résultat**)
	  let j= ref 0 in while (!j<n_left+n_right) do
			(*print_int !j;*)
		 let (fo,sub_th)= fst (take_indice all_principals !j) in
		  if !j<n_right then if ((is_in fo (sub_th.left))) then let final = (init_right sub_th fo !j) in begin match final with
		|Some(m)-> (proved:=m::!proved); (j:=!j+1); |None->  (j:=!j+1) end
		    								 else match fo with
				| And(f1,f2) -> let (th1,th2)=({left=(sub_th.left) ; right= (f1::(sub_th.right))},{left=sub_th.left ; right= (f2::sub_th.right)}) in 
										(search th1 (bound-1) proved) ;(search th2 (bound-1) proved );
											if (is_in_th th1 !proved)&&(is_in_th th2 !proved) then let res = (and_right th1 th2) in begin match res with 
													|Some(f,t) -> let final=(sel_right t !j f) in begin match final with |Some(m) ->( proved:=m::!proved);(j:=!j+1)|None ->(j:=!j+1) end
													|None -> (j:=!j+1) end else (j:=!j+1); 
										
				| Or(f1,f2) ->  let th = {left=sub_th.left ; right= (f1::f2::(sub_th.right))} in (search th (bound-1) proved);
											if (is_in_th th !proved) then let res = (or_right th) in begin match res with
													| Some(f, t')->  let final=(sel_right t' !j f) in begin match final with |Some(m) -> (j:=!j+1); (proved:=m::!proved)|None ->(j:=!j+1); end 
													| None->(j:=!j+1); end else (j:=!j+1); 
				|Impl(f1,f2)-> let th = {left=f1::sub_th.left ; right= (f2::sub_th.right)} in (search th (bound-1) proved);
										if (is_in_th th !proved) then let res = (imp_right th) in begin match res with
													| Some(f, t')->  let final=(sel_right t' !j f) in begin match final with |Some(m) ->(j:=!j+1); (proved:=m::!proved)|None ->(j:=!j+1); end  
													| None-> () end else (j:=!j+1); 
				|True -> let res = (true_right sub_th) in begin match res with 
									          | Some(f,t)->  let final=(sel_right t !j f) in begin match final with |Some(m) ->(j:=!j+1); (proved:=m::!proved) |None ->(j:=!j+1); end 
											      | None ->(j:=!j+1);  end
				|False -> let th = {left=sub_th.left ; right= sub_th.right} in begin search th (bound-1) proved;
												if (is_in_th th !proved) then let res= (false_right th) in match res with 
											| None ->(j:=!j+1); 
											| Some(f,t')->  let final=(sel_right t' !j f) in begin match final with |Some(m) -> (j:=!j+1);(proved:=m::!proved) |None ->(j:=!j+1); end 
											else (j:=!j+1);
											  end 
													
				|_ -> raise Invalid
				
			else if ((is_in fo sub_th.right) or (is_in False sub_th.left)) then begin  let final = (init_left sub_th fo (!j-n_right)) in match final with
		|Some(m)-> (proved:=m::!proved); (j:=!j+1) |None -> (j:=!j+1);end
		    								 else match fo with
				|Or(f1,f2) -> let (th1,th2)=({left=(f1::sub_th.left) ; right= sub_th.right},{left=(f2::sub_th.left) ; right= sub_th.right}) in
											(search th1  (bound-1) proved );(search th2  (bound-1) proved) ;
											if (is_in_th th1 !proved)&&(is_in_th th2 !proved) then let res = (or_left th1 th2) in begin match res with 
													|Some(f,t) ->let final=(sel_left t (!j-n_right) f) in begin match final with |Some(m) ->(j:=!j+1); (proved:=m::!proved)|None ->(j:=!j+1);end 
													|None ->(j:=!j+1); () end else (j:=!j+1); () 
				|And(f1,f2)->  let th = {left=(f1::f2::sub_th.left) ; right= sub_th.right} in (search th (bound-1) proved);
								if (is_in_th th !proved) then let res = (and_left th) in begin match res with
													| Some(f, t')->  let final=(sel_left t' (!j-n_right) f) in begin match final with |Some(m) ->(j:=!j+1);( proved:=m::!proved)|None ->(j:=!j+1); end 
													| None->(j:=!j+1); end else (j:=!j+1); 
				|Impl(f1,f2)->let (th1,th2)=({left=sub_th.left ; right= (f1::sub_th.right)},{left=(f2::sub_th.left) ; right= sub_th.right}) in
												(search th1  (bound-1) proved );(search th2  (bound-1) proved) ;
											if (is_in_th th1 !proved)&&(is_in_th th2 !proved) then let res = (imp_left th1 th2) in begin match res with 
													|Some(f,t) -> let final=(sel_left t (!j-n_right) f) in begin match final with |Some(m) -> (j:=!j+1);(proved:=m::!proved)|None ->(j:=!j+1); end 
													|None ->(j:=!j+1); () end else (j:=!j+1); () 
				|True ->     let th = {left=sub_th.left ; right= sub_th.right} in begin search th (bound-1) proved;
										if (is_in_th th !proved) then let res= (true_left th) in match res with 
											| None -> (j:=!j+1);
											| Some(f,t')-> let final=(sel_left t' (!j-n_right) f) in begin match final with |Some(m) ->(j:=!j+1); (proved:=m::!proved)|None ->(j:=!j+1); end  
											else (j:=!j+1); end
				|False -> let res = (false_left sub_th) in begin match res with 
									          | Some(f,t)-> let final=(sel_left t (!j-n_right) f) in begin match final with |Some(m) -> (j:=!j+1);(proved:=m::!proved)|None ->(j:=!j+1); end 
											      | None ->(j:=!j+1); end
				|_ -> raise Invalid; 
				
				done
				
let valid th bound = let l= ref[] in (search th bound l); is_in_th th !l
let validinter th bound l = search th bound l

let p= False
let q = Impl(True,False)
let r = True
let s=False
let falso = { left=[True] ;  right= [Impl(False,p)]}
let excluded_middle = { left=[True] ;  right= [Or(p,Impl(p,False))]}
let law = {left=[Impl(Impl(p,q),p)] ;  right= [p]}
let elimination = {left=[True] ;  right= [Impl(Impl(Impl(p,False),False),p)]}
let hilbert= {left=[Impl(p,Impl(q,r))] ;  right= [Impl(Impl(p,q),Impl(p,r))]}
let morgan = {left=[Impl(And(p,q),False)] ;  right= [Or(Impl(p,False),Impl(q,False))]}
let median = {left=[Or(And(p,r),And(q,s))] ;  right= [And(Or(p,q),Or(r,s))]}