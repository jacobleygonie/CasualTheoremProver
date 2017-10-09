open Syntax;;
open Kernel;;

let rec search (th:theorem) (bound:int) : (theorem option) = match bound with
| 0 -> None
| _ -> match th with
	|{ left=[]; right=[] } ->None
	| { left=[]; right=r } ->None
	| { left=l; right=[] } ->None
	| _ ->  begin let (n_left, n_right)= (size th.left , size th.right) in let all_principals = (make_sublist th) in let found= ref [] in    (** found stocke le résultat**)
	  let j= ref 0 in while (!j<n_left+n_right) do 
			(*print_int !j;*)
		 let (fo,sub_th)= fst (take_indice all_principals !j) in
		  if !j<n_right then if (is_in fo (sub_th.left)) then begin found:=[init_right sub_th fo !j]; j:=n_right +n_left end
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
											search {left=f1::sub_th.left ; right= (f2::sub_th.right)} (bound-1)
											in begin match prem with
											| None -> j:=(!j+1) 
											| Some(t) -> let res = (imp_right t) in begin match res with
														|Some(f,t')-> found:=[sel_right t' !j f]; (j:=n_right +n_left)
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
				
			else if (is_in fo sub_th.right) then begin found:=[init_left sub_th fo (!j-n_right)]; j:=n_right +n_left end
		    								 else match fo with
				|Or(f1,f2) ->let (prem1,prem2)= 
											((search {left=(f1::sub_th.left) ; right= sub_th.right} (bound-1)),(search {left=(f2::sub_th.left) ; right= sub_th.right} (bound-1)) )
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
											((search {left=sub_th.left ; right= (f1::sub_th.right)} (bound-1)),(search {left=(f2::sub_th.left) ; right= sub_th.right} (bound-1)) )
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


let p= Or(And(True,Impl(False,True)),Impl(Or(True,False),False))
let q = Impl(True,False)
let r = True
let s=False
let falso = { left=[True;True;True;True] ;  right= [Impl(False,p)]}
let excluded_middle = { left=[True] ;  right= [Or(p,Impl(p,False))]}
let law = {left=[Impl(Impl(p,q),p)] ;  right= [p]}
let elimination = {left=[True] ;  right= [Impl(Impl(Impl(p,False),False),p)]}
let hilbert= {left=[Impl(p,Impl(q,r))] ;  right= [Impl(Impl(p,q),Impl(p,r))]}
let morgan = {left=[Impl(And(p,q),False)] ;  right= [Or(Impl(p,False),Impl(q,False))]}
let median = {left=[Or(And(p,r),And(q,s))] ;  right= [And(Or(p,q),Or(r,s))]}