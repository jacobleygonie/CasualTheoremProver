
open Syntax;;




	
exception Invalid

let sel_left (t:theorem) (pos:int) (principal:formula) =
  if (pos > List.length t.left) then None
else let thg = insert t.left principal pos in Some({t with left = thg})


let sel_right (t:theorem) (pos:int) (principal:formula) =
if (pos > List.length t.right) then None
else let thd = insert t.right principal pos in Some({t with right = thd})

let init_left (t:theorem) (principal:formula) (pos:int) =
if (is_in principal t.right) then sel_left t pos principal
else None

let init_right (t:theorem) (principal:formula)(pos:int) =
if (is_in principal t.left) then sel_right t pos principal
else None


let and_left (t:theorem) =
match t.left with
| a::b::gamma -> Some((And(a,b) , {t with left = gamma}))
| _ -> None

let and_right (t1:theorem) (t2:theorem) =
if (equal_formula_list t1.left t2.left) then
  match t1.right , t2.right with
  | (c::delta1,d::delta2) when equal_formula_list delta1 delta2 -> Some(And(c,d),{t1 with right = delta1})
  | (_,_) -> None
else None

let imp_left (t1:theorem) (t2:theorem) =
match t1.right , t2.left with
| (c::delta , a :: gamma) when (equal_formula_list t1.left gamma) && (equal_formula_list delta t2.right) -> Some((Impl(c,a) , {left = gamma ;right = delta}))
| (_,_) -> None

let imp_right (t:theorem) =
match t.left,t.right with
| (a::gamma,c::delta) -> Some((Impl(a,c) , {right = gamma ; left = delta}))
| (_,_) -> None

let or_left (t1:theorem) (t2:theorem) =
if (equal_formula_list t1.right t2.right) then
match t1.left , t2.left with
| (a::gamma1,b::gamma2) when equal_formula_list gamma1 gamma2 -> Some(Or(a,b),{left = gamma1 ; right = t1.right})
| _ -> None
else None

let or_right (t:theorem) =
match t.right with
| (c::d::delta) -> Some(Or(c,d),{t with right = delta})
| _ -> None

let true_left (t:theorem) = Some(True,t)
let true_right (t:theorem) = Some(True,t)

let false_left (t:theorem) = Some(False,t)
let false_right (t:theorem) = Some(False,t)



(**************************************************************************)

