type term

type formula

type theorem 

val get : formula -> string * formula * formula

val make : string -> formula -> formula -> formula

val insert : 'a list -> 'a -> int -> 'a list

val equal_formula: formula -> formula -> bool

val equal_formula_list : formula list -> formula list -> bool

val is_in : formula -> formula list -> bool

val size : 'a list -> int

val take_indice : 'a list -> int -> ('a*'a list)

val make_sublist : theorem -> (formula*theorem) list