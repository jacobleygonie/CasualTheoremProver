open Syntax;;

val sel_left: theorem -> int -> formula -> theorem option

val sel_right: theorem -> int -> formula -> theorem option

val init_left : theorem -> formula -> int -> theorem option

val init_right : theorem -> formula -> int -> theorem option

val and_left : theorem -> (formula*theorem) option

val and_right : theorem->theorem -> (formula*theorem) option

val imp_left : theorem->theorem -> (formula*theorem) option

val imp_right : theorem -> (formula*theorem) option

val or_left : theorem->theorem -> (formula*theorem) option

val or_right : theorem -> (formula*theorem) option

val true_left : theorem -> (formula*theorem) option

val false_left : theorem -> (formula*theorem) option

val true_right : theorem -> (formula*theorem) option

val false_right : theorem -> (formula*theorem) option