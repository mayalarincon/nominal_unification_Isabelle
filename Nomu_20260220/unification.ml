(** 
  * the Nominal Unification algorithm by Urban, Pitts & Gabbay 
  * June, 2003
*)

open List;;
exception Fail;;                               (* exception for unification failure *) 

(* terms *)
type term = 
    Unit                                       (* units *)
  | Atm   of string                            (* atoms *)
  | Susp  of (string * string) list * string   (* suspensions *)          
  | Fun   of string * term                     (* function symbols *)
  | Abst  of string * term                     (* abstracted terms *)
  | Pair  of term * term;;                     (* pairs *)  

(* swapping operation on atoms *)
let swap (a,b) c =                             
  if a=c then b else if b=c then a else c;;
let swaps pi c = fold_right swap pi c;;

(* permutation on terms *)
let rec perm pi t =       
  match t with	
      Unit              -> Unit
    | Atm(a)            -> Atm(swaps pi a)
    | Susp(pi',x)       -> Susp(pi@pi',x)
    | Fun(name,t')      -> Fun(name, perm pi t') 
    | Abst(a,t')        -> Abst(swaps pi a,perm pi t')
    | Pair(t1,t2)       -> Pair(perm pi t1,perm pi t2);;	

(* substitution operation 
 * - implements the simple operation of "hole filling" or "context substitution"
 *)
let rec subst t sigma =     
  match t with 
      Unit           -> Unit
    | Atm(a)         -> Atm(a)
    | Susp(pi,y)     -> (try (perm pi (assoc y sigma)) with Not_found -> Susp(pi,y))
    | Fun(name,t')   -> Fun(name,subst t' sigma)
    | Abst(a,t')     -> Abst(a,subst t' sigma)
    | Pair(t1,t2)    -> Pair(subst t1 sigma,subst t2 sigma);;
	
(* substitution composition *)
let rec subst_compose sigma = 
  match sigma with
      [] -> []
    | h::tail -> h::(map (fun (v,t) -> (v,subst t [h])) (subst_compose tail));;

(* occurs check *)
let rec occurs x t =
  match t with 
      Unit                   -> false
    | Atm(a)                 -> false
    | Susp(pi,y)             -> if x=y then true else false
    | Fun(_,t') | Abst(_,t') -> occurs x t' 
    | Pair(t1,t2)            -> (occurs x t1) || (occurs x t2);;

(* deletes duplicates from a list 
 *  - used for calculating disagreement sets
 *)
let rec delete_dups l =             
  match l with                               
      []   -> []
    | h::t -> let t' = delete_dups t in if mem h t' then t' else (h::t');;

(* disagreement set 
 * - takes two permutation (lists of pairs of atoms) as arguments
 *) 
let rec ds pi pi' =    
  let (l1,l2) = split (pi@pi') 
  in filter (fun a -> (swaps pi a)!=(swaps pi' a)) (delete_dups (l1@l2))

(* eliminates a solved equation *) 
let eliminate (v,t) (eprobs,fprobs) =  
  if occurs v t
  then raise Fail
  else (map (fun (t1,t2) -> (subst t1 [(v,t)],subst t2 [(v,t)])) eprobs,
        map (fun (a,t')  -> (a,subst t' [(v,t)])) fprobs);;

(***************)
(* unification *)
(***************)

(* checks and solves all freshness problems *)
let rec check fprobs =                        
  match fprobs with
      [] -> []
    | (a,Unit)::tail        -> check tail
    | (a,Atm(b))::tail      -> if a=b then raise Fail else check tail 
    | (a,Susp(pi,x))::tail  -> (swaps (rev pi) a,x)::(check tail)
    | (a,Fun(_,t))::tail    -> check ((a,t)::tail)
    | (a,Abst(b,t))::tail   -> if a=b then (check tail) else (check ((a,t)::tail))                  
    | (a,Pair(t1,t2))::tail -> check ((a,t1)::(a,t2)::tail);;  

(* solves all equational problems *)
let rec solve eprobs fprobs = solve_aux eprobs fprobs [] 
and solve_aux eprobs fprobs sigma =
  match eprobs with 
      [] -> (subst_compose sigma, delete_dups (check fprobs))
    | (Unit,Unit)::tail -> solve_aux tail fprobs sigma
    | (Atm(a),Atm(b))::tail -> if a=b then (solve_aux tail fprobs sigma) else raise Fail
    | (Susp(pi,x),Susp(pi',x'))::tail when x=x' ->                     
        let new_fps = map (fun a -> (a,Susp([],x))) (ds pi pi') 
	in solve_aux tail (new_fps @ fprobs) sigma 
    | (Susp(pi,x),t)::tail | (t,Susp(pi,x))::tail ->
	let new_sigma = (x,perm (rev pi) t) in
	let (new_eprobs,new_fprobs) = eliminate new_sigma (tail,fprobs) 
	in solve_aux new_eprobs new_fprobs (new_sigma::sigma)
    | (Fun(n1,t1),Fun(n2,t2))::tail -> 
	if  n1 = n2 
	then solve_aux ((t1,t2)::tail) fprobs sigma
	else raise Fail
    | (Abst(a1,t1),Abst(a2,t2))::tail ->
	if a1 = a2 
	then solve_aux ((t1,t2)::tail) fprobs sigma
	else solve_aux ((t1,perm [(a1,a2)] t2)::tail) ((a1,t2)::fprobs) sigma
    | (Pair(t1,t2),Pair(s1,s2))::tail ->
	solve_aux ((t1,s1)::(t2,s2)::tail) fprobs sigma
    | _ -> raise Fail;;

   
(************)
(* Examples *)
(************)

(* a few variables*)
let x = Susp([],"X")
and y = Susp([],"Y")
and z = Susp([],"Z");;

(* lam a.(X a) =? lam b.(c b)     --> [X:=c] *)
let t1 = Abst("a",Pair(x,Atm("a")));;
let t2 = Abst("b",Pair(Atm("c"),Atm("b")));;
solve [(t1,t2)] [];; 

(* lam a.(X a) =? lam b.(a b)     --> fails      *)
let t1 = Abst("a",Pair(x,Atm("a")));;
let t2 = Abst("b",Pair(Atm("a"),Atm("b")));;
solve [(t1,t2)] [];;    

(* lam a.(X a) =? lam b.(X b)     --> a#X, b#X   *)
let t1 = Abst("a",Pair(x,Atm("a")));;
let t2 = Abst("b",Pair(x,Atm("b")));;
solve [(t1,t2)] [];;    

(* lam a.(X a) =? lam b.(Y b)     --> [X:=(a b)oY]  a#Y *)
(*                                --> [Y:=(b a)oX]  b#X *)
let t1 = Abst("a",Pair(x,Atm("a")));;
let t2 = Abst("b",Pair(y,Atm("b")));;
solve [(t1,t2)] [];;   
solve [(t2,t1)] [];;

(* quiz-questions from the paper *)
let m1 = Susp([],"M1")
and m2 = Susp([],"M2")
and m3 = Susp([],"M3")
and m4 = Susp([],"M4")
and m5 = Susp([],"M5")
and m6 = Susp([],"M6")
and m7 = Susp([],"M7");;

(* 1 --> fail *)
let t1 = Abst("a",Abst("b",Pair(m1,Atm("b"))));;
let t2 = Abst("b",Abst("a",Pair(Atm("a"),m1)));;
solve [(t1,t2)] [];;

(* 2 --> [M2:=b ,M3:=a] *)
let t1 = Abst("a",Abst("b",Pair(m2,Atm("b"))));;
let t2 = Abst("b",Abst("a",Pair(Atm("a"),m3)));;
solve [(t1,t2)] [];;

(* 3 --> [M4:=(a b)o M5] *)
let t1 = Abst("a",Abst("b",Pair(Atm("b"),m4)));;
let t2 = Abst("b",Abst("a",Pair(Atm("a"),m5)));;
solve [(t1,t2)] [];;

(* 4 --> [M6:=(b a)oM7] b#M7 *)
let t1 = Abst("a",Abst("b",Pair(Atm("b"),m6)));;
let t2 = Abst("a",Abst("a",Pair(Atm("a"),m7)));;
solve [(t1,t2)] [];;
