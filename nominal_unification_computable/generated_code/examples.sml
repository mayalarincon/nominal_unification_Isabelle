use "Nominal_Unification.ML";
open Nominal_Unification;

(* helpers: native SML strings for atoms and variables *)
val s = explode;                      (* string -> char list *)
fun at a = Atom (s a);                (* atom a *)
fun var x = Susp ([], s x);           (* variable X *)
fun susp pi x = Susp (map (fn (a, b) => (s a, s b)) pi, s x);
fun abs a t = Abst (s a, t);          (* [a]t *)

(* print the result: freshness context and substitution *)
fun show_trm (Atom a) = implode a
  | show_trm (Susp ([], x)) = implode x
  | show_trm (Susp (pi, x)) =
      String.concatWith "" (List.map (fn (a, b) => "(" ^ implode a ^ " " ^ implode b ^ ")") pi)
      ^ "." ^ implode x
  | show_trm Unit = "<>"
  | show_trm (Paar (t1, t2)) = "<" ^ show_trm t1 ^ ", " ^ show_trm t2 ^ ">"
  | show_trm (Abst (a, t)) = "[" ^ implode a ^ "]" ^ show_trm t
  | show_trm (Func (f, t)) = implode f ^ " " ^ show_trm t;
fun show NONE = "None"
  | show (SOME (Set fr, sub)) =
      "Some ({" ^ String.concatWith ", " (List.map (fn (a, x) => implode a ^ " # " ^ implode x) fr)
      ^ "}, [" ^ String.concatWith ", " (List.map (fn (x, t) => implode x ^ " := " ^ show_trm t) sub) ^ "])"
  | show _ = "?";
fun run name p = print (name ^ ":  " ^ show (nomu_unify p) ^ "\n");

run "a = a"           ([(at "a", at "a")], []);
run "a = b"           ([(at "a", at "b")], []);
run "(a b).X = a"     ([(susp [("a", "b")] "X", at "a")], []);
run "<X, a> = <b, Y>" ([(Paar (var "X", at "a"), Paar (at "b", var "Y"))], []);
run "X = f X"         ([(var "X", Func (s "f", var "X"))], []);
run "[a]X = [b]b"     ([(abs "a" (var "X"), abs "b" (at "b"))], []);
run "[a]X = [b]X"     ([(abs "a" (var "X"), abs "b" (var "X"))], []);
run "a # (a b).X"     ([], [(s "a", susp [("a", "b")] "X")]);
