structure Str_Literal : sig
  type int = IntInf.int
  val literal_of_asciis : int list -> string
  val asciis_of_literal : string -> int list
end = struct

open IntInf;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs; (* deliberate clone not relying on List._ structure *)

fun check_ascii k =
  if 0 <= k andalso k < 128
  then k
  else raise Fail "Non-ASCII character in literal";

val char_of_ascii = Char.chr o toInt o (fn k => k mod 128);

val ascii_of_char = check_ascii o fromInt o Char.ord;

val literal_of_asciis = String.implode o map char_of_ascii;

val asciis_of_literal = map ascii_of_char o String.explode;

end;

structure Nominal_Unification : sig
  type char
  datatype 'a set = Set of 'a list | Coset of 'a list
  datatype trm = Abst of char list * trm |
    Susp of (char list * char list) list * char list | Unit | Atom of char list
    | Paar of trm * trm | Func of char list * trm
  val implode : char list -> string
  val explode : string -> char list
  val nomu_unify :
    (trm * trm) list * (char list * trm) list ->
      ((char list * char list) set * (char list * trm) list) option
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  ((x1 : bool) = y1) andalso
    (((x2 : bool) = y2) andalso
      (((x3 : bool) = y3) andalso
        (((x4 : bool) = y4) andalso
          (((x5 : bool) = y5) andalso
            (((x6 : bool) = y6) andalso
              (((x7 : bool) = y7) andalso ((x8 : bool) = y8)))))));

val equal_char = {equal = equal_chara} : char equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype trm = Abst of char list * trm |
  Susp of (char list * char list) list * char list | Unit | Atom of char list |
  Paar of trm * trm | Func of char list * trm;

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Set xs) = Set (inserta A_ x xs)
  | insert A_ x (Coset xs) = Coset (removeAll A_ x xs);

fun member A_ x (Set xs) = membera A_ xs x
  | member A_ x (Coset xs) = not (membera A_ xs x);

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun swapa (b, c) a =
  (if equal_lista equal_char b a then c
    else (if equal_lista equal_char c a then b else a));

fun swapas [] a = a
  | swapas (x :: pi) a = swapa x (swapas pi a);

fun swap pi Unit = Unit
  | swap pi (Atom a) = Atom (swapas pi a)
  | swap pia (Susp (pi, x)) = Susp (pia @ pi, x)
  | swap pi (Abst (a, t)) = Abst (swapas pi a, swap pi t)
  | swap pi (Paar (t1, t2)) = Paar (swap pi t1, swap pi t2)
  | swap pi (Func (f, t)) = Func (f, swap pi t);

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun alist_rec [] c d = c
  | alist_rec (p :: al) c d = d (fst p) (snd p) al (alist_rec al c d);

fun look_up x [] = Susp ([], x)
  | look_up xa (x :: xs) =
    (if equal_lista equal_char xa (fst x) then snd x else look_up xa xs);

fun subst s Unit = Unit
  | subst s (Susp (pi, x)) = swap pi (look_up x s)
  | subst s (Atom a) = Atom a
  | subst s (Abst (a, t)) = Abst (a, subst s t)
  | subst s (Paar (t1, t2)) = Paar (subst s t1, subst s t2)
  | subst s (Func (f, t)) = Func (f, subst s t);

fun comp s1 s2 =
  alist_rec s2 s1 (fn x => fn y => fn _ => (fn a => (x, subst s1 y) :: a));

fun of_bool A_ false = zero (zero_zero_neq_one A_)
  | of_bool A_ true = one (one_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs = Str_Literal.literal_of_asciis (map integer_of_char cs);

fun occurs x Unit = false
  | occurs x (Atom a) = false
  | occurs x (Susp (pi, y)) =
    (if equal_lista equal_char x y then true else false)
  | occurs x (Abst (a, t)) = occurs x t
  | occurs x (Paar (t1, t2)) = (if occurs x t1 then true else occurs x t2)
  | occurs x (Func (f, t)) = occurs x t;

fun apply_subst s p =
  (map (fn (t1, t2) => (subst s t1, subst s t2)) (fst p),
    map (fn (a, t) => (a, subst s t)) (snd p));

fun sup_set A_ (Set xs) a = fold (insert A_) xs a
  | sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs);

val bot_set : 'a set = Set [];

fun cred_fun ((xs, (a, Unit) :: ys), (nabla, s)) =
  cred_fun ((xs, ys), (nabla, s))
  | cred_fun ((xs, (a, Paar (t1, t2)) :: ys), (nabla, s)) =
    cred_fun ((xs, (a, t1) :: (a, t2) :: ys), (nabla, s))
  | cred_fun ((xs, (a, Func (f, t)) :: ys), (nabla, s)) =
    cred_fun ((xs, (a, t) :: ys), (nabla, s))
  | cred_fun ((xs, (a, Abst (b, t)) :: ys), (nabla, s)) =
    (if equal_lista equal_char a b then cred_fun ((xs, ys), (nabla, s))
      else cred_fun ((xs, (a, t) :: ys), (nabla, s)))
  | cred_fun ((xs, (a, Atom b) :: ys), (nabla, s)) =
    (if equal_lista equal_char a b then NONE
      else cred_fun ((xs, ys), (nabla, s)))
  | cred_fun ((xs, (a, Susp (pi, x)) :: ys), (nabla, s)) =
    cred_fun
      ((xs, ys),
        (sup_set (equal_prod (equal_list equal_char) (equal_list equal_char))
           (insert (equal_prod (equal_list equal_char) (equal_list equal_char))
             (swapas (rev pi) a, x) bot_set)
           nabla,
          s))
  | cred_fun ((xs, []), (nabla, s)) = SOME ((xs, []), (nabla, s));

fun flatten [] = []
  | flatten (x :: xs) = fst x :: snd x :: flatten xs;

fun ds_list pi1 pi2 =
  remdups (equal_list equal_char)
    (maps (fn x =>
            (if not (equal_lista equal_char (swapas pi1 x) (swapas pi2 x))
              then [x] else []))
      (flatten (pi1 @ pi2)));

fun sred_fun (([], ys), (nabla, s)) = SOME (([], ys), (nabla, s))
  | sred_fun (((t1, t2) :: xs, ys), (nabla, s)) =
    (case t1
      of Abst (a, u) =>
        (case t2
          of Abst (b, v) =>
            (if equal_lista equal_char a b
              then sred_fun (((u, v) :: xs, ys), (nabla, s))
              else sred_fun
                     (((u, swap [(a, b)] v) :: xs, (a, v) :: ys), (nabla, s)))
          | Susp (pi, x) =>
            (if not (occurs x (Abst (a, u)))
              then sred_fun
                     (apply_subst [(x, swap (rev pi) (Abst (a, u)))] (xs, ys),
                       (nabla, comp [(x, swap (rev pi) (Abst (a, u)))] s))
              else NONE)
          | Unit => NONE | Atom _ => NONE | Paar (_, _) => NONE
          | Func (_, _) => NONE)
      | Susp (pi, x) =>
        (case t2
          of Abst (a, v) =>
            (if not (occurs x (Abst (a, v)))
              then sred_fun
                     (apply_subst [(x, swap (rev pi) (Abst (a, v)))] (xs, ys),
                       (nabla, comp [(x, swap (rev pi) (Abst (a, v)))] s))
              else NONE)
          | Susp (pi2, y) =>
            (if equal_lista equal_char x y
              then sred_fun
                     ((xs, map (fn a => (a, Susp ([], x))) (ds_list pi pi2) @
                             ys),
                       (nabla, s))
              else sred_fun
                     (apply_subst [(x, swap (rev pi) (Susp (pi2, y)))] (xs, ys),
                       (nabla, comp [(x, swap (rev pi) (Susp (pi2, y)))] s)))
          | Unit =>
            sred_fun
              (apply_subst [(x, swap (rev pi) Unit)] (xs, ys),
                (nabla, comp [(x, swap (rev pi) Unit)] s))
          | Atom a =>
            sred_fun
              (apply_subst [(x, swap (rev pi) (Atom a))] (xs, ys),
                (nabla, comp [(x, swap (rev pi) (Atom a))] s))
          | Paar (v1, v2) =>
            (if not (occurs x (Paar (v1, v2)))
              then sred_fun
                     (apply_subst [(x, swap (rev pi) (Paar (v1, v2)))] (xs, ys),
                       (nabla, comp [(x, swap (rev pi) (Paar (v1, v2)))] s))
              else NONE)
          | Func (g, v) =>
            (if not (occurs x (Func (g, v)))
              then sred_fun
                     (apply_subst [(x, swap (rev pi) (Func (g, v)))] (xs, ys),
                       (nabla, comp [(x, swap (rev pi) (Func (g, v)))] s))
              else NONE))
      | Unit =>
        (case t2 of Abst (_, _) => NONE
          | Susp (pi, x) =>
            sred_fun
              (apply_subst [(x, swap (rev pi) Unit)] (xs, ys),
                (nabla, comp [(x, swap (rev pi) Unit)] s))
          | Unit => sred_fun ((xs, ys), (nabla, s)) | Atom _ => NONE
          | Paar (_, _) => NONE | Func (_, _) => NONE)
      | Atom a =>
        (case t2 of Abst (_, _) => NONE
          | Susp (pi, x) =>
            sred_fun
              (apply_subst [(x, swap (rev pi) (Atom a))] (xs, ys),
                (nabla, comp [(x, swap (rev pi) (Atom a))] s))
          | Unit => NONE
          | Atom b =>
            (if equal_lista equal_char a b then sred_fun ((xs, ys), (nabla, s))
              else NONE)
          | Paar (_, _) => NONE | Func (_, _) => NONE)
      | Paar (u1, u2) =>
        (case t2 of Abst (_, _) => NONE
          | Susp (pi, x) =>
            (if not (occurs x (Paar (u1, u2)))
              then sred_fun
                     (apply_subst [(x, swap (rev pi) (Paar (u1, u2)))] (xs, ys),
                       (nabla, comp [(x, swap (rev pi) (Paar (u1, u2)))] s))
              else NONE)
          | Unit => NONE | Atom _ => NONE
          | Paar (v1, v2) =>
            sred_fun (((u1, v1) :: (u2, v2) :: xs, ys), (nabla, s))
          | Func (_, _) => NONE)
      | Func (f, u) =>
        (case t2 of Abst (_, _) => NONE
          | Susp (pi, x) =>
            (if not (occurs x (Func (f, u)))
              then sred_fun
                     (apply_subst [(x, swap (rev pi) (Func (f, u)))] (xs, ys),
                       (nabla, comp [(x, swap (rev pi) (Func (f, u)))] s))
              else NONE)
          | Unit => NONE | Atom _ => NONE | Paar (_, _) => NONE
          | Func (g, v) =>
            (if equal_lista equal_char f g
              then sred_fun (((u, v) :: xs, ys), (nabla, s)) else NONE)));

fun bit_cut_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), false)
    else let
           val (r, s) =
             IntInf.divMod (IntInf.abs k, IntInf.abs (2 : IntInf.int));
         in
           ((if IntInf.< ((0 : IntInf.int), k) then r
              else IntInf.- (IntInf.~ r, s)),
             ((s : IntInf.int) = (1 : IntInf.int)))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val (_, a) = bit_cut_integer q6;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, a)
                        end;

fun explode s = map char_of_integer (Str_Literal.asciis_of_literal s);

fun red_plus_fun (p, (nabla, s)) =
  (case sred_fun (p, (nabla, s)) of NONE => NONE
    | SOME ((xs, ys), (nablaa, sa)) => cred_fun ((xs, ys), (nablaa, sa)));

fun nomu_unify p =
  (case red_plus_fun (p, (bot_set, [])) of NONE => NONE
    | SOME (_, (nabla, s)) => SOME (nabla, s));

end; (*struct Nominal_Unification*)
