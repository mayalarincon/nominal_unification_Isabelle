theory Terms 
  imports Swap
begin

(* terms *)

datatype trm = Abst string  trm   
             | Susp "(string \<times> string)list" string
             | Unit                                   
             | Atom string                           
             | Paar trm trm                          
             | Func string trm                       

(* swapping operation on terms *)

fun swap  :: "(string \<times> string)list \<Rightarrow> trm \<Rightarrow> trm"
  where
  "swap  pi (Unit)        = Unit" 
| "swap  pi (Atom a)      = Atom (swapas pi a)"
| "swap  pi (Susp pi' X)  = Susp (pi@pi') X"
| "swap  pi (Abst a t)    = Abst (swapas pi a) (swap pi t)"
| "swap  pi (Paar t1 t2)  = Paar (swap pi t1) (swap pi t2)"
| "swap  pi (Func F t)    = Func F (swap pi t)"

lemma [simp]: 
  shows "swap [] t = t"
  by (induct_tac t) (auto)


lemma swap_append: 
  shows "swap (pi1@pi2) t = swap pi1 (swap pi2 t)"
  apply(induct t arbitrary: pi1 pi2)
  apply(auto simp add: swapas_append)
  done

lemma swap_empty: 
  assumes "swap pi t = Susp [] X" 
  shows "pi = []"
  using assms swap.elims by blast 

(* depth of terms *)

fun depth :: "trm \<Rightarrow> nat"
  where
  "depth (Unit)      = 0"
| "depth (Atom a)    = 0"
| "depth (Susp pi X) = 0"
| "depth (Abst a t)  = 1 + depth t"
| "depth (Func F t)  = 1 + depth t"
| "depth (Paar t t') = 1 + (max (depth t) (depth t'))" 

lemma 
  Suc_max_left:  "Suc(max x y) = z \<longrightarrow> x < z" and
  Suc_max_right: "Suc(max x y) = z \<longrightarrow> y < z"
by(auto)

lemma [simp]: 
  shows "depth (swap pi t) = depth t" 
  by (induct t) (auto)


(* occurs predicate and variables in terms *)

fun occurs :: "string \<Rightarrow> trm \<Rightarrow> bool"
  where 
  "occurs X (Unit)       = False"
| "occurs X (Atom a)     = False"
| "occurs X (Susp pi Y)  = (if X = Y then True else False)"
| "occurs X (Abst a t)   = occurs X t"
| "occurs X (Paar t1 t2) = (if (occurs X t1) then True else (occurs X t2))"
| "occurs X (Func F t)   = occurs X t"

fun vars_trm :: "trm \<Rightarrow> string set"
  where
  "vars_trm (Unit)       = {}"
| "vars_trm (Atom a)     = {}"
| "vars_trm (Susp pi X)  = {X}"
| "vars_trm (Paar t1 t2) = (vars_trm t1)\<union>(vars_trm t2)"
| "vars_trm (Abst a t)   = vars_trm t"
| "vars_trm (Func F t)   = vars_trm t"


(* subterms and proper subterms *)

fun sub_trms :: "trm \<Rightarrow> trm set"
  where 
  "sub_trms (Unit)       = {Unit}"
| "sub_trms (Atom a)     = {Atom a}"
| "sub_trms (Susp pi Y)  = {Susp pi Y}"
| "sub_trms (Abst a t)   = {Abst a t} \<union> sub_trms t"
| "sub_trms (Paar t1 t2) = {Paar t1 t2} \<union> sub_trms t1 \<union> sub_trms t2"
| "sub_trms (Func F t)   = {Func F t} \<union> sub_trms t"

fun psub_trms :: "trm \<Rightarrow> trm set"
  where
  "psub_trms (Unit)       = {}"
| "psub_trms (Atom a)     = {}"
| "psub_trms (Susp pi X)  = {}"
| "psub_trms (Paar t1 t2) = sub_trms t1 \<union> sub_trms t2"
| "psub_trms (Abst a t)   = sub_trms t"
| "psub_trms (Func F t)   = sub_trms t"

lemma psub_sub_trms: 
  assumes "t1 \<in> psub_trms t2" 
  shows "t1 \<in> sub_trms t2"
  using assms
  by(induct t2)(auto)


lemma t_sub_trms_t: 
  shows "t\<in> sub_trms t"
  by (induct t) (auto)


lemma abst_psub_trms: 
  assumes "Abst a t1 \<in> sub_trms t2"
  shows "t1 \<in> psub_trms t2"
  using assms
apply(induct t2 arbitrary: t1)
apply(auto simp add: t_sub_trms_t intro: psub_sub_trms)
done

lemma func_psub_trms: 
  assumes "Func F t1 \<in> sub_trms t2"
  shows "t1 \<in> psub_trms t2"
  using assms
apply(induct t2)
apply(auto simp add: t_sub_trms_t intro: psub_sub_trms)
done

lemma paar_psub_trms: 
  assumes "Paar t1 t2 \<in> sub_trms t3"
  shows "t1 \<in> psub_trms t3" and "t2 \<in> psub_trms t3"
  using assms
apply(induct t3)
apply(auto simp add: t_sub_trms_t intro: psub_sub_trms)
done

end