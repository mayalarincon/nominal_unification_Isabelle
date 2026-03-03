theory Termination 

  imports Mgu

begin

(* set of variables *)

type_synonym eprobs = "((trm \<times> trm) list)"
type_synonym fprobs = "((string \<times> trm) list)"
type_synonym probs = "eprobs \<times> fprobs"
                                             
fun vars_trm :: "trm \<Rightarrow> string set"
  where
"vars_trm (Unit)       = {}" |
  "vars_trm (Atom a)     = {}" |
  "vars_trm (Susp pi X)  = {X}" |
  "vars_trm (Paar t1 t2) = (vars_trm t1)\<union>(vars_trm t2)" |
  "vars_trm (Abst a t)   = vars_trm t" | 
  "vars_trm (Func F t)   = vars_trm t"

fun vars_eprobs :: "eprobs \<Rightarrow> (string set)"
  where 
  "vars_eprobs [] = {}" |
  "vars_eprobs (x#xs) = (vars_trm (snd x))\<union>(vars_trm (fst x))\<union>(vars_eprobs xs)"

fun vars_fprobs:: "fprobs \<Rightarrow> (string set)"
  where
  "vars_fprobs [] = {}" |
  "vars_fprobs (x#xs) = (vars_trm (snd x))\<union>(vars_fprobs xs)"


definition apply_subst_eprobs :: "substs \<Rightarrow> eprobs \<Rightarrow> eprobs"
  where "apply_subst_eprobs s P \<equiv> map (\<lambda>(t1, t2). (subst s t1 \<approx>? subst s t2)) P"


lemma[simp]: "vars_trm (swap pi t) = vars_trm t"
  by (induct t) auto

fun size_trm :: "trm \<Rightarrow> nat"
  where
  "size_trm (Unit)      = 1" |
  "size_trm (Atom a)    = 1" |
  "size_trm (Susp pi X) = 1" |
  "size_trm (Abst a t)  = 1 + size_trm t" |
  "size_trm (Func F t)  = 1 + size_trm t" |
  "size_trm (Paar t t') = 1 + (size_trm t) + (size_trm t')"

fun size_fprobs :: "fprobs \<Rightarrow> nat"
  where 
    "size_fprobs [] = 0" |
    "size_fprobs (x#xs) = (size_trm (snd x))+(size_fprobs xs)"

fun size_eprobs :: "eprobs \<Rightarrow> nat"
  where
 "size_eprobs [] = 0" | 
  "size_eprobs (x#xs) = (size_trm (fst x))+(size_trm (snd x))+(size_eprobs xs)"

  (*size_probs  :: "probs \<Rightarrow> nat"*)

lemma size_swap [simp]: "size_trm (swap pi t) = size_trm t"
  by (induct t) auto

definition measure_relation :: 
  "(nat\<times>nat\<times>nat) \<Rightarrow> (nat\<times>nat\<times>nat) \<Rightarrow> bool"  (infix "\<lless>" 80)
where
  "x \<lless> y \<longleftrightarrow> (x, y) \<in> (less_than <*lex*> less_than <*lex*> less_than)"

fun rank :: "probs \<Rightarrow> (nat\<times>nat\<times>nat)"
  where
  "rank (eprobs,fprobs) = (card (vars_eprobs eprobs),size_eprobs eprobs, size_fprobs fprobs)"


lemma vars_term_finite [simp]: "finite (vars_trm t)"
  by (induct t) auto


lemma vars_eprobs_finite [simp]: "finite (vars_eprobs P)"
  by (induct P) auto


lemma union_comm: "A\<union>(B\<union>C)=(A\<union>B)\<union>C"
  by auto

lemma card_union: "\<lbrakk>finite A; finite B\<rbrakk>\<Longrightarrow>(card B < card (A\<union>B)) \<or> (card B = card (A\<union>B))"
  using psubset_card_mono finite_Un inf_sup_ord(4) psubsetI by metis

lemma card_insert: "\<lbrakk>finite B\<rbrakk>\<Longrightarrow>(card B < card (insert X B)) \<or> (card B = card (insert X B))"
 using psubset_card_mono card_insert_le order_le_imp_less_or_eq by fast

lemma subseteq_card: "\<lbrakk>A\<subseteq>B ; finite B\<rbrakk> \<Longrightarrow> (card A \<le> card B)"
  using card_mono le_eq_less_or_eq by auto

lemma not_occurs_trm: "\<not>occurs X t \<longrightarrow> X\<notin> vars_trm t"
  by (induct t) auto

lemma not_occurs_subst: "\<not>occurs X t1\<longrightarrow> X\<notin> vars_trm (subst [(X,swap pi2 t1)] t2)" 
  using subst_susp not_occurs_trm by (induct t2) auto

lemma not_occurs_list: "\<not> occurs X t \<longrightarrow>
  X \<notin> vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs)"
  using not_occurs_subst apply_subst_eprobs_def by (induct xs) auto

lemma vars_equ: 
  assumes "\<not>occurs X t1" and "occurs X t2"
  shows "vars_trm (subst [(X, swap pi t1)] t2)=(vars_trm t1\<union>vars_trm t2)-{X}"
  using assms
proof(induct t2)
  case (Susp pi X)
  then show ?case sorry
next
  case (Paar t21 t22)
  then show ?case
    using not_occurs_trm subst_not_occurs by fastforce
qed (simp_all)


lemma vars_subseteq:
  assumes "\<not>occurs X t "
  shows "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs) \<subseteq> (vars_trm t \<union> vars_eprobs xs)"
  using assms
proof(induct xs)
  case Nil
  then show ?case sorry
next
  case (Cons a xs)
  then show ?case sorry
qed


lemma vars_decrease: 
  assumes "\<not>occurs X t"
  shows "card (vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs))
                 < card (insert X (vars_trm t \<union> vars_eprobs xs))"
proof(cases "X \<in> (vars_trm t \<union> vars_eprobs xs)")
  case True
  then show ?thesis sorry
next
  case False
  then show ?thesis sorry
qed

lemma rank_cred: 
  assumes "P1\<turnstile>(nabla)\<rightarrow>P2" 
  shows "(rank P2) \<lless> (rank P1)"
  using assms
proof(cases rule: c_red.cases[OF \<open>P1 \<turnstile> nabla \<rightarrow> P2\<close>])
  case (1 a xs)
  then show ?thesis sorry
next
  case (2 a t1 t2 xs)
  then show ?thesis sorry
next
  case (3 a F t xs)
  then show ?thesis sorry
next
  case (4 a t xs)
  then show ?thesis sorry
next
  case (5 a b t xs)
  then show ?thesis sorry
next
  case (6 a b xs)
  then show ?thesis sorry
next
  case (7 a pi X xs)
  then show ?thesis sorry
qed


lemma rank_sred: 
  assumes "P1\<turnstile> s \<leadsto>P2"
  shows "(rank P2) \<lless> (rank P1)"
  using assms
proof(cases rule: s_red.cases[OF \<open>P1\<turnstile> s \<leadsto>P2\<close>])
  case (1 xs ys)
  then show ?thesis sorry
next
  case (2 t1 t2 s1 s2 xs ys)
  then show ?thesis sorry
next
  case (3 F t1 t2 xs ys)
  then show ?thesis sorry
next
  case (4 a t1 t2 xs ys)
  then show ?thesis sorry
next
  case (5 a b t1 t2 xs ys)
  then show ?thesis sorry
next
  case (6 a xs ys)
  then show ?thesis sorry
next
  case (7 pi1 X pi2 xs ys)
  then show ?thesis sorry
next
  case (8 X t pi xs ys)
  then show ?thesis sorry
next
  case (9 X t pi xs ys)
  then show ?thesis sorry
qed


lemma rank_trans: "\<lbrakk>rank P1 \<lless> rank P2; rank P2 \<lless> rank P3\<rbrakk>\<Longrightarrow> rank P1 \<lless> rank P3"
  using measure_relation_def trans_less_than trans_lex_prod transE by metis

(* all reduction are well-founded under \<lless> *)

lemma rank_red_plus: "\<lbrakk>P1\<Turnstile> (s,nabla)\<Rightarrow>P2\<rbrakk> \<Longrightarrow>(rank P2) \<lless> (rank P1)"
apply(erule red_plus.induct)
apply(auto dest: rank_sred rank_cred rank_trans)
done

end

