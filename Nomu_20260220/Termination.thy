

theory Termination = Main + Terms + Fresh + Equ + Substs + Mgu:

(* set of variables *)

consts 
  vars_trm    :: "trm \<Rightarrow> string set"
  vars_eprobs :: "eprobs \<Rightarrow> (string set)"
primrec
  "vars_trm (Unit)       = {}"
  "vars_trm (Atom a)     = {}"
  "vars_trm (Susp pi X)  = {X}"
  "vars_trm (Paar t1 t2) = (vars_trm t1)\<union>(vars_trm t2)"
  "vars_trm (Abst a t)   = vars_trm t"
  "vars_trm (Func F t)   = vars_trm t"
primrec
  "vars_eprobs [] = {}"
  "vars_eprobs (x#xs) = (vars_trm (snd x))\<union>(vars_trm (fst x))\<union>(vars_eprobs xs)"

lemma[simp]: "vars_trm (swap pi t) = vars_trm t"
apply(induct_tac t)
apply(auto)
done

consts 
  size_trm    :: "trm \<Rightarrow> nat"
  size_fprobs :: "fprobs \<Rightarrow> nat"
  size_eprobs :: "eprobs \<Rightarrow> nat"
  size_probs  :: "probs \<Rightarrow> nat"
primrec
  "size_trm (Unit)      = 1"
  "size_trm (Atom a)    = 1"
  "size_trm (Susp pi X) = 1"
  "size_trm (Abst a t)  = 1 + size_trm t"
  "size_trm (Func F t)  = 1 + size_trm t"
  "size_trm (Paar t t') = 1 + (size_trm t) + (size_trm t')"
primrec
  "size_fprobs [] = 0"
  "size_fprobs (x#xs) = (size_trm (snd x))+(size_fprobs xs)"
primrec
  "size_eprobs [] = 0"
  "size_eprobs (x#xs) = (size_trm (fst x))+(size_trm (snd x))+(size_eprobs xs)"

lemma[simp]: "size_trm (swap pi t) = size_trm t"
apply(induct_tac t)
apply(auto)
done

syntax        
  "_measure_relation" :: "(nat\<times>nat\<times>nat) \<Rightarrow> (nat\<times>nat\<times>nat) \<Rightarrow> bool" ("_ \<lless> _" [80,80] 80)
translations
  "n1 \<lless> n2"  \<rightleftharpoons> "(n1,n2) \<in> (less_than<*lex*>less_than<*lex*>less_than)"

consts 
  rank :: "probs \<Rightarrow> (nat\<times>nat\<times>nat)"
primrec
  "rank (eprobs,fprobs) = (card (vars_eprobs eprobs),size_eprobs eprobs,size_fprobs fprobs)" 

lemma[simp]: "finite (vars_trm t)"
apply(induct t)
apply(auto)
done

lemma[simp]: "finite (vars_eprobs P)"
apply(induct_tac P)
apply(auto)
done

lemma union_comm: "A\<union>(B\<union>C)=(A\<union>B)\<union>C"
apply(auto)
done

lemma card_union: "\<lbrakk>finite A; finite B\<rbrakk>\<Longrightarrow>(card B < card (A\<union>B)) \<or> (card B = card (A\<union>B))"
apply(auto)
apply(rule psubset_card_mono)
apply(auto)
done

lemma card_insert: "\<lbrakk>finite B\<rbrakk>\<Longrightarrow>(card B < card (insert X B)) \<or> (card B = card (insert X B))"
apply(auto)
apply(rule psubset_card_mono)
apply(auto)
done

lemma subseteq_card: "\<lbrakk>A\<subseteq>B; finite B\<rbrakk>\<Longrightarrow>(card A \<le> card B)"
apply(drule_tac A="A" in card_mono)
apply(auto simp add: le_eq_less_or_eq)
done

lemma not_occurs_trm: "\<not>occurs X t \<longrightarrow> X\<notin> vars_trm t"
apply(induct_tac t)
apply(auto)
done

lemma not_occurs_subst: "\<not>occurs X t1\<longrightarrow> X\<notin> vars_trm (subst [(X,swap pi2 t1)] t2)" 
apply(induct_tac t2)
apply(auto simp add: subst_susp not_occurs_trm)
done

lemma not_occurs_list: "\<not>occurs X t \<longrightarrow>
  X\<notin> vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs)"
apply(induct_tac xs)
apply(simp)
apply(case_tac a)
apply(auto simp add: not_occurs_subst)
done

lemma vars_equ: "\<not>occurs X t1 \<and> occurs X t2\<longrightarrow> 
  vars_trm (subst [(X, swap pi t1)] t2)=(vars_trm t1\<union>vars_trm t2)-{X}"
apply(induct_tac t2)
apply(force)
apply(case_tac "X=list2")
apply(simp add: subst_susp not_occurs_trm)
apply(simp)
apply(simp)
apply(simp)
apply(simp)
apply(rule conjI)
apply(case_tac "occurs X trm2")
apply(force)
apply(force dest: not_occurs_trm[THEN mp] simp add: subst_not_occurs)
apply(force dest: not_occurs_trm[THEN mp] simp add: subst_not_occurs)
apply(force)
done

lemma vars_subseteq: "\<not>occurs X t \<longrightarrow>
  vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs) \<subseteq> (vars_trm t \<union> vars_eprobs xs)"
apply(induct_tac xs)
apply(simp)
apply(rule impI)
apply(simp)
apply(case_tac "occurs X (fst a)")
apply(case_tac "occurs X (snd a)")
apply(simp add: vars_equ[THEN mp])
apply(force)
apply(simp add: subst_not_occurs)
apply(force simp add: vars_equ)
apply(case_tac "occurs X (snd a)")
apply(simp add: vars_equ[THEN mp])
apply(force simp add: subst_not_occurs)
apply(force simp add: subst_not_occurs)
done

lemma vars_decrease: 
  "\<not>occurs X t\<longrightarrow> card (vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs))
                 <card (insert X (vars_trm t \<union> vars_eprobs xs))"
apply(rule impI)
apply(case_tac "X\<in>(vars_trm t \<union> vars_eprobs xs)")
(* first case *)
apply(subgoal_tac "insert X (vars_trm t \<union> vars_eprobs xs) = (vars_trm t \<union> vars_eprobs xs)") (*A*)
apply(simp)
apply(frule_tac pi1="pi" and xs1="xs" in vars_subseteq[THEN mp])
apply(frule_tac pi1="pi" and xs1="xs" in not_occurs_list[THEN mp])
apply(subgoal_tac "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs)
                   \<subset>  vars_trm t \<union> vars_eprobs xs") (* B *)
apply(simp add: psubset_card_mono)
(* B *)
apply(force)
(* A *)
apply(force)
(* second case *)
apply(subgoal_tac "finite (vars_trm t \<union> vars_eprobs xs)")
apply(drule_tac x="X" in card_insert_disjoint)
apply(simp)
apply(simp)
apply(frule_tac pi1="pi" and xs1="xs" in vars_subseteq[THEN mp])
apply(auto dest: subseteq_card)
done

lemma rank_cred: "\<lbrakk>P1\<turnstile>(nabla)\<rightarrow>P2\<rbrakk>\<Longrightarrow>(rank P2) \<lless> (rank P1)"
apply(ind_cases "P1 \<turnstile> nabla \<rightarrow> P2")
apply(simp_all add: lex_prod_def)
done

lemma rank_sred: "\<lbrakk>P1\<turnstile>(s)\<leadsto>P2\<rbrakk>\<Longrightarrow>(rank P2) \<lless> (rank P1)"
apply(ind_cases "P1 \<turnstile> s \<leadsto> P2")
apply(simp_all add: lex_prod_def union_comm)
apply(subgoal_tac 
  "vars_trm s1\<union>vars_trm t1\<union>vars_trm s2\<union>vars_trm t2\<union>vars_eprobs xs = 
   vars_trm s1\<union>vars_trm s2\<union>vars_trm t1\<union>vars_trm t2\<union>vars_eprobs xs") (*A*)
apply(simp)
(* A *)
apply(force)
(* Susp-Susp case *)
apply(simp add: card_insert)
(* variable elimination cases *)
apply(simp_all add: apply_subst_def vars_decrease)
done


lemma rank_trans: "\<lbrakk>rank P1 \<lless> rank P2; rank P2 \<lless> rank P3\<rbrakk>\<Longrightarrow>rank P1 \<lless> rank P3"
apply(simp add: lex_prod_def)
apply(auto)
done

(* all reduction are well-founded under \<lless> *)

lemma rank_red_plus: "\<lbrakk>P1\<Turnstile>(s,nabla)\<Rightarrow>P2\<rbrakk>\<Longrightarrow>(rank P2) \<lless> (rank P1)"
apply(erule red_plus.induct)
apply(auto dest: rank_sred rank_cred rank_trans)
done

end

