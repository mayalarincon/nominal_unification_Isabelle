theory Mgu

imports Main  Terms  Fresh  Equ  Substs

begin
(* unification problems *)

(*

syntax
 "_equ_prob"   :: "trm \<Rightarrow> trm \<Rightarrow> (trm\<times>trm)"        ("_ \<approx>? _" [81,81] 81)
 "_fresh_prob" :: "string \<Rightarrow> trm \<Rightarrow> (string\<times>trm)"  ("_ \<sharp>? _" [81,81] 81)

translations 
  "t1 \<approx>? t2" \<rightharpoonup> "(t1,t2)"
  " a \<sharp>? t"  \<rightharpoonup> "(a,t)"*)



(* all solutions for a unification problem *)

type_synonym problem_type = "((trm\<times>trm)list) \<times> ((string\<times>trm)list)"

type_synonym unifier_type = "fresh_envs \<times> substs"

consts 
  U :: "problem_type \<Rightarrow> (unifier_type set)"
defs all_solutions_def : 
  "U P  \<equiv> {(nabla,s). 
             (\<forall> (t1,t2)\<in>set (fst P). nabla \<turnstile> subst s t1 \<approx> subst s t2) \<and> 
             (\<forall>   (a,t)\<in>set (snd P). nabla \<turnstile> a \<sharp> subst s t) }"

(* set of variables in unification problems *)

consts
  vars_fprobs :: "((string\<times>trm) list) \<Rightarrow> (string set)"
  vars_eprobs :: "((trm\<times>trm)list) \<Rightarrow> (string set)"
  vars_probs  :: "problem_type \<Rightarrow> nat"
primrec
  "vars_fprobs [] = {}"
  "vars_fprobs (x#xs) = (vars_trm (snd x))\<union>(vars_fprobs xs)"
primrec
  "vars_eprobs [] = {}"
  "vars_eprobs (x#xs) = (vars_trm (snd x))\<union>(vars_trm (fst x))\<union>(vars_eprobs xs)"
defs
  vars_probs_def: "vars_probs P \<equiv> card((vars_fprobs (snd P))\<union>(vars_eprobs (fst P)))"


(* most general unifier *)

consts 
  mgu :: "problem_type \<Rightarrow> unifier_type \<Rightarrow> bool"
defs mgu_def:
  "mgu P unif \<equiv> 
   \<forall> (nabla,s1)\<in> U P. (\<exists> s2. (nabla\<Turnstile>(subst s2) (fst unif)) \<and> 
                              (nabla\<Turnstile>subst (s2 \<bullet>(snd unif)) \<approx> subst s1))"

(* idempotency of a unifier *)

consts 
  idem :: "unifier_type \<Rightarrow> bool"
defs 
  idem_def: "idem unif \<equiv> (fst unif)\<Turnstile> subst ((snd unif)\<bullet>(snd unif)) \<approx> subst (snd unif)"

(* application of a substitution to a problem *)

consts 
  apply_subst :: "substs \<Rightarrow> problem_type \<Rightarrow> problem_type"
defs apply_subst_def: 
  "apply_subst s P \<equiv> (map (\<lambda>(t1,t2). (subst s t1 \<approx>? subst s t2)) (fst P),
                      map (\<lambda>(a,t).   (a \<sharp>? (subst s t)) ) (snd P))" 

(* equality reductions *)

consts 
  s_red :: "(problem_type \<times> substs \<times> problem_type) set"
syntax 
  "_s_red" :: "problem_type \<Rightarrow> substs \<Rightarrow> problem_type \<Rightarrow> bool"  ("_ \<turnstile> _ \<leadsto> _ " [80,80,80] 80)
translations "P1 \<turnstile>sigma\<leadsto> P2" \<rightleftharpoons> "(P1,sigma,P2)\<in>s_red"
inductive s_red
intros
  unit_sred[intro!,dest!]:    "((Unit\<approx>?Unit)#xs,ys) \<turnstile>[]\<leadsto> (xs,ys)"
  paar_sred[intro!,dest!]:    "((Paar t1 t2\<approx>?Paar s1 s2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?s1)#(t2\<approx>?s2)#xs,ys)"
  func_sred[intro!,dest!]:    "((Func F t1\<approx>?Func F t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?t2)#xs,ys)"
  abst_aa_sred[intro!,dest!]: "((Abst a t1\<approx>?Abst a t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?t2)#xs,ys)"
  abst_ab_sred[intro!]: "a\<noteq>b\<Longrightarrow> 
                       ((Abst a t1\<approx>?Abst b t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1\<approx>?swap [(a,b)] t2)#xs,(a\<sharp>?t2)#ys)"
  atom_sred[intro!,dest!]:    "((Atom a\<approx>?Atom a)#xs,ys) \<turnstile>[]\<leadsto> (xs,ys)"  
  susp_sred[intro!,dest!]:    "((Susp pi1 X\<approx>?Susp pi2 X)#xs,ys) 
                                \<turnstile>[]\<leadsto> (xs,(map (\<lambda>a. a\<sharp>? Susp [] X) (ds_list pi1 pi2))@ys)"
  var_1_sred[intro!]:   "\<not>(occurs X t)\<Longrightarrow>((Susp pi X\<approx>?t)#xs,ys)
                               \<turnstile>[(X,swap (rev pi) t)]\<leadsto> apply_subst [(X,swap (rev pi) t)] (xs,ys)"
  var_2_sred[intro!]:   "\<not>(occurs X t)\<Longrightarrow>((t\<approx>?Susp pi X)#xs,ys) 
                               \<turnstile>[(X,swap (rev pi) t)]\<leadsto> apply_subst [(X,swap (rev pi) t)] (xs,ys)"

(* freshness reductions *)

consts 
  c_red :: "(problem_type \<times> fresh_envs \<times> problem_type) set"
syntax 
  "_c_red" :: "problem_type \<Rightarrow> fresh_envs \<Rightarrow> problem_type \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow> _ " [80,80,80] 80)
translations "P1 \<turnstile>nabla\<rightarrow> P2" \<rightleftharpoons> "(P1,nabla,P2)\<in>c_red"
inductive c_red
intros
  unit_cred[intro!]:    "([],(a \<sharp>? Unit)#xs) \<turnstile>{}\<rightarrow> ([],xs)"
  paar_cred[intro!]:    "([],(a \<sharp>? Paar t1 t2)#xs) \<turnstile>{}\<rightarrow> ([],(a\<sharp>?t1)#(a\<sharp>?t2)#xs)"
  func_cred[intro!]:    "([],(a \<sharp>? Func F t)#xs) \<turnstile>{}\<rightarrow> ([],(a\<sharp>?t)#xs)"
  abst_aa_cred[intro!]: "([],(a \<sharp>? Abst a t)#xs) \<turnstile>{}\<rightarrow> ([],xs)"
  abst_ab_cred[intro!]: "a\<noteq>b\<Longrightarrow>([],(a \<sharp>? Abst b t)#xs) \<turnstile>{}\<rightarrow> ([],(a\<sharp>?t)#xs)"
  atom_cred[intro!]:    "a\<noteq>b\<Longrightarrow>([],(a \<sharp>? Atom b)#xs) \<turnstile>{}\<rightarrow> ([],xs)"  
  susp_cred[intro!]:    "([],(a \<sharp>? Susp pi X)#xs) \<turnstile>{((swapas (rev pi) a),X)}\<rightarrow> ([],xs)" 

(* unification reduction sequence *)

consts 
  red_plus :: "(problem_type \<times> unifier_type \<times> problem_type) set"
syntax 
  red_plus :: "problem_type \<Rightarrow> unifier_type \<Rightarrow> problem_type \<Rightarrow> bool" ("_ \<Turnstile> _ \<Rightarrow> _ " [80,80,80] 80)

translations "P1 \<Turnstile>(nabla,s)\<Rightarrow> P2" \<rightleftharpoons> "(P1,(nabla,s),P2)\<in>red_plus"
inductive red_plus
intros
  sred_single[intro!]: "\<lbrakk>P1\<turnstile>s1\<leadsto>P2\<rbrakk>\<Longrightarrow>P1\<Turnstile>({},s1)\<Rightarrow>P2"
  cred_single[intro!]: "\<lbrakk>P1\<turnstile>nabla1\<rightarrow>P2\<rbrakk>\<Longrightarrow>P1\<Turnstile>(nabla1,[])\<Rightarrow>P2"
  sred_step[intro!]:   "\<lbrakk>P1\<turnstile>s1\<leadsto>P2;P2\<Turnstile>(nabla2,s2)\<Rightarrow>P3\<rbrakk>\<Longrightarrow>P1\<Turnstile>(nabla2,(s2\<bullet>s1))\<Rightarrow>P3"
  cred_step[intro!]:   "\<lbrakk>P1\<turnstile>nabla1\<rightarrow>P2;P2\<Turnstile>(nabla2,[])\<Rightarrow>P3\<rbrakk>\<Longrightarrow>P1\<Turnstile>(nabla2\<union>nabla1,[])\<Rightarrow>P3"

lemma mgu_idem: 
  "\<lbrakk>(nabla1,s1)\<in>U P; 
   \<forall>(nabla2,s2)\<in> U P. nabla2\<Turnstile>(subst s2) nabla1 \<and>  nabla2\<Turnstile>subst(s2 \<bullet> s1)\<approx>subst s2 \<rbrakk>\<Longrightarrow>
   mgu P (nabla1,s1)\<and>idem (nabla1,s1)"
apply(rule conjI)
apply(simp only: mgu_def)
apply(rule ballI)
apply(simp)
apply(drule_tac x="x" in bspec)
apply(assumption)
apply(force)
apply(drule_tac x="(nabla1,s1)" in bspec)
apply(assumption)
apply(simp add: idem_def)
done

lemma problem_subst_comm: "((nabla,s2)\<in>U (apply_subst s1 P)) = ((nabla,(s2\<bullet>s1))\<in>U P)"
apply(simp add: all_solutions_def apply_subst_def)
apply(auto)
apply(drule_tac x="(a,b)" in bspec, assumption, simp add: subst_comp_expand)+
done

lemma P1_to_P2_sred: 
  "\<lbrakk>(nabla1,s1)\<in>U P1; P1 \<turnstile>s2\<leadsto> P2 \<rbrakk>\<Longrightarrow>((nabla1,s1)\<in>U P2) \<and> (nabla1\<Turnstile>subst (s1\<bullet>s2)\<approx>subst s1)"
apply(ind_cases "P1 \<turnstile>s2\<leadsto> P2")
apply(simp_all)
--Unit
apply(force intro!: equ_refl simp add: all_solutions_def ext_subst_def subst_equ_def subst_susp)
--Paar
apply(simp add: all_solutions_def ext_subst_def subst_equ_def subst_susp)
apply(force intro!: equ_refl dest!: equ_paar_elim)
--Func
apply(simp add: all_solutions_def ext_subst_def subst_equ_def subst_susp)
apply(force intro!: equ_refl dest!: equ_func_elim)
--Abst.aa
apply(simp add: all_solutions_def ext_subst_def subst_equ_def subst_susp)
apply(force intro!: equ_refl dest!: equ_abst_aa_elim)
--Abst.ab
apply(simp add: all_solutions_def ext_subst_def subst_equ_def subst_susp)
apply(force intro!: equ_refl dest!: equ_abst_ab_elim simp add: subst_swap_comm)
--Atom
apply(simp add: all_solutions_def ext_subst_def subst_equ_def subst_susp)
apply(force intro!: equ_refl)
--Susp
apply(rule conjI)
apply(auto)
apply(simp add: all_solutions_def)
apply(erule conjE)+
apply(simp add: ds_list_equ_ds)
apply(simp only: subst_susp)
apply(drule equ_pi1_pi2_dec[THEN mp])
apply(auto)
apply(drule_tac x="aa" in bspec)
apply(assumption)
apply(simp add: subst_susp)
apply(simp add: subst_equ_def subst_susp)
apply(rule ballI)
apply(rule equ_refl)
--Var.one
apply(drule_tac "t2.1"="swap (rev pi) t" in subst_not_occurs[THEN mp])
apply(simp only: problem_subst_comm)
apply(simp add: all_solutions_def ext_subst_def subst_equ_def)
apply(rule conjI)
apply(rule ballI)
apply(erule conjE)+
apply(drule unif_1)
apply(clarify)
apply(drule_tac x="(a,b)" in bspec)
apply(assumption)
apply(simp)
apply(simp add: unif_2a)
apply(erule conjE)+
apply(drule unif_1)
apply(rule ballI)
apply(clarify)
apply(drule_tac x="(a,b)" in bspec)
apply(assumption)
apply(simp)
apply(simp add: unif_2b)
apply(rule unif_1)
apply(simp add: all_solutions_def)
--Var.two
apply(drule_tac "t2.1"="swap (rev pi) t" in subst_not_occurs[THEN mp])
apply(simp only: problem_subst_comm)
apply(simp add: all_solutions_def ext_subst_def subst_equ_def)
apply(auto)
apply(drule_tac x="(a,b)" in bspec)
apply(assumption)
apply(simp)
apply(drule equ_sym)
apply(drule unif_1)
apply(simp add: unif_2a)
apply(drule_tac x="(a,b)" in bspec)
apply(assumption)
apply(simp)
apply(drule equ_sym)
apply(drule unif_1)
apply(simp add: unif_2b)
apply(rule unif_1)
apply(rule equ_sym)
apply(simp add: all_solutions_def)
done

lemma P1_from_P2_sred: "\<lbrakk>(nabla1,s1)\<in>U P2; P1\<turnstile>s2\<leadsto>P2\<rbrakk>\<Longrightarrow>(nabla1,s1\<bullet>s2)\<in>U P1"
apply(ind_cases "P1 \<turnstile>s2\<leadsto> P2")
--Susp.Paar.Func.Abst.aa
apply(simp add: all_solutions_def, force)
apply(simp add: all_solutions_def, force)
apply(simp add: all_solutions_def, force)
apply(simp add: all_solutions_def, force)
--Abst.ab
apply(simp only: all_solutions_def)
apply(force simp add: subst_swap_comm)
--Atom
apply(simp only: all_solutions_def, force)
--Susp
apply(simp)
apply(auto)
apply(simp add: all_solutions_def)
apply(simp add: ds_list_equ_ds)
apply(subgoal_tac "nabla1\<turnstile>(swap pi1 (subst s1 (Susp [] X)))\<approx>(swap pi2 (subst s1 (Susp [] X)))")
apply(simp add: subst_susp subst_swap_comm)
apply(simp add: subst_susp subst_swap_comm)
apply(rule equ_pi1_pi2_add[THEN mp])
apply(drule conjunct2)
apply(auto)
apply(drule_tac x="(a,Susp [] X)" in bspec)
apply(auto)
apply(simp add: subst_susp)
--Var.one
apply(simp only: problem_subst_comm)
apply(simp only: all_solutions_def)
apply(simp)
apply(simp only: subst_comp_expand)
apply(subgoal_tac "subst [(X, swap (rev pi) t)] t = t")--A
apply(simp add: subst_susp)
apply(simp only: subst_swap_comm)
apply(simp only: equ_pi_to_right[THEN sym])
apply(simp only: equ_involutive_right)
apply(rule equ_refl)
--A
apply(rule subst_not_occurs[THEN mp])
apply(assumption)
--Var.two
apply(simp only: problem_subst_comm)
apply(simp only: all_solutions_def)
apply(simp)
apply(simp only: subst_comp_expand)
apply(subgoal_tac "subst [(X, swap (rev pi) t)] t = t")--B
apply(simp add: subst_susp)
apply(simp only: subst_swap_comm)
apply(simp only: equ_pi_to_left[THEN sym])
apply(simp only: equ_involutive_left)
apply(rule equ_refl)
--B
apply(rule subst_not_occurs[THEN mp])
apply(assumption)
done

lemma P1_to_P2_cred: 
  "\<lbrakk>(nabla1,s1)\<in>U P1; P1 \<turnstile>nabla2\<rightarrow> P2 \<rbrakk>\<Longrightarrow>((nabla1,s1)\<in>U P2) \<and> (nabla1\<Turnstile>(subst s1) nabla2)"
apply(ind_cases " P1\<turnstile>nabla2\<rightarrow>P2")
apply(simp_all)
apply(auto simp add: ext_subst_def all_solutions_def)
apply(rule fresh_swap_left[THEN mp])
apply(simp add: subst_swap_comm[THEN sym] subst_susp)
done

lemma P1_from_P2_cred: 
  "\<lbrakk>(nabla1,s1)\<in>U P2; P1 \<turnstile>nabla2\<rightarrow> P2; nabla3\<Turnstile>(subst s1) nabla2\<rbrakk>\<Longrightarrow>(nabla1\<union>nabla3,s1)\<in>U P1"
apply(ind_cases "P1 \<turnstile>nabla2\<rightarrow> P2")
apply(simp_all)
apply(auto simp add: ext_subst_def all_solutions_def fresh_weak)
apply(simp add: subst_susp)
apply(rule fresh_swap_right[THEN mp])
apply(drule_tac "nabla2.1"="nabla1" in fresh_weak[THEN mp])
apply(subgoal_tac "nabla3 \<union> nabla1=nabla1 \<union> nabla3")--A
apply(simp)
apply(rule Un_commute)
done

lemma P1_to_P2_red_plus: "\<lbrakk>P1 \<Turnstile>(nabla,s)\<Rightarrow>P2\<rbrakk>\<Longrightarrow> (nabla1,s1)\<in>U P1 \<longrightarrow>
  ((nabla1,s1)\<in>U P2)\<and>(nabla1\<Turnstile>subst (s1\<bullet>s)\<approx>subst s1)\<and>(nabla1\<Turnstile>(subst s1) nabla)"
apply(erule red_plus.induct)
-- sred
apply(rule impI)
apply(drule_tac "P2.0"="P2" and "s2.0"="s1a" in P1_to_P2_sred)
apply(force)
apply(rule conjI, force)+
apply(force simp add: ext_subst_def)
-- cred
apply(rule impI)
apply(drule_tac "P2.0"="P2" and "nabla2.0"="nabla1a" in P1_to_P2_cred)
apply(assumption)
apply(force intro!: equ_refl simp add: subst_equ_def)
-- sred
apply(rule impI)
apply(drule_tac "P2.0"="P2" and "s2.0"="s1a" in P1_to_P2_sred)
apply(assumption)
apply(erule conjE)+
apply(rule conjI)
apply(force)
apply(rule conjI)
apply(drule mp)
apply(assumption)
apply(erule conjE)+
apply(rule_tac "s2.0"="((s1\<bullet>s2)\<bullet>s1a)" in subst_trans)
apply(simp only: subst_assoc subst_equ_def)
apply(rule ballI)
apply(rule equ_refl)
apply(rule_tac "s2.0"="(s1\<bullet>s1a)" in subst_trans)
apply(rule subst_cancel_right)
apply(assumption)
apply(assumption)
apply(force)
-- cred
apply(rule impI)
apply(drule_tac "P2.0"="P2" and "nabla2.0"="nabla1a" in P1_to_P2_cred)
apply(auto simp add: ext_subst_def)
done

lemma P1_from_P2_red_plus: "\<lbrakk>P1 \<Turnstile>(nabla,s)\<Rightarrow>P2\<rbrakk>\<Longrightarrow>(nabla1,s1)\<in>U P2\<longrightarrow>
        nabla3\<Turnstile>(subst s1)(nabla)\<longrightarrow>(nabla1\<union>nabla3,(s1\<bullet>s))\<in>U P1"
apply(erule red_plus.induct)
-- sred
apply(rule impI)+
apply(drule_tac "P1.0"="P1" and "s2.0"="s1a" in P1_from_P2_sred)
apply(assumption)
apply(force simp only: all_solutions_def equ_weak fresh_weak)
-- cred
apply(rule impI)+
apply(drule_tac "P1.0"="P1" and "nabla3.0"="nabla3" and "nabla2.0"="nabla1a" in P1_from_P2_cred)
apply(assumption)+
apply(simp add: all_solutions_def)
-- sred
apply(rule impI)+
apply(simp)
apply(drule_tac "P1.0"="P1" and "P2.0"="P2" and "s2.0"="s1a" in P1_from_P2_sred)
apply(assumption)
apply(simp add: all_solutions_def subst_assoc)
-- cred
apply(rule impI)+
apply(subgoal_tac "nabla3 \<Turnstile> (subst s1) nabla2")--A
apply(simp)
apply(drule_tac "P1.0"="P1" and "P2.0"="P2" and
                "nabla2.0"="nabla1a" and "nabla3.0"="nabla3" in P1_from_P2_cred)
apply(assumption)
apply(simp)
apply(simp add: ext_subst_def)
apply(subgoal_tac "nabla1 \<union> nabla3 \<union> nabla3=nabla1 \<union> nabla3")--A
apply(simp)
--A
apply(force)
--B
apply(simp add: ext_subst_def)
done

lemma mgu: "\<lbrakk>P \<Turnstile>(nabla,s)\<Rightarrow>([],[])\<rbrakk>\<Longrightarrow> mgu P (nabla,s) \<and> idem (nabla,s)"
apply(frule_tac "nabla3.2"="nabla" and "nabla2"="nabla" and 
                "s1.2"="[]" and "nabla1.2"="{}"
                in P1_from_P2_red_plus[THEN mp,THEN mp])
apply(force simp add: all_solutions_def)
apply(force simp add: ext_subst_def)
apply(rule mgu_idem)
apply(simp add: all_solutions_def)
apply(rule ballI)
apply(clarify)
apply(drule_tac  "nabla1.0"="a" and "s1.0"="b"in P1_to_P2_red_plus)
apply(simp)
done  

end









