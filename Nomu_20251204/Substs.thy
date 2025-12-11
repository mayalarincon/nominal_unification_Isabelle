

theory Substs

imports Main  Terms  PreEqu  Equ

begin

(* substitutions *)

type_synonym substs = "(string \<times> trm)list"

fun look_up :: "string \<Rightarrow> substs \<Rightarrow> trm" where
  "look_up X []     = Susp [] X" |
  "look_up X (x#xs) = (if (X = fst x) then (snd x) else look_up X xs)"

fun subst :: "substs \<Rightarrow> trm \<Rightarrow> trm" where
  subst_unit: "subst s (Unit)          = Unit" |
  subst_susp: "subst s (Susp pi X)     = swap pi (look_up X s)" |
  subst_atom: "subst s (Atom a)        = Atom a" |
  subst_abst: "subst s (Abst a t)      = Abst a (subst s t)" |
  subst_paar: "subst s (Paar t1 t2)    = Paar (subst s t1) (subst s t2)" |
  subst_func: "subst s (Func F t)      = Func F (subst s t)"

declare subst_susp [simp del]

(* composition of substitutions (adapted from Martin Coen) *)

fun alist_rec :: "substs \<Rightarrow> substs \<Rightarrow> (string\<Rightarrow>trm\<Rightarrow>substs\<Rightarrow>substs\<Rightarrow>substs) \<Rightarrow> substs" where
  "alist_rec [] c d = c" |
  "alist_rec (p#al) c d = d (fst p) (snd p) al (alist_rec al c d)"

definition comp ::  "substs \<Rightarrow> substs \<Rightarrow> substs" (infixl \<open>\<bullet>\<close> 81) where
 "s1 \<bullet> s2 \<equiv> alist_rec s2 s1 (\<lambda> x y xs g. (x,subst s1 y)#g)"

(* domain of substitutions *)

definition domn :: "(trm \<Rightarrow> trm) \<Rightarrow> string set" where
  "domn s \<equiv> {X. (s (Susp [] X)) \<noteq> (Susp [] X)}" 

(* substitutions extending freshness environments *)

definition ext_subst :: "fresh_envs \<Rightarrow> (trm \<Rightarrow> trm) \<Rightarrow> fresh_envs \<Rightarrow> bool" (" _ \<Turnstile> _ _ " [80,80,80] 80) where
  "nabla1 \<Turnstile> s (nabla2) \<equiv> (\<forall>(a,X)\<in>nabla2. nabla1\<turnstile>a\<sharp> s (Susp [] X))"

(* alpha-equality for substitutions *)

definition subst_equ :: "fresh_envs \<Rightarrow> (trm\<Rightarrow>trm) \<Rightarrow> (trm\<Rightarrow>trm) \<Rightarrow> bool" (" _ \<Turnstile> _ \<approx> _" [80,80,80] 80)
  where
  "nabla \<Turnstile> s1 \<approx> s2 \<equiv>  \<forall>X\<in>(domn s1\<union>domn s2). (nabla \<turnstile> s1 (Susp [] X) \<approx> s2 (Susp [] X))"

lemma not_in_domn: "X\<notin>(domn s)\<Longrightarrow> (s (Susp [] X)) = (Susp [] X)"
apply(auto simp only: domn_def)
done

lemma subst_swap_comm: "subst s (swap pi t) = swap pi (subst s t)"
apply(induct_tac t)
apply(auto simp add: swap_append subst_susp)
done

lemma subst_not_occurs: "\<not>(occurs X t) \<longrightarrow> subst [(X,t2)] t = t"
apply(induct t)
apply(auto simp add: subst_susp)
done

lemma [simp]: "subst [] t = t"
apply(induct_tac t, auto simp add: subst_susp)
done

lemma [simp]: "subst (s\<bullet>[]) = subst s"
apply(auto simp add: comp_def)
done

lemma [simp]: "subst ([]\<bullet>s) = subst s"
apply(rule ext)
apply(induct_tac x)
apply(auto)
apply(induct_tac s rule: alist_rec.induct)
apply(auto simp add: comp_def subst_susp)
done

lemma subst_comp_expand: "subst (s1\<bullet>s2) t = subst s1 (subst s2 t)"
apply(induct_tac t)
apply(auto)
apply(induct_tac s2 rule: alist_rec.induct)
apply(auto simp add: comp_def subst_susp subst_swap_comm)
done

lemma subst_assoc: "subst (s1\<bullet>(s2\<bullet>s3))=subst ((s1\<bullet>s2)\<bullet>s3)"
apply(rule ext)
apply(induct_tac x)
apply(auto)
apply(simp add: subst_comp_expand)
done

lemma fresh_subst: "nabla1\<turnstile>a\<sharp>t\<Longrightarrow> nabla2\<Turnstile>(subst s) nabla1 \<longrightarrow> nabla2\<turnstile>a\<sharp>subst s t"
apply(erule fresh.induct)
apply(auto)
--Susp
apply(simp add: ext_subst_def subst_susp)
apply(drule_tac x="(swapas (rev pi) a, X)" in bspec)
apply(assumption)
apply(simp)
apply(rule fresh_swap_right[THEN mp])
apply(assumption)
done

lemma equ_subst: "nabla1\<turnstile>t1\<approx>t2\<Longrightarrow> nabla2\<Turnstile> (subst s) nabla1 \<longrightarrow> nabla2\<turnstile>(subst s t1)\<approx>(subst s t2)"
apply(erule equ.induct)
apply(auto)
apply(rule_tac "nabla1.1"="nabla" in fresh_subst[THEN mp])
apply(assumption)+
apply(simp add: subst_swap_comm)
-- Susp
apply(simp only: subst_susp)
apply(rule equ_pi1_pi2_add[THEN mp])
apply(simp only: ext_subst_def subst_susp)
apply(force)
done

lemma unif_1: 
  "\<lbrakk>nabla\<turnstile>subst s (Susp pi X)\<approx>subst s t\<rbrakk>\<Longrightarrow> nabla\<Turnstile> subst (s\<bullet>[(X,swap (rev pi) t)])\<approx>subst s"
apply(simp only: subst_equ_def)
apply(case_tac "pi=[]")
apply(simp add: subst_susp comp_def)
apply(force intro: equ_sym equ_refl)
apply(subgoal_tac "domn (subst (s\<bullet>[(X,swap (rev pi) t)]))=domn(subst s)\<union>{X}")--A
apply(simp)
apply(rule conjI)
apply(simp add: subst_comp_expand)
apply(simp add: subst_susp)
apply(simp only: subst_swap_comm)
apply(simp only: equ_pi_to_left)
apply(rule equ_sym)
apply(assumption)
apply(rule ballI)
apply(simp only: subst_comp_expand)
apply(simp add: subst_susp)
apply(force intro: equ_sym equ_refl simp add: subst_swap_comm equ_pi_to_left)
--A
apply(simp only: domn_def)
apply(auto)
apply(simp add: subst_comp_expand)
apply(simp add: subst_susp subst_swap_comm)
apply(simp only: subst_comp_expand)
apply(simp add: subst_susp subst_swap_comm)
apply(drule swap_empty[THEN mp])
apply(simp)
apply(simp only: subst_comp_expand)
apply(simp only: subst_susp)
apply(auto)
apply(case_tac "x=X")
apply(simp)
apply(simp add: subst_swap_comm)
apply(drule swap_empty[THEN mp])
apply(simp)
apply(simp add: subst_susp)
done

lemma subst_equ_a:
"\<lbrakk>nabla\<Turnstile>(subst s1) \<approx> (subst s2)\<rbrakk>\<Longrightarrow> \<forall>t2. nabla\<turnstile>(subst s2 t1)\<approx>t2 \<longrightarrow> nabla\<turnstile>(subst s1 t1)\<approx>t2"
apply(rule allI)
apply(induct t1)
--Abst.ab
apply(rule impI)
apply(simp)
apply(ind_cases "nabla \<turnstile> Abst list (subst s1 trm) \<approx> t2")
apply(best)
--Abst.aa
apply(force)
--Susp
apply(rule impI)
apply(simp only: subst_equ_def)
apply(case_tac "list2\<in>domn (subst s1) \<union> domn (subst s2)")
apply(drule_tac x="list2" in bspec)
apply(assumption)
apply(simp)
apply(subgoal_tac "nabla \<turnstile> subst s2 (Susp [] list2) \<approx> swap (rev list1) t2")--A
apply(drule_tac "t1.0"="subst s1 (Susp [] list2)" and
                "t2.0"="subst s2 (Susp [] list2)" and 
                "t3.0"="swap (rev list1) t2" in equ_trans)
apply(assumption)
apply(simp only: equ_pi_to_right)
apply(simp add: subst_swap_comm[THEN sym])
--A
apply(simp only: equ_pi_to_right)
apply(simp add: subst_swap_comm[THEN sym])
apply(simp)
apply(erule conjE)
apply(drule not_in_domn)+
apply(subgoal_tac "subst s1 (Susp list1 list2)=swap list1 (subst s1 (Susp [] list2))")--B
apply(subgoal_tac "subst s2 (Susp list1 list2)=swap list1 (subst s2 (Susp [] list2))")--C
apply(simp)
--BC
apply(simp (no_asm) add: subst_swap_comm[THEN sym])
apply(simp (no_asm) add: subst_swap_comm[THEN sym])
--Unit
apply(force)
--Atom
apply(force)
--Paar
apply(rule impI)
apply(simp)
apply(ind_cases "nabla \<turnstile> Paar (subst sigma1 trm1) (subst sigma1 trm2) \<approx> t2")
apply(best)
--Func
apply(rule impI)
apply(simp)
apply(ind_cases "nabla \<turnstile> Func list (subst sigma1 trm) \<approx> t2")
apply(best)
done

lemma unif_2a: "\<lbrakk>nabla\<Turnstile>subst s1\<approx>subst s2\<rbrakk>\<Longrightarrow> 
                (nabla\<turnstile>subst s2 t1 \<approx> subst s2 t2)\<longrightarrow>(nabla\<turnstile>subst s1 t1 \<approx> subst s1 t2)"
apply(rule impI)
apply(frule_tac "t1.0"="t1" in subst_equ_a)
apply(drule_tac x="subst s2 t2" in spec)
apply(simp)
apply(drule equ_sym)
apply(drule equ_sym) 
apply(frule_tac "t1.0"="t2" in subst_equ_a)
apply(drule_tac x="subst s1 t1" in spec)
apply(rule equ_sym)
apply(simp)
done


lemma unif_2b: "\<lbrakk>nabla\<Turnstile>subst s1\<approx> subst s2\<rbrakk>\<Longrightarrow>nabla\<turnstile>a\<sharp> subst s2 t\<longrightarrow>nabla\<turnstile>a\<sharp>subst s1 t"
apply(induct t)
--Abst
apply(simp)
apply(rule impI)
apply(case_tac "a=list")
apply(force)
apply(force dest!: fresh_abst_ab_elim)
--Susp
apply(rule impI)
apply(subgoal_tac "subst s1 (Susp list1 list2)= swap list1 (subst s1 (Susp [] list2))")--A
apply(subgoal_tac "subst s2 (Susp list1 list2)= swap list1 (subst s2 (Susp [] list2))")--B
apply(simp add: subst_equ_def)
apply(case_tac "list2\<in>domn (subst s1) \<union> domn (subst s2)")
apply(drule_tac x="list2" in bspec)
apply(assumption)
apply(rule fresh_swap_right[THEN mp])
apply(rule_tac "t1.1"=" subst s2 (Susp [] list2)" in l3_jud[THEN mp])
apply(rule equ_sym)
apply(simp)
apply(rule fresh_swap_left[THEN mp])
apply(simp)
apply(simp)
apply(erule conjE)
apply(drule not_in_domn)+
apply(simp add: subst_swap_comm)
--AB
apply(simp (no_asm) add: subst_swap_comm[THEN sym])
apply(simp (no_asm) add: subst_swap_comm[THEN sym])
--Unit
apply(force)
--Atom
apply(force)
--Paar
apply(force dest!: fresh_paar_elim)
--Func
apply(force dest!:  fresh_func_elim)
done

lemma subst_equ_to_trm: "nabla\<Turnstile>subst s1 \<approx> subst s2\<Longrightarrow> nabla\<turnstile>subst s1 t\<approx>subst s2 t"
apply(induct_tac t)
apply(auto simp add: subst_equ_def)
apply(case_tac "list2\<in>domn (subst s1) \<union> domn (subst s2)")
apply(simp only: subst_susp)
apply(simp only: equ_pi_to_left[THEN sym])
apply(simp only: equ_involutive_left)
apply(simp)
apply(erule conjE)
apply(drule not_in_domn)+
apply(subgoal_tac "subst s1 (Susp list1 list2)=swap list1 (subst s1 (Susp [] list2))")--A
apply(subgoal_tac "subst s2 (Susp list1 list2)=swap list1 (subst s2 (Susp [] list2))")--B
apply(simp)
apply(rule equ_refl)
apply(simp (no_asm_use) add: subst_swap_comm[THEN sym])+
done

lemma subst_cancel_right: "\<lbrakk>nabla\<Turnstile>(subst s1)\<approx>(subst s2)\<rbrakk>\<Longrightarrow>nabla\<Turnstile>(subst (s1\<bullet>s))\<approx>(subst (s2\<bullet>s))" 
apply(simp (no_asm) only: subst_equ_def)
apply(rule ballI)
apply(simp only: subst_comp_expand)
apply(rule subst_equ_to_trm)
apply(assumption)
done

lemma subst_trans: "\<lbrakk>nabla\<Turnstile>subst s1\<approx>subst s2; nabla\<Turnstile>subst s2\<approx>subst s3\<rbrakk>\<Longrightarrow>nabla\<Turnstile>subst s1\<approx>subst s3"
apply(simp add: subst_equ_def)
apply(auto)
apply(case_tac "X \<in>domn (subst s2)")
apply(drule_tac x="X" in bspec)
apply(force)
apply(drule_tac x="X" in bspec)
apply(force)
apply(rule_tac "t2.0"="subst s2 (Susp [] X)" in equ_trans)
apply(assumption)+
apply(case_tac "X \<in>domn (subst s3)")
apply(drule_tac x="X" in bspec)
apply(force)
apply(drule_tac x="X" in bspec)
apply(force)
apply(rule_tac "t2.0"="subst s2 (Susp [] X)" in equ_trans)
apply(assumption)+
apply(drule not_in_domn)+
apply(drule_tac x="X" in bspec)
apply(force)
apply(simp)
apply(case_tac "X \<in>domn (subst s1)")
apply(drule_tac x="X" in bspec)
apply(force)
apply(drule_tac x="X" in bspec)
apply(force)
apply(rule_tac "t2.0"="subst s2 (Susp [] X)" in equ_trans)
apply(assumption)+
apply(case_tac "X \<in>domn (subst s2)")
apply(drule_tac x="X" in bspec)
apply(force)
apply(drule_tac x="X" in bspec)
apply(force)
apply(rule_tac "t2.0"="subst s2 (Susp [] X)" in equ_trans)
apply(assumption)+
apply(drule not_in_domn)+
apply(simp)
apply(rotate_tac 1)
apply(drule_tac x="X" in bspec)
apply(force)
apply(simp)
done

(* if occurs holds, then one subterm is equal to (subst s (Susp pi X)) *)

lemma occurs_sub_trm_equ: 
  "occurs X t1 \<longrightarrow> (\<exists>t2\<in>sub_trms (subst s t1). (\<exists>pi.(nabla\<turnstile>subst s (Susp pi1 X)\<approx>(swap pi t2))))" 
apply(induct_tac t1)
apply(auto)
apply(simp only: subst_susp)
apply(rule_tac x="swap list1 (look_up X s)" in bexI)
apply(rule_tac x="pi1@(rev list1)" in exI)
apply(simp add: swap_append)
apply(simp add: equ_pi_to_left[THEN sym])
apply(simp only: equ_involutive_left)
apply(rule equ_refl)
apply(rule t_sub_trms_t)
done

end
