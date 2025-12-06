

theory Unification = Main + Terms + Fresh + Equ + Substs + Mgu:

(* problems to which no reduction applies *)

consts stuck :: "problem_type set"
defs
  stuck_def: "stuck \<equiv> { P1. \<not>(\<exists>P2 nabla s. P1 \<Turnstile>(nabla,s)\<Rightarrow>P2)}"

(* all problems which are stuck and have no unifier *)

consts fail :: "problem_type set"
inductive fail
intros
[intro!]: "\<lbrakk>occurs X t\<rbrakk>\<Longrightarrow>(Susp pi X\<approx>?Abst a t#xs,ys)\<in>fail"
[intro!]: "\<lbrakk>occurs X t\<rbrakk>\<Longrightarrow>(Susp pi X\<approx>?Func F t#xs,ys)\<in>fail"
[intro!]: "\<lbrakk>occurs X t1\<or>occurs X t2\<rbrakk>\<Longrightarrow>(Susp pi X\<approx>?Paar t1 t2#xs,ys)\<in>fail"
[intro!]: "\<lbrakk>occurs X t\<rbrakk>\<Longrightarrow>(Abst a t\<approx>?Susp pi X#xs,ys)\<in>fail"
[intro!]: "\<lbrakk>occurs X t\<rbrakk>\<Longrightarrow>(Func F t\<approx>?Susp pi X#xs,ys)\<in>fail"
[intro!]: "\<lbrakk>occurs X t1\<or>occurs X t2\<rbrakk>\<Longrightarrow>(Paar t1 t2\<approx>?Susp pi X#xs,ys)\<in>fail"
[intro!,dest!]: "([],a\<sharp>? Atom a#ys)\<in>fail"
[intro!]: "a\<noteq>b\<Longrightarrow>(Atom a\<approx>? Atom b#xs,ys)\<in>fail"
[intro!,dest!]: "(Abst a t\<approx>?Unit#xs,ys)\<in>fail"
[intro!,dest!]: "(Unit\<approx>?Abst a t#xs,ys)\<in>fail"
[intro!,dest!]: "(Abst a t\<approx>?Atom b#xs,ys)\<in>fail"
[intro!,dest!]: "(Atom b\<approx>?Abst a t#xs,ys)\<in>fail"
[intro!,dest!]: "(Abst a t\<approx>?Paar t1 t2#xs,ys)\<in>fail"
[intro!,dest!]: "(Paar t1 t2\<approx>?Abst a t#xs,ys)\<in>fail"
[intro!,dest!]: "(Abst a t\<approx>?Func F t1#xs,ys)\<in>fail"
[intro!,dest!]: "(Func F t1\<approx>?Abst a t#xs,ys)\<in>fail"
[intro!,dest!]: "(Unit\<approx>?Atom b#xs,ys)\<in>fail"
[intro!,dest!]: "(Atom b\<approx>?Unit#xs,ys)\<in>fail"
[intro!,dest!]: "(Unit\<approx>?Paar t1 t2#xs,ys)\<in>fail"
[intro!,dest!]: "(Paar t1 t2\<approx>?Unit#xs,ys)\<in>fail"
[intro!,dest!]: "(Unit\<approx>?Func F t1#xs,ys)\<in>fail"
[intro!,dest!]: "(Func F t1\<approx>?Unit#xs,ys)\<in>fail"
[intro!,dest!]: "(Atom a\<approx>?Paar t1 t2#xs,ys)\<in>fail"
[intro!,dest!]: "(Paar t1 t2\<approx>?Atom a#xs,ys)\<in>fail"
[intro!,dest!]: "(Atom a\<approx>?Func F t1#xs,ys)\<in>fail"
[intro!,dest!]: "(Func F t1\<approx>?Atom a#xs,ys)\<in>fail"
[intro!,dest!]: "(Func F t\<approx>?Paar t1 t2#xs,ys)\<in>fail"
[intro!,dest!]: "(Paar t1 t2\<approx>?Func F t#xs,ys)\<in>fail"
[intro!]: "\<lbrakk>F1\<noteq>F2\<rbrakk>\<Longrightarrow>(Func F1 t1\<approx>?Func F2 t2#xs,ys)\<in>fail"

(* the results that are interesting are the stuck ones *)

consts 
  results :: "problem_type \<Rightarrow> problem_type set"
defs
  results_def: 
  "results P1 \<equiv> if P1\<in>stuck then {P1} else {P2. \<exists>nabla s. P1\<Turnstile>(nabla,s)\<Rightarrow>P2 \<and> P2\<in>stuck}"

(* a "failed" problem has no unifier *)

lemma fail_then_empty: 
  "(P1\<in>fail) \<Longrightarrow> (U P1={})"
apply(erule fail.cases)
apply(simp add: all_solutions_def)
apply(rule allI)+
apply(rule impI)
apply(drule_tac nabla1="aa" and s1="b" and "pi1.1"="pi" in occurs_sub_trm_equ[THEN mp])
apply(subgoal_tac "\<forall>t1\<in>psub_trms (Abst a (subst b t)).\<not>(\<exists>pi2. aa\<turnstile>Abst a (subst b t)\<approx>swap pi2 t1)")
apply(simp)
apply(drule equ_sym)
apply(clarify)
apply(drule_tac "t1.0"="Abst a (subst b t)" and 
                "t2.0"="subst b (Susp pi X)" and 
                "t3.0"="swap pia t2" in equ_trans)
apply(simp)
apply(best)
apply(rule psub_trm_not_equ)
apply(simp add: all_solutions_def)
apply(rule allI)+
apply(rule impI)
apply(drule_tac nabla1="a" and s1="b" and "pi1.1"="pi" in occurs_sub_trm_equ[THEN mp])
apply(subgoal_tac "\<forall>t1\<in>psub_trms (Func F (subst b t)).\<not>(\<exists>pi2. a\<turnstile>Func F (subst b t)\<approx>swap pi2 t1)")
apply(simp)
apply(drule equ_sym)
apply(clarify)
apply(drule_tac "t1.0"="Func F (subst b t)" and 
                "t2.0"="subst b (Susp pi X)" and 
                "t3.0"="swap pia t2" in equ_trans)
apply(simp)
apply(best)
apply(rule psub_trm_not_equ)
apply(simp add: all_solutions_def)
apply(rule allI)+
apply(rule impI)
apply(erule disjE)
apply(drule_tac nabla1="a" and s1="b" and "pi1.1"="pi" in occurs_sub_trm_equ[THEN mp])
apply(subgoal_tac "\<forall>t3\<in>psub_trms (Paar (subst b t1) (subst b t2)).
                                \<not>(\<exists>pi2. a\<turnstile>Paar (subst b t1) (subst b t2)\<approx>swap pi2 t3)")
apply(simp)
apply(drule equ_sym)
apply(clarify)
apply(drule_tac "t1.0"="Paar (subst b t1) (subst b t2)" and 
                "t2.0"="subst b (Susp pi X)" and 
                "t3.0"="swap pia t2a" in equ_trans)
apply(simp)
apply(best)
apply(rule psub_trm_not_equ)
apply(drule_tac nabla1="a" and s1="b" and "pi1.1"="pi" in occurs_sub_trm_equ[THEN mp])
apply(subgoal_tac "\<forall>t3\<in>psub_trms (Paar (subst b t1) (subst b t2)).
                                \<not>(\<exists>pi2. a\<turnstile>Paar (subst b t1) (subst b t2)\<approx>swap pi2 t3)")
apply(simp)
apply(drule equ_sym)
apply(clarify)
apply(drule_tac "t1.0"="Paar (subst b t1) (subst b t2)" and 
                "t2.0"="subst b (Susp pi X)" and 
                "t3.0"="swap pia t2a" in equ_trans)
apply(simp)
apply(best)
apply(rule psub_trm_not_equ)
apply(simp add: all_solutions_def)
apply(rule allI)+
apply(rule impI)
apply(drule_tac nabla1="aa" and s1="b" and "pi1.1"="pi" in occurs_sub_trm_equ[THEN mp])
apply(subgoal_tac "\<forall>t3\<in>psub_trms (Abst a (subst b t)).
                                \<not>(\<exists>pi2. aa\<turnstile>Abst a (subst b t)\<approx>swap pi2 t3)")
apply(simp)
apply(clarify)
apply(drule_tac "t1.0"="Abst a (subst b t)" and 
                "t2.0"="subst b (Susp pi X)" and 
                "t3.0"="swap pia t2" in equ_trans)
apply(simp)
apply(best)
apply(rule psub_trm_not_equ)
apply(simp add: all_solutions_def)
apply(rule allI)+
apply(rule impI)
apply(drule_tac nabla1="a" and s1="b" and "pi1.1"="pi" in occurs_sub_trm_equ[THEN mp])
apply(subgoal_tac "\<forall>t1\<in>psub_trms (Func F (subst b t)).\<not>(\<exists>pi2. a\<turnstile>Func F (subst b t)\<approx>swap pi2 t1)")
apply(simp)
apply(clarify)
apply(drule_tac "t1.0"="Func F (subst b t)" and 
                "t2.0"="subst b (Susp pi X)" and 
                "t3.0"="swap pia t2" in equ_trans)
apply(simp)
apply(best)
apply(rule psub_trm_not_equ)
apply(simp add: all_solutions_def)
apply(rule allI)+
apply(rule impI)
apply(erule disjE)
apply(drule_tac nabla1="a" and s1="b" and "pi1.1"="pi" in occurs_sub_trm_equ[THEN mp])
apply(subgoal_tac "\<forall>t3\<in>psub_trms (Paar (subst b t1) (subst b t2)).
                                \<not>(\<exists>pi2. a\<turnstile>Paar (subst b t1) (subst b t2)\<approx>swap pi2 t3)")
apply(simp)
apply(clarify)
apply(drule_tac "t1.0"="Paar (subst b t1) (subst b t2)" and 
                "t2.0"="subst b (Susp pi X)" and 
                "t3.0"="swap pia t2a" in equ_trans)
apply(simp)
apply(best)
apply(rule psub_trm_not_equ)
apply(drule_tac nabla1="a" and s1="b" and "pi1.1"="pi" in occurs_sub_trm_equ[THEN mp])
apply(subgoal_tac "\<forall>t3\<in>psub_trms (Paar (subst b t1) (subst b t2)).
                                \<not>(\<exists>pi2. a\<turnstile>Paar (subst b t1) (subst b t2)\<approx>swap pi2 t3)")
apply(simp)
apply(clarify)
apply(drule_tac "t1.0"="Paar (subst b t1) (subst b t2)" and 
                "t2.0"="subst b (Susp pi X)" and 
                "t3.0"="swap pia t2a" in equ_trans)
apply(simp)
apply(best)
apply(rule psub_trm_not_equ)
apply(simp add: all_solutions_def, fast dest!: fresh.cases)
apply(simp add: all_solutions_def, fast dest!: equ.cases)+
done

(* the only stuck problems are the "failed" problems and the empty problem *)

lemma stuck_equiv: "stuck = {([],[])}\<union>fail"
apply(subgoal_tac "([],[])\<in>stuck")
apply(subgoal_tac "\<forall>P\<in>fail. P\<in>stuck")
apply(subgoal_tac "\<forall>P\<in>stuck. P=([],[]) \<or> P\<in>fail")
apply(force)
apply(rule ballI)
apply(thin_tac "([], []) \<in> stuck")
apply(thin_tac "\<forall>P\<in>fail. P \<in> stuck")
apply(simp add: stuck_def)
apply(clarify)
apply(case_tac a)
apply(simp)
apply(case_tac b)
apply(simp)
apply(simp)
apply(case_tac aa)
apply(simp)
apply(case_tac ba)
apply(simp_all)
apply(case_tac "ab=lista")
apply(force)
apply(force)
apply(force)
apply(force)
apply(force)
apply(force)
apply(force)
apply(case_tac aa)
apply(simp)
apply(case_tac ab)
apply(simp_all)
apply(case_tac ba)
apply(simp_all)
apply(case_tac "lista=listb")
apply(force)
apply(force)
apply(case_tac "occurs list2 (Abst lista trm)")
apply(force)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) (Abst lista trm))] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) (Abst lista trm))] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) (Abst lista trm))]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(force)
apply(force)
apply(force)
apply(force)
apply(case_tac ba)
apply(simp_all)
apply(case_tac "occurs list2 (Abst lista trm)")
apply(force)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) (Abst lista trm))] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) (Abst lista trm))] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) (Abst lista trm))]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(case_tac "list2=list2a")
apply(force)
apply(case_tac "occurs list2 (Susp list1a list2a)")
apply(simp)
apply(drule_tac 
    x="fst (apply_subst [(list2,swap (rev list1) (Susp list1a list2a))] (list,b))" in spec)
apply(drule_tac 
    x="snd (apply_subst [(list2,swap (rev list1) (Susp list1a list2a))] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) (Susp list1a list2a))]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(case_tac "occurs list2 Unit")
apply(simp)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) Unit)] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) Unit)] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) Unit)]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(case_tac "occurs list2 (Atom lista)")
apply(simp)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) (Atom lista))] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) (Atom lista))] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) (Atom lista))]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(case_tac "occurs list2 (Paar trm1 trm2)")
apply(force)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) (Paar trm1 trm2))] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) (Paar trm1 trm2))] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) (Paar trm1 trm2))]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(case_tac "occurs list2 (Func lista trm)")
apply(force)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) (Func lista trm))] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) (Func lista trm))] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) (Func lista trm))]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(case_tac ba)
apply(simp_all)
apply(force)
apply(case_tac "occurs list2 Unit")
apply(simp)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) Unit)] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) Unit)] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) Unit)]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(force)
apply(force)
apply(force)
apply(force)
apply(case_tac ba)
apply(simp_all)
apply(force)
apply(case_tac "occurs list2 (Atom lista)")
apply(simp)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) (Atom lista))] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) (Atom lista))] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) (Atom lista))]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(force)
apply(force)
apply(force)
apply(force)
apply(case_tac ba)
apply(simp_all)
apply(force)
apply(case_tac "occurs list2 (Paar trm1 trm2)")
apply(force)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) (Paar trm1 trm2))] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) (Paar trm1 trm2))] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) (Paar trm1 trm2))]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(force)
apply(force)
apply(force)
apply(force)
apply(case_tac ba)
apply(simp_all)
apply(force)
apply(case_tac "occurs list2 (Func lista trm)")
apply(force)
apply(drule_tac x="fst (apply_subst [(list2,swap (rev list1) (Func lista trm))] (list,b))" in spec)
apply(drule_tac x="snd (apply_subst [(list2,swap (rev list1) (Func lista trm))] (list,b))" in spec)
apply(drule_tac x="{}" in spec)
apply(drule_tac x="[(list2, swap (rev list1) (Func lista trm))]" in spec)
apply(simp only: surjective_pairing[THEN sym])
apply(force)
apply(force)
apply(force)
apply(force)
apply(force)
apply(rule ballI)
apply(thin_tac "([], []) \<in> stuck")
apply(simp add: stuck_def)
apply(clarify)
apply(ind_cases "((a, b), (nabla, s), aa, ba) \<in> red_plus")
apply(ind_cases "((a, b), s, aa, ba) \<in> s_red")
apply(simp_all)
apply(ind_cases "((Unit, Unit) # aa, b) \<in> fail")
apply(ind_cases "((Paar t1 t2, Paar s1 s2) # xs, b) \<in> fail")
apply(ind_cases "((Func F t1, Func F t2) # xs, b) \<in> fail")
apply(simp)
apply(ind_cases "((Abst ab t1, Abst ab t2) # xs, b) \<in> fail")
apply(ind_cases "((Abst ab t1, Abst bb t2) # xs, b) \<in> fail")
apply(ind_cases "((Atom ab, Atom ab) # aa, b) \<in> fail")
apply(simp)
apply(ind_cases "((Susp pi1 X, Susp pi2 X) # aa, b) \<in> fail")
apply(ind_cases "((Susp pi X, t) # xs, b) \<in> fail")
apply(simp add: apply_subst_def)+
apply(case_tac "occurs X t1")
apply(simp)
apply(simp)
apply(ind_cases "((t, Susp pi X) # xs, b) \<in> fail")
apply(simp add: apply_subst_def)
apply(case_tac "occurs X t1")
apply(simp)
apply(simp)
apply(case_tac "occurs X t1")
apply(simp)
apply(simp)
apply(ind_cases "((a, b), nabla, aa, ba) \<in> c_red")
apply(simp_all)
apply(ind_cases "([], (ab, Unit) # ba) \<in> fail")
apply(ind_cases "([], (ab, Paar t1 t2) # xs) \<in> fail")
apply(ind_cases "([], (ab, Func F t) # xs) \<in> fail")
apply(ind_cases "([], (ab, Abst ab t) # ba) \<in> fail")
apply(ind_cases "([], (ab, Abst bb t) # xs) \<in> fail")
apply(ind_cases "([], (ab, Atom bb) # ba) \<in> fail")
apply(simp)
apply(ind_cases "([], (ab, Susp pi X) # ba) \<in> fail")
apply(ind_cases "(a, b) \<turnstile> s1 \<leadsto> P2")
apply(simp_all)
apply(ind_cases "((Unit, Unit) # xs, b) \<in> fail")
apply(ind_cases "((Paar t1 t2, Paar s1 s2) # xs, b) \<in> fail")
apply(ind_cases "((Func F t1, Func F t2) # xs, b) \<in> fail")
apply(simp)
apply(ind_cases "((Abst ab t1, Abst ab t2) # xs, b) \<in> fail")
apply(ind_cases "((Abst ab t1, Abst bb t2) # xs, b) \<in> fail")
apply(ind_cases "((Atom ab, Atom ab) # aa, b) \<in> fail")
apply(simp)
apply(ind_cases "((Susp pi1 X, Susp pi2 X) # aa, b) \<in> fail")
apply(ind_cases "((Susp pi X, t) # xs, b) \<in> fail")
apply(simp add: apply_subst_def)+
apply(case_tac "occurs X t1")
apply(simp)
apply(simp)
apply(ind_cases "((t, Susp pi X) # xs, b) \<in> fail")
apply(simp add: apply_subst_def)
apply(case_tac "occurs X t1")
apply(simp)
apply(simp)
apply(case_tac "occurs X t1")
apply(simp)
apply(simp)
apply(ind_cases "(a, b) \<turnstile> nabla1 \<rightarrow> P2")
apply(simp_all)
apply(ind_cases "([], (ab, Unit) # ba) \<in> fail")
apply(ind_cases "([], (ab, Paar t1 t2) # xs) \<in> fail")
apply(ind_cases "([], (ab, Func F t) # xs) \<in> fail")
apply(ind_cases "([], (ab, Abst ab t) # ba) \<in> fail")
apply(ind_cases "([], (ab, Abst bb t) # xs) \<in> fail")
apply(ind_cases "([], (ab, Atom bb) # ba) \<in> fail")
apply(simp)
apply(ind_cases "([], (ab, Susp pi X) # ba) \<in> fail")
apply(simp add: stuck_def)
apply(rule allI)+
apply(clarify)
apply(ind_cases "(([], []), (nabla, s), a, b) \<in> red_plus")
apply(ind_cases "(([], []), s, a, b) \<in> s_red")
apply(ind_cases "(([], []), nabla, a, b) \<in> c_red")
apply(ind_cases "([], []) \<turnstile> s1 \<leadsto> P2")
apply(ind_cases "([], []) \<turnstile> nabla1 \<rightarrow> P2")
done

lemma u_empty_sred: 
  "P1\<turnstile>s\<leadsto>P2 \<longrightarrow> U P2 ={} \<longrightarrow> U P1={}"
apply(rule impI)
apply(ind_cases "P1 \<turnstile> s \<leadsto> P2")
apply(rule impI, simp add: all_solutions_def)
apply(rule impI, simp add: all_solutions_def)
apply(fast dest!: equ_paar_elim)
apply(rule impI, simp add: all_solutions_def)
apply(fast dest!: equ_func_elim)
apply(rule impI, simp add: all_solutions_def)
apply(fast dest!: equ_abst_aa_elim)
apply(rule impI, simp add: all_solutions_def)
apply(force dest!: equ_abst_ab_elim simp add: subst_swap_comm[THEN sym])
apply(rule impI, simp add: all_solutions_def)
apply(rule impI, simp add: all_solutions_def)
apply(simp add: ds_list_equ_ds)
apply(rule allI)+
apply(rule impI)
apply(drule_tac x="a" in spec)
apply(drule_tac x="b" in spec)
apply(erule disjE)
apply(force)
apply(simp add: subst_susp)
apply(drule equ_pi1_pi2_dec[THEN mp])
apply(force simp add: subst_susp)
apply(auto)
apply(simp add: all_solutions_def)
apply(simp_all add: apply_subst_def)
apply(auto)
apply(drule_tac x="a" in spec)
apply(drule_tac x="b" in spec)
apply(drule unif_1)
apply(auto)
apply(drule_tac x="(aa,ba)" in bspec)
apply(assumption)
apply(simp)
apply(drule_tac "t1.0"="aa" and "t2.0"="ba" in unif_2a)
apply(simp add: subst_comp_expand)
apply(drule_tac x="(aa,ba)" in bspec)
apply(assumption)
apply(simp)
apply(drule_tac a="aa" and "t"="ba" in unif_2b)
apply(simp add: subst_comp_expand)
apply(simp add: all_solutions_def)
apply(auto)
apply(drule_tac x="a" in spec)
apply(drule_tac x="b" in spec)
apply(drule equ_sym)
apply(drule unif_1)
apply(auto)
apply(drule_tac x="(aa,ba)" in bspec)
apply(assumption)
apply(simp)
apply(drule_tac "t1.0"="aa" and "t2.0"="ba" in unif_2a)
apply(simp add: subst_comp_expand)
apply(drule_tac x="(aa,ba)" in bspec)
apply(assumption)
apply(simp)
apply(drule_tac a="aa" and "t"="ba" in unif_2b)
apply(simp add: subst_comp_expand)
done

lemma u_empty_cred: 
  "P1\<turnstile>nabla\<rightarrow>P2 \<longrightarrow> U P2 ={} \<longrightarrow> U P1={}"
apply(rule impI)
apply(ind_cases "P1 \<turnstile>nabla\<rightarrow>P2")
apply(rule impI, simp add: all_solutions_def)
apply(rule impI, simp add: all_solutions_def)
apply(fast dest!: fresh_paar_elim)
apply(rule impI, simp add: all_solutions_def)
apply(fast dest!: fresh_func_elim)
apply(rule impI, simp add: all_solutions_def)
apply(rule impI, simp add: all_solutions_def)
apply(force dest!: fresh_abst_ab_elim)
apply(rule impI, simp add: all_solutions_def)
apply(rule impI, simp add: all_solutions_def)
done

lemma u_empty_red_plus: 
  "P1\<Turnstile>(nabla,s)\<Rightarrow>P2 \<longrightarrow> U P2 ={} \<longrightarrow> U P1={}"
apply(rule impI)
apply(erule red_plus.induct)
apply(drule u_empty_sred[THEN mp], assumption)
apply(drule u_empty_cred[THEN mp], assumption)
apply(drule u_empty_sred[THEN mp], force)
apply(drule u_empty_cred[THEN mp], force)
done

(* all problems that cannot be solved produce "failed" problems only *)

lemma empty_then_fail: "U P1={} \<longrightarrow> (\<forall>P\<in>results P1. P\<in>fail)"
apply(simp add: results_def)
apply(rule conjI)
apply(rule impI)
apply(rule impI)
apply(simp add: stuck_equiv)
apply(erule disjE)
apply(subgoal_tac "({},[])\<in>U ([],[])")
apply(simp)
apply(simp add: all_solutions_def)
apply(assumption)
apply(rule impI)+
apply(rule allI)+
apply(rule impI)
apply(erule conjE)
apply(simp add: stuck_equiv)
apply(auto)
apply(subgoal_tac "({},[])\<in>U ([],[])")
apply(drule_tac "nabla3.0"="nabla" and "nabla1.0"="{}" and "s1.0"="[]" in P1_from_P2_red_plus)
apply(simp add: ext_subst_def)
apply(auto)
apply(simp add: all_solutions_def)
done

(* if a problem can be solved then no "failed" problem is produced *)

lemma not_empty_then_not_fail: "U P1\<noteq>{} \<longrightarrow> \<not>(\<exists>P\<in>results P1. P\<in>fail)"
apply(rule impI)
apply(simp)
apply(rule ballI)
apply(clarify)
apply(simp add: results_def)
apply(case_tac "P1\<in>stuck")
apply(simp_all)
apply(drule fail_then_empty)
apply(simp)
apply(drule fail_then_empty)
apply(erule conjE)
apply(clarify)
apply(drule u_empty_red_plus[THEN mp])
apply(simp)
done

end









































































