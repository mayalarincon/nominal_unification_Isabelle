theory Unification 

imports Mgu

begin
(* problems to which no reduction applies *)

definition stuck :: "problem_type set" where
  stuck_def: "stuck \<equiv> { P1. \<not>(\<exists>P2 nabla s. P1 \<Turnstile>(nabla,s)\<Rightarrow>P2)}"
                                                        
(* all problems which are stuck and have no unifier *)


inductive fail :: "problem_type \<Rightarrow> bool" where
fail_occur_abst [intro!]: "\<lbrakk>occurs X t\<rbrakk>\<Longrightarrow> fail ((Susp pi X \<approx>? Abst a t) # xs, ys)" |
fail_occur_func [intro!]: "\<lbrakk>occurs X t\<rbrakk>\<Longrightarrow> fail (Susp pi X \<approx>?Func F t#xs,ys)" |
fail_occur_paar [intro!]: "\<lbrakk>occurs X t1\<or>occurs X t2\<rbrakk>\<Longrightarrow> fail (Susp pi X\<approx>?Paar t1 t2#xs,ys)" |
fail_fresh_atom [intro!]: "fail ([],a\<sharp>? Atom a#ys)"|
fail_diff_atoms [intro!]: "a\<noteq>b\<Longrightarrow> fail (Atom a\<approx>? Atom b#xs,ys)" |
fail_abst_unit [intro!]: " fail (Abst a t\<approx>?Unit#xs,ys)" |
fail_abst_atom [intro!]: "fail (Abst a t\<approx>?Atom b#xs,ys)" |
fail_abst_paar [intro!]: "fail (Abst a t\<approx>?Paar t1 t2#xs,ys)" | 
fail_func_abst [intro!]: "fail (Func F t1\<approx>?Abst a t#xs,ys)" |
fail_atom_unit [intro!]: "fail (Atom b\<approx>?Unit#xs,ys)" |
fail_paar_unit [intro!]: "fail (Paar t1 t2\<approx>?Unit#xs,ys)" |
fail_func_unit [intro!]: "fail (Func F t1\<approx>?Unit#xs,ys)" | 
fail_atom_paar [intro!]: "fail (Atom a\<approx>?Paar t1 t2#xs,ys)" |
fail_func_atom [intro!]: "fail (Func F t1\<approx>?Atom a#xs,ys)" | 
fail_func_paar [intro!]: "fail (Func F t\<approx>?Paar t1 t2#xs,ys)" |
fail_diff_func [intro!]: "\<lbrakk>F1\<noteq>F2\<rbrakk>\<Longrightarrow> fail (Func F1 t1\<approx>?Func F2 t2#xs,ys)" |
fail_sym [intro!]: "fail (s \<approx>? t # xs, ys) \<Longrightarrow> fail (t \<approx>? s # xs, ys)"


definition 
  results :: "problem_type \<Rightarrow> problem_type set" where 
  "results P1 \<equiv> if P1 \<in> stuck then {P1} else {P2. \<exists>nabla s. P1\<Turnstile>(nabla,s)\<Rightarrow>P2 \<and> P2\<in>stuck}"

(*the solutions of a problem are the same for symmetric equations -- MOVE to Mgu.thy*)

lemma U_equ_symm:
  shows "U (s\<approx>?t#xs, ys) = U (t\<approx>?s#xs, ys)"
  by(auto simp add: all_solutions_def equ_symm) 


(* a "failed" problem has no unifier *)


lemma fail_then_empty: 
  assumes "fail P1"
  shows "U P1 = {}"
  using assms
proof(induct rule: fail.induct)
  case (fail_occur_abst X t pi a xs ys)
  let ?P = "(Susp pi X \<approx>? Abst a t # xs, ys)"
  { assume "U ((Susp pi X, Abst a t) # xs, ys) \<noteq> {}"
    then obtain s nabla where eq1: "nabla \<turnstile> subst s (Susp pi X) \<approx> Abst a (subst s t)"
      by (auto simp add: all_solutions_def)
    moreover
    have "occurs X t" by fact
    then obtain t' pi' where  
      eq2: "nabla \<turnstile> subst s (Susp pi X) \<approx> swap pi' t'" "t'\<in>sub_trms (subst s t)"
      using occurs_sub_trm_equ by blast
    moreover  
    have eq3: "\<not> nabla \<turnstile> (Abst a (subst s t)) \<approx> swap pi' t'"
      using eq2 psub_trm_not_equ by auto
    then have "False" using eq1 eq2 eq3
      by (metis equ_symm equ_trans)
  }
  then show "U ?P = {}" by auto
next
  case (fail_occur_func X t pi F xs ys)
  let ?P = "(Susp pi X \<approx>? Func F t # xs, ys)"
  { assume "U ((Susp pi X, Func F t) # xs, ys) \<noteq> {}"
    then obtain s nabla where eq1: "nabla \<turnstile> subst s (Susp pi X) \<approx> Func F (subst s t)"
      by (auto simp add: all_solutions_def)
    moreover
    have "occurs X t" by fact
    then obtain t' pi' where  
      eq2: "nabla \<turnstile> subst s (Susp pi X) \<approx> swap pi' t'" "t'\<in>sub_trms (subst s t)"
      using occurs_sub_trm_equ by blast
    moreover  
    have eq3: "\<not> nabla \<turnstile> (Func F (subst s t)) \<approx> swap pi' t'"
      using eq2 psub_trm_not_equ by auto
    then have "False" using eq1 eq2 eq3
      by (metis equ_symm equ_trans)
  }
  then show "U ?P = {}" by auto
next
  case (fail_occur_paar X t1 t2 pi xs ys)
  let ?P = "(Susp pi X \<approx>? Paar t1 t2 # xs, ys)"
  have "occurs X t1 \<or> occurs X t2" by fact
  then show "U ?P = {}"
  proof
    {assume "occurs X t1"
      {assume "U ((Susp pi X, Paar t1 t2) # xs, ys) \<noteq> {}"
    then obtain s nabla where eq1: "nabla \<turnstile> subst s (Susp pi X) \<approx> Paar (subst s t1) (subst s t2)"
      by (auto simp add: all_solutions_def)
    moreover
    have "occurs X t1" by fact
     then obtain t' pi' where  
      eq2: "nabla \<turnstile> subst s (Susp pi X) \<approx> swap pi' t'" "t'\<in>sub_trms (subst s t1)"
      using occurs_sub_trm_equ by blast
    moreover  
    have eq3: "\<not> nabla \<turnstile> (Paar (subst s t1) (subst s t2)) \<approx> swap pi' t'"
      using eq2 psub_trm_not_equ by auto
    then have "False" using eq1 eq2 eq3
      by (metis equ_symm equ_trans)}
  then show "U ?P = {}" by auto}

    {assume "occurs X t2"
    {assume "U ((Susp pi X, Paar t1 t2) # xs, ys) \<noteq> {}"
      then obtain s nabla where eq1: "nabla \<turnstile> subst s (Susp pi X) \<approx> Paar (subst s t1) (subst s t2)"
        by (auto simp add: all_solutions_def)
      moreover
      have "occurs X t2" by fact
      then obtain t' pi' where  
        eq2: "nabla \<turnstile> subst s (Susp pi X) \<approx> swap pi' t'" "t'\<in>sub_trms (subst s t2)"
        using occurs_sub_trm_equ by blast
      moreover  
      have eq3: "\<not> nabla \<turnstile> (Paar (subst s t1) (subst s t2)) \<approx> swap pi' t'"
        using eq2 psub_trm_not_equ by auto
      then have "False" using eq1 eq2 eq3
        by (metis equ_symm equ_trans)
    }
    then show "U ?P = {}" by auto}
  qed
next
  case (fail_fresh_atom a ys)
  let ?P = "([], a \<sharp>? Atom a # ys)"
  have "\<nexists> nabla s. nabla \<turnstile> a \<sharp> subst s (Atom a)"
    using subst_atom Fresh_elims(3) by auto
  thus "U ?P = {}"
    using all_solutions_def by simp
next
  case (fail_diff_atoms a b xs ys)
  let ?P = "(Atom a \<approx>? Atom b # xs, ys)"
  from \<open>a \<noteq> b\<close> have "\<nexists> nabla s. nabla \<turnstile> subst s (Atom a) \<approx> subst s (Atom b)"
    using Equ_elims(1) by auto
  thus "U ?P = {}"
    using all_solutions_def by simp
next
  case (fail_abst_unit a t xs ys)
  let ?P = "(Abst a t \<approx>? Unit # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Abst a t) \<approx> subst s Unit"
    by (auto elim: equ.cases)
  thus "U ?P = {}" 
    using all_solutions_def by simp
next
  case (fail_abst_atom a t b xs ys)
  let ?P = "(Abst a t \<approx>? Atom b # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Abst a t) \<approx> subst s (Atom b)"
     by (auto elim: equ.cases)
  thus "U ?P = {}" 
    using all_solutions_def by simp
next
  case (fail_abst_paar a t t1 t2 xs ys)
  let ?P = "(Abst a t \<approx>? Paar t1 t2 # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Abst a t) \<approx> subst s (Paar t1 t2)"
     by (auto elim: equ.cases)
  thus "U ?P = {}"
    using all_solutions_def by simp
next
  case (fail_func_abst F t1 a t xs ys)
  let ?P = "(Func F t1 \<approx>? Abst a t # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Func F t1) \<approx> subst s (Abst a t)"
     by (auto elim: equ.cases)
  thus "U ?P = {}"
    using all_solutions_def by simp
next
  case (fail_atom_unit b xs ys)
  let ?P = "(Atom b \<approx>? Unit # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Atom b) \<approx> subst s (Unit)"
     by (auto elim: equ.cases)
  thus "U ?P = {}" 
    using all_solutions_def by simp
next
  case (fail_paar_unit t1 t2 xs ys)
  let ?P = "(Paar t1 t2 \<approx>? Unit # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Paar t1 t2) \<approx> subst s (Unit)"
     by (auto elim: equ.cases)
  thus "U ?P = {}" 
    using all_solutions_def by simp
next
  case (fail_func_unit F t1 xs ys)
  let ?P = "(Func F t1\<approx>? Unit # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Func F t1) \<approx> subst s (Unit)"
     by (auto elim: equ.cases)
  thus "U ?P = {}" 
    using all_solutions_def by simp
next
  case (fail_atom_paar b t1 t2 xs ys)
  let ?P = "(Atom b \<approx>? Paar t1 t2 # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Atom b) \<approx> subst s (Paar t1 t2)"
     by (auto elim: equ.cases)
  thus "U ?P = {}" 
    using all_solutions_def by simp
next
  case (fail_func_atom F t1 b xs ys)
  let ?P = "(Func F t1 \<approx>? Atom b # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Func F t1) \<approx> subst s (Atom b)"
     by (auto elim: equ.cases)
  thus "U ?P = {}" 
    using all_solutions_def by simp
next
  case (fail_func_paar F t t1 t2 xs ys)
  let ?P = "(Func F t \<approx>? Paar t1 t2 # xs, ys)"
  have "\<nexists> nabla s. nabla \<turnstile> subst s (Func F t) \<approx> subst s (Paar t1 t2)"
     by (auto elim: equ.cases)
  thus "U ?P = {}" 
    using all_solutions_def by simp
next
  case (fail_diff_func F1 F2 t1 t2 xs ys)
  let ?P = "(Func F1 t1 \<approx>? Func F2 t2 # xs, ys)"
  from \<open>F1 \<noteq> F2\<close> have "\<nexists> nabla s. nabla \<turnstile> subst s (Func F1 t1) \<approx> subst s (Func F2 t2)"
     by (auto elim: equ.cases)
  thus "U ?P = {}" 
    using all_solutions_def by simp
next
  case (fail_sym s t xs ys)
  let ?P = "(t \<approx>? s # xs, ys)"
  have "fail ((s, t) # xs, ys)"
    "U ((s, t) # xs, ys) = {}" by fact+
  thus "U ?P = {}"
   using all_solutions_def U_equ_symm by simp
qed


(* the only stuck problems are the "failed" problems and the empty problem *)

lemma stuck_equiv: 
  shows "stuck = {([],[])} \<union> {P1. fail P1}"
  sorry


lemma u_empty_sred: 
  assumes "P1\<turnstile>s\<leadsto>P2" and "U P2 ={}"
  shows "U P1 = {}"
  using assms
proof(induct rule: s_red.induct)
  case (unit_sred xs ys)
  then show ?case sorry
next
  case (paar_sred t1 t2 s1 s2 xs ys)
  then show ?case sorry
next
  case (func_sred F t1 t2 xs ys)
  then show ?case sorry
next
  case (abst_aa_sred a t1 t2 xs ys)
  then show ?case sorry
next
  case (abst_ab_sred a b t1 t2 xs ys)
  then show ?case sorry
next
  case (atom_sred a xs ys)
  then show ?case sorry
next
  case (susp_sred pi1 X pi2 xs ys)
  then show ?case sorry
next
  case (var_1_sred X t pi xs ys)
  then show ?case sorry
next
  case (var_2_sred X t pi xs ys)
  then show ?case sorry
qed


lemma u_empty_cred:
  assumes "P1\<turnstile>nabla\<rightarrow>P2" and "U P2 ={}"
  shows "U P1={}"
  using assms
proof(induct rule: c_red.induct)
  case (unit_cred a xs)
  then show ?case sorry
next
  case (paar_cred a t1 t2 xs)
  then show ?case sorry
next
  case (func_cred a F t xs)
  then show ?case sorry
next
  case (abst_aa_cred a t xs)
  then show ?case sorry
next
  case (abst_ab_cred a b t xs)
  then show ?case sorry
next
  case (atom_cred a b xs)
  then show ?case sorry
next
  case (susp_cred a pi X xs)
  then show ?case sorry
qed


lemma u_empty_red_plus: 
  assumes "P1\<Turnstile>(nabla,s)\<Rightarrow>P2" and "U P2 ={}"
  shows "U P1={}"
  using assms
proof(induct rule: red_plus.induct)
  case (sred_single P1 s1 P2)
  then show ?case sorry
next
  case (cred_single P1 nabla1 P2)
  then show ?case sorry
next
  case (sred_step P1 s1 P2 nabla2 s2 P3)
  then show ?case sorry
next
  case (cred_step P1 nabla1 P2 nabla2 P3)
  then show ?case sorry
qed


(* all problems that cannot be solved produce "failed" problems only *)

lemma empty_then_fail: 
assumes "U P1={}"
shows" (\<forall>P\<in>results P1. fail P)"
  using assms sorry
(*
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
apply(rule_tac "nabla3.0"="nabla" and "nabla1.0"="{}" and "s1.0"="[]" in P1_from_P2_red_plus)
apply(simp add: ext_subst_def)
apply(auto)
apply(simp add: all_solutions_def)
done*)

(* if a problem can be solved then no "failed" problem is produced *)

lemma not_empty_then_not_fail: 
  assumes "U P1\<noteq>{}"
  shows "\<not>(\<exists>P\<in>results P1. fail P)"
apply(simp)
apply(rule ballI)
apply(clarify)
apply(simp add: results_def)
apply(case_tac "P1\<in>stuck")
apply(simp_all)
apply(drule fail_then_empty)
   apply(clarify)
  using assms fail_then_empty u_empty_red_plus by (auto, meson)

end