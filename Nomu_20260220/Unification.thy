theory Unification 

imports Termination

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


(*definition of normal form of a problem*)

definition 
  normal_form :: "problem_type \<Rightarrow> problem_type set" where 
  "normal_form P1 \<equiv> if P1 \<in> stuck then {P1} else {P2. \<exists>nabla s. P1\<Turnstile>(nabla,s)\<Rightarrow>P2 \<and> P2\<in>stuck}"

text\<open>The reflexive-transitive closures of sred and cred\<close>

inductive sred_rtc :: "problem_type \<Rightarrow> substs \<Rightarrow> problem_type \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto>\<^sup>* _" [80,80,80] 80)
  where
sred_refl[intro!]: "P1 \<turnstile> [] \<leadsto>\<^sup>* P1" |
sred_rtc_step[intro!]: "\<lbrakk>P1 \<turnstile> s1 \<leadsto> P2; P2 \<turnstile> s2 \<leadsto>\<^sup>* P3\<rbrakk> \<Longrightarrow> P1 \<turnstile> (s2 \<bullet> s1) \<leadsto>\<^sup>* P3"


inductive cred_rtc :: "problem_type \<Rightarrow> fresh_envs \<Rightarrow> problem_type \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow>\<^sup>* _ " [80,80,80] 80)
  where
cred_refl[intro!] : "P1 \<turnstile> {} \<rightarrow>\<^sup>* P1" |
cred_rtc_step[intro!] : "\<lbrakk>P1 \<turnstile> nabla1 \<rightarrow> P2; P2 \<turnstile> nabla2 \<rightarrow>\<^sup>* P3\<rbrakk> \<Longrightarrow> P1 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P3"

text\<open>Either the measure reduces or the problem stays the same under equation reductions.\<close>

lemma rank_r_sred_rtc:
  assumes "P1 \<turnstile> s \<leadsto>\<^sup>* P2"
  shows "(P2, P1) \<in> rank_r \<or> P1 = P2"
using assms
proof (induct rule: sred_rtc.induct)
  case (sred_refl P1)
  then show "(P1, P1) \<in> rank_r \<or> P1 = P1" by simp
next
  case (sred_rtc_step P1 s1 P' s2 P2)
  then have "(P', P1) \<in> rank_r"
    using rank_r_sred by blast
  moreover have "(P2, P') \<in> rank_r \<or> P' = P2"
    using sred_rtc_step by simp
  ultimately show "(P2, P1) \<in> rank_r \<or> P1 = P2"
    using sred_rtc_step rank_r_trans by blast
qed

text\<open>If the problem does not change under the reflexive-transitive closure of sred,
the substitution must be empty.\<close>

lemma sred_rtc_no_cycle:
  assumes "P \<turnstile> s \<leadsto>\<^sup>* P"
  shows "s = []"
proof(rule ccontr)
  assume "s \<noteq> []"
  hence "(P,P) \<in> rank_r"
  proof(cases rule: sred_rtc.cases[OF assms])
    case (1 P1)
    then show ?thesis
      using \<open>s \<noteq> []\<close> by auto
  next
    case (2 P1 s1 P2 s2 P3)
    hence "(P2,P1) \<in> rank_r" 
      using rank_r_sred by simp
    moreover have "P1 = P3" 
      using 2(1,3) by simp
    moreover have "(P3, P2) \<in> rank_r \<or> P2=P3"
      using 2(5) rank_r_sred_rtc by simp
    ultimately have "(P3,P3) \<in> rank_r" 
      using rank_r_trans by blast
    then show "(P, P) \<in> rank_r" 
      using 2(3) by simp
  qed
  thus "False" using wf_rank_r by simp
qed

text\<open>If P1 reduces to a diferent P2 under steps of sred, then it reduces via red_plus.\<close>

lemma sred_rtc_to_redplus:
  assumes "P1 \<noteq> P2"  "P1 \<turnstile> s \<leadsto>\<^sup>* P2"
  shows "P1 \<Turnstile> ({}, s) \<Rightarrow> P2"
  using assms
proof(induct rule: sred_rtc.induct[OF assms(2)])
  case (1 P1)
  then show ?case by simp
next
  case (2 P1 s1 P' s2 P2)
  then show "P1 \<Turnstile> ({}, s2 \<bullet> s1) \<Rightarrow> P2"
    proof(cases "P' = P2")
      case True
      with 2(1,2) have 
        i: "P1 \<turnstile> s1 \<leadsto> P2" "P2 \<turnstile> s2 \<leadsto>\<^sup>* P2" by simp+
      hence "s2 = []" 
        using sred_rtc_no_cycle by simp
      with i have "P1 \<turnstile> (s2\<bullet>s1) \<leadsto> P2" by simp
      then show "P1 \<Turnstile> ({}, s2 \<bullet> s1) \<Rightarrow> P2 " 
        using sred_single by simp
    next
      case False
      with 2(2,3) have "P' \<Turnstile> ({}, s2) \<Rightarrow> P2" 
        by simp
      with 2(1) show "P1 \<Turnstile> ({}, s2 \<bullet> s1) \<Rightarrow> P2" 
        using sred_step by simp
    qed
qed

text\<open>The following two lemmas guarantee that we don't apply any non-trivial step of equational
reductions after applying a freshness reduction.\<close>

lemma no_nontrivial_sred_after_cred_aux:
  assumes "P1 \<turnstile> nabla \<rightarrow> P2" and "P2 \<turnstile> s \<leadsto>\<^sup>* P3"
  shows "P2 = P3"
  using assms
proof(induct rule: sred_rtc.induct[OF assms(2)])
  case (1 P2)
  then show ?case by simp
next
  case (2 P2 s' P' s2 P3)
  hence "fst P2 = []"
    using c_red_eqs_empty by auto
  moreover have "fst P2 \<noteq> []" 
    using 2(1) sred_eqs_not_empty by simp
  ultimately have False by auto
  then show ?case by simp
qed

lemma no_nontrivial_sred_after_cred:
  assumes "P1 \<turnstile> nabla1 \<rightarrow> P2"
    and "P2 \<turnstile> s \<leadsto>\<^sup>* P'" and "P' \<turnstile> nabla2 \<rightarrow>\<^sup>* P3"
  shows "P1 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P3"
  using assms
proof-
  from assms(1,2) have "P2 = P'" 
    using no_nontrivial_sred_after_cred_aux by simp
  hence "P2 \<turnstile> nabla2 \<rightarrow>\<^sup>* P3" 
    using assms(3) by simp
  with assms(1) show "P1 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P3"
    using cred_rtc_step by simp
qed

text\<open>If there is a reduction from P1 to P2 via red_plus, we can split into equational reductions
first and freshness reductions after.\<close>

lemma red_plus_decompose:
  assumes "P1 \<Turnstile> (nabla, s) \<Rightarrow> P2"
  shows "\<exists> P3. P1 \<turnstile> s \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> nabla \<rightarrow>\<^sup>* P2"
  using assms
proof (induction P1\<equiv>"P1" nablas\<equiv>"(nabla, s)" P2\<equiv>"P2" arbitrary: nabla s P1 P2 rule: red_plus.induct)
  case (sred_single P1 s1 P2)
  hence "P1 \<turnstile> s1 \<leadsto>\<^sup>* P2"
    using sred_rtc_step[OF sred_single sred_refl] by simp
  moreover have "P2 \<turnstile> {} \<rightarrow>\<^sup>* P2"
   using cred_refl by simp
  ultimately show "\<exists>P3. P1 \<turnstile> s1 \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> {} \<rightarrow>\<^sup>* P2" by blast
next
  case (cred_single P1 nabla1 P2)
  hence "P1 \<turnstile> nabla1 \<rightarrow>\<^sup>* P2"
    using cred_rtc_step[OF cred_single cred_refl] by simp
  moreover have "P1 \<turnstile> [] \<leadsto>\<^sup>* P1"
    using sred_refl by simp
  ultimately show "\<exists>P3. P1 \<turnstile> [] \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> nabla1 \<rightarrow>\<^sup>* P2" by blast
next
  case (sred_step P1 s1 P' nabla2 s2 P2)
  have "P1 \<turnstile> s1 \<leadsto> P'" by fact
  moreover obtain P3 where
    IH: "P' \<turnstile> s2 \<leadsto>\<^sup>* P3" "P3 \<turnstile> nabla2 \<rightarrow>\<^sup>* P2"
    using sred_step(3) by auto
  ultimately have "P1 \<turnstile> s2 \<bullet> s1 \<leadsto>\<^sup>* P3" 
    using sred_rtc_step by simp
  with IH(2) show "\<exists>P3. P1 \<turnstile> s2 \<bullet> s1 \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> nabla2 \<rightarrow>\<^sup>* P2"
    by blast
next
  case (cred_step P1 nabla1 P' nabla2 P2)
  have i: "P1 \<turnstile> nabla1 \<rightarrow> P'" by fact
  moreover obtain P3 where
    IH: "P' \<turnstile> [] \<leadsto>\<^sup>* P3" "P3 \<turnstile> nabla2 \<rightarrow>\<^sup>* P2"
    using cred_step(3) by auto
  ultimately have "P1 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P2"
    using no_nontrivial_sred_after_cred by simp
  moreover have "P1 \<turnstile> [] \<leadsto>\<^sup>* P1"
    using sred_refl by simp
  ultimately show "\<exists>P3. P1 \<turnstile> [] \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> (nabla2 \<union> nabla1) \<rightarrow>\<^sup>* P2"
    by blast
qed

text\<open>A form of transitivity of red_plus.\<close>

lemma red_plus_transitivity:
  assumes "P1 \<Turnstile> (nabla1, s1) \<Rightarrow> P2"
      and "P2 \<Turnstile> (nabla2, s2) \<Rightarrow> P3"
    shows "\<exists> nabla3 s3. P1 \<Turnstile> (nabla3, s3) \<Rightarrow> P3"
  using assms
proof (induction rule: red_plus.induct[OF assms(1)])
  case (2 P1 nabla1 P2)
  then obtain P' where
  i: "P2 \<turnstile> s2 \<leadsto>\<^sup>* P'"
    using red_plus_decompose by blast
  with 2(1) have "P2 = P'" 
   using no_nontrivial_sred_after_cred_aux by simp
  hence "s2 = []" 
    using i(1) sred_rtc_no_cycle by simp
  hence "P2 \<Turnstile> (nabla2, []) \<Rightarrow> P3" 
    using 2(3) by simp
  with 2(1) show "\<exists>nabla3 s3. P1 \<Turnstile> (nabla3, s3) \<Rightarrow> P3"
    using cred_step by auto
next
  case (4 P1 nabla P' nabla' P2)
  then obtain nabla3 s3 where
    P_prime_to_P3: "P' \<Turnstile> (nabla3, s3) \<Rightarrow> P3" by auto
  then obtain P'' where "P' \<turnstile> s3 \<leadsto>\<^sup>* P''" "P'' \<turnstile> nabla3 \<rightarrow>\<^sup>* P3"
    using red_plus_decompose by blast
  with 4(1) have "P' = P''" 
    using  no_nontrivial_sred_after_cred_aux by simp
  moreover have "s3 =[]"
    using \<open>P' \<turnstile> s3 \<leadsto>\<^sup>* P''\<close> sred_rtc_no_cycle calculation by simp
  hence "P' \<Turnstile> (nabla3, []) \<Rightarrow> P3" 
    using P_prime_to_P3 by simp
  with 4(1) show "\<exists>nabla3 s3. P1 \<Turnstile> (nabla3, s3) \<Rightarrow> P3"
    using cred_step by auto
qed (auto)



text\<open>Every problem has a normal form.\<close>

lemma normal_form_exists:
  shows "P \<in> stuck \<or> (\<exists> P2 nabla s. P \<Turnstile>(nabla,s)\<Rightarrow>P2 \<and> P2\<in>stuck )"
proof(induction P rule: wf_induct_rule[OF wf_rank_r])
  case (1 P)
  then show "P \<in> stuck \<or> (\<exists>P2 nabla s. P \<Turnstile> (nabla, s) \<Rightarrow> P2  \<and> P2 \<in> stuck)"
  proof (cases "P \<in> stuck")
    case True
    then show "P \<in> stuck \<or> (\<exists>P2 nabla s. P \<Turnstile> (nabla, s) \<Rightarrow> P2  \<and> P2 \<in> stuck)" by simp
  next
    case False
    then obtain P' nabla s where P_to_P_prime:
      "P \<Turnstile>(nabla,s)\<Rightarrow>P'"
      unfolding stuck_def by auto
    hence "(P', P) \<in> rank_r"
      using rank_r_red_plus by simp
    hence aux: "P' \<in> stuck \<or> (\<exists>P2 nabla s. P' \<Turnstile> (nabla, s) \<Rightarrow> P2 \<and> P2 \<in> stuck)"
      using 1 by simp
    then show "P \<in> stuck \<or> (\<exists>P2 nabla s. P \<Turnstile> (nabla, s) \<Rightarrow> P2  \<and> P2 \<in> stuck)"
    proof(cases "P' \<in> stuck")
      case True
      then show ?thesis 
        using P_to_P_prime by blast
    next
      case False
      then obtain P2 nabla' s' where
      P_prime_to_P2: "P' \<Turnstile> (nabla', s') \<Rightarrow> P2" "P2 \<in> stuck"
        using aux by auto
      then obtain nabla1 s1 where "P \<Turnstile> (nabla1, s1) \<Rightarrow> P2" "P2\<in> stuck"
        using P_to_P_prime red_plus_transitivity by blast
      then show ?thesis by blast
    qed
  qed
qed

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

lemma not_reduce_then_fail:
  assumes "\<not> (\<exists>nabla s P'. ((t1 \<approx>? t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P')"
  shows "fail ((t1 \<approx>? t2) # xs, ys)"
  using assms
proof(cases t1)
  case (Abst a t1')
  have t1_def: "t1 = Abst a t1'" by fact
  then show "fail ((t1, t2) # xs, ys)"
  proof(cases t2)
    case (Abst b t2')
    with t1_def
    have "((t1 \<approx>? t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1'\<approx>?t2')#xs,ys) \<or> 
    ((t1\<approx>? t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1'\<approx>?swap [(a,b)] t2')#xs,(a\<sharp>?t2')#ys)"
      using abst_aa_sred abst_ab_sred by (cases "a=b") auto
    hence "\<exists> P2. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},[])\<Rightarrow>P2"
      using sred_single by blast
    thus "fail ((t1, t2) # xs, ys)"
      using assms by simp
  next
    case (Susp pi X)
    have t2_def: "t2 = Susp pi X" by fact
    with t1_def
    show "fail ((t1, t2) # xs, ys)" 
    proof(cases "occurs X t1'")
      case True
      with t1_def t2_def
      show "fail ((t1, t2) # xs, ys)" 
      using fail_sym[OF fail_occur_abst[OF True]] by simp
    next
      case False
      with t1_def 
      have not_occurs: "\<not> occurs X t1" by simp
      hence "((t1\<approx>? Susp pi X)#xs,ys) 
                    \<turnstile>[(X,swap (rev pi) t1)]\<leadsto> apply_subst [(X,swap (rev pi) t1)] (xs,ys)"
        using t1_def var_2_sred[OF not_occurs] by simp
       hence "\<exists> P2 s. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},s)\<Rightarrow>P2"
         using t1_def t2_def sred_single by blast
       thus "fail ((t1, t2) # xs, ys)" 
         using assms by simp
    qed
  qed (auto)
next
  case (Susp pi X)
  have t1_def: "t1 = Susp pi X" by fact
  then show "fail ((t1, t2) # xs, ys)"
  proof(cases "occurs X t2")
    case True
    then show "fail ((t1, t2) # xs, ys)"
    proof(cases t2)
      case (Abst a t2')
      have t2_def: "t2 = Abst a t2'" by fact
      with True
      have "occurs X t2'" unfolding occurs.simps(4) t2_def by argo
      thus "fail ((t1, t2) # xs, ys)"
        using t1_def t2_def fail_occur_abst by simp
    next
      case (Susp pi' Y)
      have t2_def: "t2 = Susp pi' Y" by fact
      have "X = Y" 
        using True unfolding t2_def occurs.simps(3)
        by argo
      hence "((Susp pi X\<approx>?Susp pi' Y)#xs,ys) 
                                \<turnstile>[]\<leadsto> (xs,(map (\<lambda>a. a\<sharp>? Susp [] X) (ds_list pi pi'))@ys)"
        using susp_sred by simp
      hence "\<exists> P2. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},[])\<Rightarrow>P2"
        using sred_single t1_def t2_def by blast
      thus"fail ((t1, t2) # xs, ys)"
        using assms by simp
    next
      case (Paar t21 t22)
      have t2_def: "t2 = Paar t21 t22" by fact
      with True
      have "occurs X t21 \<or> occurs X t22" unfolding occurs.simps(5) t2_def by argo
      thus "fail ((t1, t2) # xs, ys)"
        using t1_def t2_def fail_occur_paar by simp
    next
      case (Func f t2')
      have t2_def: "t2 = Func f t2'" by fact
      with True
      have "occurs X t2'" unfolding occurs.simps(6) t2_def by argo
      thus "fail ((t1, t2) # xs, ys)"
        using t1_def t2_def fail_occur_func by simp
    qed (auto simp add: True)
  next
    case False
    hence "((Susp pi X, t2) # xs, ys) \<turnstile> 
    [(X, swap (rev pi) t2)] \<leadsto> apply_subst [(X, swap (rev pi) t2)] (xs, ys)"
      using var_1_sred[OF False] by simp
    hence "\<exists> P2 s. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},s)\<Rightarrow>P2"
      using t1_def sred_single by blast
    thus "fail ((t1, t2) # xs, ys)" 
      using assms by simp
  qed
next
  case Unit
  have t1_def: "t1 = Unit" by fact
  then show "fail ((t1, t2) # xs, ys)"
  proof(cases t2)
    case (Susp pi X)
    have t2_def: "t2 =  Susp pi X" by fact
    with t1_def have not_occurs: "\<not> occurs X t1" by simp
    hence "((t1\<approx>? Susp pi X)#xs,ys) 
                    \<turnstile>[(X,swap (rev pi) t1)]\<leadsto> apply_subst [(X,swap (rev pi) t1)] (xs,ys)"
      using t1_def var_2_sred[OF not_occurs] by simp
    hence "\<exists> P2 s. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},s)\<Rightarrow>P2"
      using t1_def t2_def sred_single by blast
    thus "fail ((t1, t2) # xs, ys)" 
      using assms by simp
  next
    case Unit
    with t1_def
    have "((t1 \<approx>? t2)#xs,ys) \<turnstile>[]\<leadsto> (xs,ys)"
      using unit_sred by auto
    hence "\<exists> P2. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},[])\<Rightarrow>P2"
      using sred_single by blast
    thus "fail ((t1, t2) # xs, ys)"
      using assms by simp
  qed (auto)
next
  case (Atom a)
  have t1_def: "t1 = Atom a" by fact
  then show "fail ((t1, t2) # xs, ys)" 
  proof(cases t2)
    case (Susp pi X)
    have t2_def: "t2 =  Susp pi X" by fact
    with t1_def have not_occurs: "\<not> occurs X t1" by simp
    hence "((t1\<approx>? Susp pi X)#xs,ys) 
                    \<turnstile>[(X,swap (rev pi) t1)]\<leadsto> apply_subst [(X,swap (rev pi) t1)] (xs,ys)"
      using t1_def var_2_sred[OF not_occurs] by simp
    hence "\<exists> P2 s. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},s)\<Rightarrow>P2"
      using t1_def t2_def sred_single by blast
    thus "fail ((t1, t2) # xs, ys)" 
      using assms by simp
  next
    case (Atom b)
    have t2_def: "t2 = Atom b" by fact
    then show "fail ((t1, t2) # xs, ys)"
    proof(cases "a=b")
      case True
      hence "((t1 \<approx>? t2)#xs,ys) \<turnstile>[]\<leadsto> (xs,ys)"
        using t2_def t1_def atom_sred by simp
      hence "\<exists> P2. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},[])\<Rightarrow>P2"
        using sred_single by blast
      thus "fail ((t1, t2) # xs, ys)"
        using assms by simp
    qed (simp add: t1_def t2_def fail_diff_atoms)
  qed(auto)
next
  case (Paar t11 t12)
  have t1_def: "t1 = Paar t11 t12" by fact
  then show "fail ((t1, t2) # xs, ys)"
  proof(cases t2)
  next
    case (Susp pi X)
    have t2_def: "t2 = Susp pi X" by fact
    then show "fail ((t1, t2) # xs, ys)" 
    proof(cases "occurs X t11 \<or> occurs X t12")
      case True
      then show "fail ((t1, t2) # xs, ys)" 
        using t1_def t2_def fail_sym[OF fail_occur_paar[OF True]] by simp
    next
      case False
      hence "\<not> occurs X t1"
        using t1_def by simp
      hence "((t1\<approx>?Susp pi X)#xs,ys) 
                               \<turnstile>[(X,swap (rev pi) t1)]\<leadsto> apply_subst [(X,swap (rev pi) t1)] (xs,ys)"
        by auto
      hence "\<exists> P2 s. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},s)\<Rightarrow>P2"
        using t1_def t2_def sred_single by blast
      thus "fail ((t1, t2) # xs, ys)" 
        using assms by simp
    qed
  next
    case (Paar t21 t22)
    have t2_def: "t2 = Paar t21 t22" by fact
    with t1_def have
    "((t1 \<approx>? t2)#xs,ys) \<turnstile>[]\<leadsto> ((t11\<approx>?t21)#(t12\<approx>?t22)#xs,ys)"
      using paar_sred by simp
    hence "\<exists> P2. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},[])\<Rightarrow>P2"
      using sred_single by blast
    thus "fail ((t1, t2) # xs, ys)"
      using assms by simp
  qed(auto)
next
  case (Func f t1')
  have t1_def: "t1 = Func f t1'" by fact
  then show "fail ((t1, t2) # xs, ys)"
  proof(cases t2)
    case (Susp pi X)
     have t2_def: "t2 = Susp pi X" by fact
     with t1_def
    show "fail ((t1, t2) # xs, ys)" 
    proof(cases "occurs X t1'")
      case True
      with t1_def t2_def
      show "fail ((t1, t2) # xs, ys)" 
      using fail_sym[OF fail_occur_func[OF True]] by simp
    next
      case False
      with t1_def 
      have not_occurs: "\<not> occurs X t1" by simp
      hence "((t1\<approx>? Susp pi X)#xs,ys) 
                    \<turnstile>[(X,swap (rev pi) t1)]\<leadsto> apply_subst [(X,swap (rev pi) t1)] (xs,ys)"
        using t1_def var_2_sred[OF not_occurs] by simp
       hence "\<exists> P2 s. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},s)\<Rightarrow>P2"
         using t1_def t2_def sred_single by blast
       thus "fail ((t1, t2) # xs, ys)" 
         using assms by simp
    qed
  next
    case (Func g t2')
     have t2_def: "t2 = Func g t2'" by fact
     then show "fail ((t1, t2) # xs, ys)"
     proof(cases "f=g")
       case True
       hence "((t1 \<approx>? t2)#xs,ys) \<turnstile>[]\<leadsto> ((t1'\<approx>?t2')#xs,ys)"
         using t1_def t2_def func_sred by simp
       hence "\<exists> P2. ((t1 \<approx>? t2)#xs,ys) \<Turnstile>({},[])\<Rightarrow>P2"
         using sred_single by blast
       thus "fail ((t1, t2) # xs, ys)"
         using assms by simp
     next
       case False
       then show "fail ((t1, t2) # xs, ys)"
         using t1_def t2_def fail_diff_func[OF False] by simp
     qed
  qed(auto)
qed


lemma fresh_reduces_if_not_atom:
  assumes "t \<noteq> Atom a"
  shows "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla,s) \<Rightarrow> P2"
  using assms cred_single
proof(cases t)
  case (Abst b t')
  then show "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla, s) \<Rightarrow> P2"
  proof(cases "a=b")
    case True
    hence "([], (a \<sharp>? t) # xs) \<turnstile>{}\<rightarrow> ([],xs)"
      unfolding Abst using abst_aa_cred by simp
    then show "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla, s) \<Rightarrow> P2"
      using cred_single by blast
  next
    case False
    hence "([], (a \<sharp>? t) # xs) \<turnstile>{}\<rightarrow> ([], (a\<sharp>? t') # xs)"
      unfolding  Abst using abst_ab_cred by simp
    then show "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla, s) \<Rightarrow> P2"
      using cred_single by blast
  qed
next
  case (Atom b)
  with assms
  have "a \<noteq> b" by simp
  hence "([], (a \<sharp>? t) # xs) \<turnstile> {}\<rightarrow> ([],xs)"
    unfolding Atom using atom_cred by simp
  then show "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla, s) \<Rightarrow> P2"
    using cred_single by blast
qed (simp add: cred_single, blast+)


lemma empty_stuck:
  shows "([],[]) \<in> stuck"
proof-
  have "\<not> (\<exists>P2 nabla s. ([],[]) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  thus "([],[]) \<in> stuck"
    unfolding stuck_def by auto
qed

lemma fail_is_stuck:
  assumes "fail P"
  shows "P \<in> stuck"
  using assms
proof(induct rule: fail.induct)
  case (fail_occur_abst X t pi a xs ys)
  have t_occurs: "occurs X t" by fact
  moreover have "\<not> (\<exists>P2 nabla s. ((Susp pi X \<approx>? Abst a t) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
  proof
    assume "\<exists>P2 nabla s. ((Susp pi X \<approx>? Abst a t) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2"
    then obtain P2 nabla s where
    red: "((Susp pi X \<approx>? Abst a t) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2"
      by auto
    thus False 
    proof (cases rule: red_plus.cases)
      case sred_single
      have "((Susp pi X, Abst a t) # xs, ys) \<turnstile> s \<leadsto> P2" by fact
      hence "\<not> occurs X t" 
         by (auto elim: s_red.cases)
      with t_occurs show False by simp
    next
      case cred_single
      have "((Susp pi X, Abst a t) # xs, ys) \<turnstile> nabla \<rightarrow> P2" by fact
      moreover have "fst ((Susp pi X, Abst a t) # xs, ys) \<noteq> []"
        by simp
      ultimately show False 
        using c_red_eqs_empty by blast
    next
      case (sred_step s1 P3 s2)
      have "((Susp pi X, Abst a t) # xs, ys) \<turnstile> s1 \<leadsto> P3" by fact
      hence "\<not> occurs X t" 
        by (auto elim: s_red.cases)
      with t_occurs show False by simp
    next
      case (cred_step nabla1 P3 nabla2)
      have "((Susp pi X, Abst a t) # xs, ys) \<turnstile> nabla1 \<rightarrow> P3" by fact
       moreover have "fst ((Susp pi X, Abst a t) # xs, ys) \<noteq> []"
        by simp
      ultimately show False 
        using c_red_eqs_empty by blast
    qed
  qed
  then show "((Susp pi X, Abst a t) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_occur_func X t pi F xs ys)
  have t_occurs: "occurs X t" by fact
  moreover have "\<not> (\<exists>P2 nabla s. ((Susp pi X \<approx>? Func F t) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
  proof
    assume "\<exists>P2 nabla s. ((Susp pi X \<approx>? Func F t) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2"
    then obtain P2 nabla s where
    red: "((Susp pi X \<approx>? Func F t) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2"
      by auto
    thus False 
    proof (cases rule: red_plus.cases)
      case sred_single
      have "((Susp pi X, Func F t) # xs, ys) \<turnstile> s \<leadsto> P2" by fact
      hence "\<not> occurs X t" 
         by (auto elim: s_red.cases)
      with t_occurs show False by simp
    next
      case cred_single
      have "((Susp pi X, Func F t) # xs, ys) \<turnstile> nabla \<rightarrow> P2" by fact
      moreover have "fst ((Susp pi X, Func F t) # xs, ys) \<noteq> []"
        by simp
      ultimately show False 
        using c_red_eqs_empty by blast
    next
      case (sred_step s1 P3 s2)
      have "((Susp pi X, Func F t) # xs, ys) \<turnstile> s1 \<leadsto> P3" by fact
      hence "\<not> occurs X t" 
         by (auto elim: s_red.cases)
      with t_occurs show False by simp
    next
      case (cred_step nabla1 P3 nabla2)
      have "((Susp pi X, Func F t) # xs, ys) \<turnstile> nabla1 \<rightarrow> P3" by fact
       moreover have "fst ((Susp pi X, Func F t) # xs, ys) \<noteq> []"
        by simp
      ultimately show False 
        using c_red_eqs_empty by blast
    qed
  qed
  then show "((Susp pi X, Func F t) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_occur_paar X t1 t2 pi xs ys)
  have "occurs X t1 \<or> occurs X t2" by fact
  hence t_occurs: "occurs X (Paar t1 t2)"
    using occurs.simps(5) by auto
  moreover have "\<not> (\<exists>P2 nabla s. ((Susp pi X \<approx>? Paar t1 t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
  proof
    assume "\<exists>P2 nabla s. ((Susp pi X \<approx>? Paar t1 t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2"
    then obtain P2 nabla s where
    red: "((Susp pi X \<approx>? Paar t1 t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2"
      by auto
    thus False 
    proof (cases rule: red_plus.cases)
      case sred_single
      have "((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> s \<leadsto> P2" by fact
      hence "\<not> occurs X (Paar t1 t2)" 
        by (auto elim: s_red.cases)
      with t_occurs show False by simp
    next
      case cred_single
      have "((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> nabla \<rightarrow> P2" by fact
      moreover have "fst ((Susp pi X, Paar t1 t2) # xs, ys) \<noteq> []"
        by simp
      ultimately show False 
        using c_red_eqs_empty by blast
    next
      case (sred_step s1 P3 s2)
      have "((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> s1 \<leadsto> P3" by fact
      hence "\<not> occurs X (Paar t1 t2)" 
        by (auto elim: s_red.cases)
      with t_occurs show False by simp
    next
      case (cred_step nabla1 P3 nabla2)
      have "((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> nabla1 \<rightarrow> P3" by fact
       moreover have "fst ((Susp pi X, Paar t1 t2) # xs, ys) \<noteq> []"
        by simp
      ultimately show False 
        using c_red_eqs_empty by blast
    qed
  qed
  then show "((Susp pi X, Paar t1 t2) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_fresh_atom a ys)
  have "\<not> (\<exists>P2 nabla s. ([], (a, Atom a) # ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "([], (a, Atom a) # ys) \<in> stuck" 
    unfolding stuck_def by simp
next
  case (fail_diff_atoms a b xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Atom a, Atom b) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Atom a, Atom b) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_abst_unit a t xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Abst a t, Unit) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Abst a t, Unit) # xs, ys) \<in> stuck"
     unfolding stuck_def by simp
next
  case (fail_abst_atom a t b xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Abst a t, Atom b) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Abst a t, Atom b) # xs, ys) \<in> stuck"
     unfolding stuck_def by simp
next
  case (fail_abst_paar a t t1 t2 xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Abst a t, Paar t1 t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Abst a t, Paar t1 t2) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_func_abst F t1 a t xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Func F t1, Abst a t) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Func F t1, Abst a t) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_atom_unit b xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Atom b, Unit) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Atom b, Unit) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_paar_unit t1 t2 xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Paar t1 t2, Unit) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Paar t1 t2, Unit) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_func_unit F t1 xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Func F t1, Unit) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Func F t1, Unit) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_atom_paar a t1 t2 xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Atom a, Paar t1 t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Atom a, Paar t1 t2) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_func_atom F t1 a xs ys)
  hence "\<not> (\<exists>P2 nabla s. ((Func F t1, Atom a) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Func F t1, Atom a) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_func_paar F t t1 t2 xs ys)
   hence "\<not> (\<exists>P2 nabla s. ((Func F t, Paar t1 t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Func F t, Paar t1 t2) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_diff_func F1 F2 t1 t2 xs ys)
   hence "\<not> (\<exists>P2 nabla s. ((Func F1 t1, Func F2 t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P2)"
    by (auto elim: red_plus.cases s_red.cases c_red.cases)
  then show "((Func F1 t1, Func F2 t2) # xs, ys) \<in> stuck"
    unfolding stuck_def by simp
next
  case (fail_sym s t xs ys)
  hence not_reduce: "\<nexists> P2 nabla s1. ((s, t) # xs, ys) \<Turnstile> (nabla, s1) \<Rightarrow> P2"
    unfolding stuck_def by simp
  have"\<nexists> P2 nabla s1. ((t, s) # xs, ys) \<Turnstile> (nabla, s1) \<Rightarrow> P2"
  proof
    assume "\<exists>P2 nabla s1. ((t, s) # xs, ys) \<Turnstile> (nabla, s1) \<Rightarrow> P2"
    then obtain P2 nabla s1 where 
      reduces: "((t, s) # xs, ys) \<Turnstile> (nabla, s1) \<Rightarrow> P2"
      by auto
    hence "\<exists> P3 nabla1 s2. ((s, t) # xs, ys) \<Turnstile> (nabla1, s2) \<Rightarrow> P3"
      using red_plus_symm[of \<open>((t, s) # xs, ys)\<close> t s xs ys nabla s1 P2] by auto
    with not_reduce show False by simp
  qed
  then show "((t, s) # xs, ys) \<in> stuck" unfolding stuck_def by simp
qed


lemma stuck_equiv: 
  shows "stuck = {([],[])} \<union> {P1. fail P1}"      
proof (rule set_eqI, rule iffI)
  fix P
  {assume P_is_stuck: "P \<in> stuck"
  then obtain eqs freshs where 
    P_def: "P = (eqs, freshs)" by (cases P)
  show "P \<in> {([], [])} \<union> {P1. fail P1}"
  proof(cases eqs)
    case Nil
    then show "P \<in> {([], [])} \<union> {P1. fail P1}"
    proof(cases freshs)
      case Nil
      with \<open>eqs = []\<close>
      show "P \<in> {([], [])} \<union> {P1. fail P1}" using P_def by simp
    next
      case (Cons c freshs')
      then obtain a t where c_def: "c = a \<sharp>? t" by force
      have "t = Atom a" 
        using fresh_reduces_if_not_atom P_is_stuck 
        unfolding stuck_def P_def Nil Cons c_def by blast
      hence "fail P" 
        unfolding P_def Nil Cons c_def using fail_fresh_atom by simp
      thus "P \<in> {([], [])} \<union> {P1. fail P1}" by auto
    qed
  next
    case(Cons e eqs')
    then obtain s t where e_def: "e = s \<approx>? t" by force
    have "fail P" 
      using P_is_stuck unfolding P_def Cons e_def 
        stuck_def using not_reduce_then_fail by simp
    thus "P \<in> {([], [])} \<union> {P1. fail P1}" by auto
  qed }

  {assume "P \<in> {([], [])} \<union> {P1. fail P1}"
    then show "P \<in> stuck" 
      using empty_stuck fail_is_stuck by blast
      }
qed


(*if reduces to a non-solvable problem, then it is non-solvable *)

lemma u_empty_sred: 
  assumes "P1\<turnstile>s\<leadsto>P2" and "U P2 ={}"
  shows "U P1 = {}"
  using assms P1_from_P2_sred all_solutions_def P1_to_P2_sred by blast


lemma u_empty_cred:
  assumes "P1\<turnstile>nabla\<rightarrow>P2" and "U P2 ={}"
  shows "U P1={}"
  using assms P1_from_P2_cred all_solutions_def P1_to_P2_cred by blast


lemma u_empty_red_plus: 
  assumes "P1\<Turnstile>(nabla,s)\<Rightarrow>P2" and "U P2 ={}"
  shows "U P1={}"
  using assms P1_from_P2_red_plus all_solutions_def P1_to_P2_red_plus1 by fast


(* all problems that cannot be solved produce "failed" problems only *)

lemma empty_then_fail: 
assumes "U P1={}"
shows" (\<forall>P \<in> normal_form P1. fail P)"
proof
  fix P
  assume P_is_nf: "P \<in> normal_form P1"
  hence P_is_stuck: "P \<in> stuck"
    using normal_form_def by (cases "P1 \<in> stuck") auto
  hence P_is_empty_or_fails: "P = ([],[]) \<or> fail P"
    using stuck_equiv by auto
  have "P \<noteq> ([],[])"
  proof
    assume P_empty: "P = ([],[])"
    hence solution: "({},[]) \<in> U P"
      using all_solutions_def by simp
    hence P_neq: "P \<noteq> P1" 
    using assms by auto
    show False
    proof(cases "P1\<in> stuck")
      case True
      then have "normal_form P1 = {P1}"
        unfolding normal_form_def by simp
      with P_is_nf have "P = P1" by simp
      with P_neq show False by simp
    next
      case False
      with P_is_nf
      obtain nabla s where P1_goes_to_P: "P1 \<Turnstile> (nabla, s) \<Rightarrow> P" 
        unfolding normal_form_def by auto
      hence "({} \<union> nabla, [] \<bullet> s) \<in> U P1"
        using P1_from_P2_red_plus[OF P1_goes_to_P solution ext_subst_id] by simp
      with assms show False by simp
    qed
  qed
  thus "fail P"
    using P_is_empty_or_fails by simp
qed


(* if a problem can be solved then no "failed" problem is produced *)

lemma not_empty_then_not_fail: 
  assumes "U P1\<noteq>{}"
  shows "\<not>(\<exists>P\<in> normal_form P1. fail P)"
proof(simp, rule ballI)
  fix P
  assume P_is_nf: "P \<in> normal_form P1"
  show "\<not> fail P"
  proof
    assume P_fails: "fail P"
    show False
    proof(cases "P1\<in> stuck")
      case True
      have "normal_form P1 = {P1}"
        unfolding normal_form_def using True by simp
      hence "P = P1" using P_is_nf by simp
      with P_fails have "U P1 = {}"
        using fail_then_empty by simp
      thus False using assms by simp
      next
        case False
        with P_is_nf
        obtain nabla s where P1_goes_to_P: "P1 \<Turnstile> (nabla, s) \<Rightarrow> P"
          unfolding normal_form_def by auto
        moreover have "U P = {}" 
          using P_fails fail_then_empty by simp
        ultimately have "U P1 = {}" 
          using u_empty_red_plus by simp
        then show False 
          using assms by simp
      qed
  qed
qed

text\<open>The procedure is complete, i.e. if a non-empty problem has a solution, then red_plus finds
the most general solution.\<close>

theorem completeness:
  assumes "P1 \<noteq> ([],[])" "U P1 \<noteq> {}"
  shows "\<exists> nabla' s'. P1 \<Turnstile> (nabla', s') \<Rightarrow> ([],[]) \<and> mgu P1 (nabla', s')"
proof-
  have P1_not_stuck: "P1 \<notin> stuck" 
  proof
    assume "P1\<in> stuck"
    hence "P1 = ([],[])\<or> fail P1" 
      unfolding stuck_equiv by simp
    hence "P1 =([],[])"
      using assms(2) fail_then_empty by blast
    thus False using assms(1) by simp
  qed
  then obtain P2 nabla' s' where 
    normal_form: "P1 \<Turnstile> (nabla', s') \<Rightarrow> P2" "P2 \<in> stuck"
    using normal_form_exists by blast
  hence "P2 \<in> normal_form P1" 
    using P1_not_stuck unfolding normal_form_def by auto
  hence "P2=([],[])"
    using not_empty_then_not_fail[OF assms(2)] normal_form(2) stuck_equiv by auto
  with normal_form(1) have "P1 \<Turnstile> (nabla', s') \<Rightarrow> ([],[])" by simp
  moreover have "mgu P1 (nabla',s')" 
    using mgu calculation by simp
  ultimately show "\<exists>nabla' s'. P1 \<Turnstile> (nabla', s') \<Rightarrow> ([], [])  \<and> mgu P1 (nabla', s')"
    by auto
qed
  


end