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

lemma red_plus_first_step:
  assumes "P \<Turnstile> (nabla,s) \<Rightarrow> P'"
  shows
    "(\<exists>s1 P2. P \<turnstile> s1 \<leadsto> P2) \<or>
     (\<exists>nabla1 P2. P \<turnstile> nabla1 \<rightarrow> P2)"
  using assms by (cases rule: red_plus.cases) blast+

lemma c_red_empty_eqs:
  assumes "P \<turnstile> nabla \<rightarrow> P'"
  shows "fst P = []"
  using assms by (cases rule: c_red.cases) auto

lemma c_red_not_nonempty_eqs:
  shows "\<not> ((t1 \<approx>? t2) # xs, ys) \<turnstile> nabla \<rightarrow> P'"
proof
  assume assm: "((t1 \<approx>? t2) # xs, ys) \<turnstile> nabla \<rightarrow> P'"
  then show False
    using c_red_empty_eqs[OF assm]
      fst_conv[of \<open>(t1 \<approx>? t2) # xs\<close> ys] list.distinct[of \<open>(t1 \<approx>? t2)\<close> xs]
    by simp
qed

lemma sred_exists_if_same_shape:
  assumes "(t1 = Paar t11 t12 \<and> t2 = Paar t21 t22) \<or>
     ( t1 = Func F t1' \<and> t2 = Func F t2') \<or>
     ( t1 = Abst a t1' \<and> t2 = Abst a t2') \<or>
     ( t1 = Abst a t1' \<and> t2 = Abst b t2' \<and> (a\<noteq>b)) \<or>
     ( t1 = Atom a \<and> t2 = Atom a) \<or>
     ( t1 = Susp pi1 X \<and> t2 = Susp pi2 X) \<or>
     (t1 = Susp pi X \<and> t2 = t \<and> (\<not> occurs X t)) \<or>
     ( t1 = t \<and> t2 = Susp pi X \<and> (\<not> occurs X t)) \<or> (t1 = Unit \<and> t2 = Unit)"
  shows "\<exists> s P'. ((t1 \<approx>? t2) # xs, ys) \<turnstile> s \<leadsto> P'"
  using assms
  apply auto
proof-
  {assume "t1 = Abst a t1'" "t2 = Abst b t2'" "(a\<noteq>b)"
  then have "((Abst a t1' \<approx>? Abst a t2')#xs,ys) \<turnstile>[]\<leadsto> ((t1'\<approx>?t2')#xs,ys)"
    using abst_ab_sred by auto
  thus "\<exists>s aa ba. ((Abst a t1', Abst b t2') # xs, ys) \<turnstile> s  \<leadsto> (aa, ba)"
    by blast}

  {assume "t1 = Susp pi X" "\<not> occurs X t" "t2 = t"
  then have "((Susp pi X\<approx>?t)#xs,ys) 
                               \<turnstile>[(X,swap (rev pi) t)]\<leadsto> apply_subst [(X,swap (rev pi) t)] (xs,ys)"
    using var_1_sred by simp
  thus "\<exists>s a b. ((Susp pi X, t) # xs, ys) \<turnstile> s \<leadsto> (a, b)" 
    using prod.collapse by metis}

  {assume "t2 = Susp pi X" "\<not> occurs X t" "t1 = t"
  then have "((t\<approx>?Susp pi X)#xs,ys) 
                               \<turnstile>[(X,swap (rev pi) t)]\<leadsto> apply_subst [(X,swap (rev pi) t)] (xs,ys)"
    using var_2_sred by simp
  thus "\<exists>s a b. ((t, Susp pi X) # xs, ys) \<turnstile> s \<leadsto> (a, b)" 
    using prod.collapse by metis}
qed

lemma red_plus_exists_if_same_shape:
  assumes
    "(t1 = Paar t11 t12 \<and> t2 = Paar t21 t22) \<or>
     (t1 = Func F t1' \<and> t2 = Func F t2') \<or>
     (t1 = Abst a t1' \<and> t2 = Abst a t2') \<or>
     (t1 = Abst a t1' \<and> t2 = Abst b t2' \<and> (a\<noteq>b)) \<or>
     (t1 = Atom a \<and> t2 = Atom a) \<or>
     (t1 = Susp pi1 X \<and> t2 = Susp pi2 X) \<or>
     (t1 = Susp pi X \<and> t2 = t \<and> (\<not> occurs X t)) \<or>
     (t1 = t \<and> t2 = Susp pi X \<and> (\<not> occurs X t)) \<or>
     (t1 = Unit \<and> t2 = Unit)"
  shows "\<exists>nabla s P'. ((t1 \<approx>? t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P'"
using assms
proof -
  have "\<exists> s P2. ((t1 \<approx>? t2) # xs, ys) \<turnstile> s \<leadsto> P2"
    using sred_exists_if_same_shape[OF assms] by simp
  then obtain s P2 where
  step: "((t1 \<approx>? t2) # xs, ys) \<turnstile> s \<leadsto> P2"
    by auto
  then have "((t1 \<approx>? t2) # xs, ys) \<Turnstile> ({}, s) \<Rightarrow> P2"
    using sred_single by simp
  then show ?thesis by blast
qed


lemma not_reduce_then_fail:
  assumes "\<not> (\<exists>nabla s P'. ((t1 \<approx>? t2) # xs, ys) \<Turnstile> (nabla,s) \<Rightarrow> P')"
  shows "fail ((t1 \<approx>? t2) # xs, ys)"
  using assms
proof-
  have no_shape:
  "\<not> ((t1 = Paar t11 t12 \<and> t2 = Paar t21 t22) \<or>
      (t1 = Func F t1' \<and> t2 = Func F t2') \<or>
      (t1 = Abst a t1' \<and> t2 = Abst a t2') \<or>
      (t1 = Abst a t1' \<and> t2 = Abst b t2' \<and> a \<noteq> b) \<or>
      (t1 = Atom a \<and> t2 = Atom a) \<or>
      (t1 = Susp pi1 X \<and> t2 = Susp pi2 X) \<or>
      (t1 = Susp pi X \<and> t2 = t \<and> \<not> occurs X t) \<or>
      (t1 = t \<and> t2 = Susp pi X \<and> \<not> occurs X t) \<or>
      (t1 = Unit \<and> t2 = Unit))"
  for t11 t12 t21 t22 F t1' t2' a b pi1 pi2 pi X t
    using assms red_plus_exists_if_same_shape by blast 


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
  case (Susp pi X)
  then show "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla, s) \<Rightarrow> P2"
    using cred_single by blast
next
  case Unit
  then show "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla, s) \<Rightarrow> P2"
    using cred_single by blast
next
  case (Atom b)
  with assms
  have "a \<noteq> b" by simp
  hence "([], (a \<sharp>? t) # xs) \<turnstile> {}\<rightarrow> ([],xs)"
    unfolding Atom using atom_cred by simp
  then show "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla, s) \<Rightarrow> P2"
    using cred_single by blast
next
  case (Paar t1 t2)
  then show "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla, s) \<Rightarrow> P2"
    using cred_single by blast
next
  case (Func f t')
  then show "\<exists>P2 nabla s. ([], (a \<sharp>? t) # xs) \<Turnstile> (nabla, s) \<Rightarrow> P2"
    using cred_single by blast
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
    show "P \<in> stuck" sorry}
qed


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
shows" (\<forall>P \<in> results P1. fail P)"
  using assms
  sorry

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