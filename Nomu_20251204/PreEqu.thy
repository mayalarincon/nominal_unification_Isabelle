theory PreEqu

imports Main  Swap  Terms  Disagreement  Fresh

begin


inductive equ :: "fresh_envs \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" (" _ \<turnstile> _ \<approx> _" [80,80,80] 80) where
equ_abst_ab[intro!]: "\<lbrakk>a\<noteq>b;(nabla \<turnstile> a \<sharp> t2);(nabla \<turnstile> t1 \<approx> (swap [(a,b)] t2))\<rbrakk> 
                      \<Longrightarrow> (nabla \<turnstile> Abst a t1 \<approx> Abst b t2)" |
equ_abst_aa[intro!]: "(nabla \<turnstile> t1 \<approx> t2) \<Longrightarrow> (nabla \<turnstile> Abst a t1 \<approx> Abst a t2)" |
equ_unit[intro!]:    "(nabla \<turnstile> Unit \<approx> Unit)" |
equ_atom[intro!]:    "a=b\<Longrightarrow>nabla \<turnstile> Atom a \<approx> Atom b" |
equ_susp[intro!]:    "(\<forall> c \<in> ds pi1 pi2. (c,X) \<in> nabla) \<Longrightarrow> (nabla \<turnstile> Susp pi1 X \<approx> Susp pi2 X)" |
equ_paar[intro!]:    "\<lbrakk>(nabla \<turnstile> t1\<approx>t2);(nabla \<turnstile> s1\<approx>s2)\<rbrakk> \<Longrightarrow> (nabla \<turnstile> Paar t1 s1 \<approx> Paar t2 s2)" |
equ_func[intro!]:    "(nabla \<turnstile> t1 \<approx> t2) \<Longrightarrow> (nabla \<turnstile> Func F t1 \<approx> Func F t2)"

inductive_cases Equ_elims:
"nabla \<turnstile> Atom a \<approx> Atom b"
"nabla \<turnstile> Unit \<approx> Unit"
"nabla \<turnstile> Susp pi1 X \<approx> Susp pi2 X"
"nabla \<turnstile> Paar s1 t1 \<approx> Paar s2 t2"
"nabla \<turnstile> Func F t1 \<approx> Func F t2"
"nabla \<turnstile> Abst a t1 \<approx> Abst a t2"
"nabla \<turnstile> Abst a t1 \<approx> Abst b t2"


lemma equ_depth: 
  assumes "nabla \<turnstile> t1 \<approx> t2"
  shows "depth t1 = depth t2"
  using assms by (rule equ.induct, simp_all)


lemma rev_pi_pi_equ: "(nabla \<turnstile> swap (rev pi) (swap pi t) \<approx> t)"
apply(induct t)
       apply(auto)
  by (metis ds_rev elem_ds swapas_append swapas_rev_pi_a)

lemma equ_pi_right: 
  assumes "\<forall>a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t"
  shows "nabla \<turnstile> t \<approx> swap pi t"
  using assms
proof(induct t arbitrary: pi)
   case (Abst b t')
   have "swapas pi b = b \<or> swapas pi b \<noteq> b" by blast
  moreover 
  { assume eq: "swapas pi b = b"
    have "nabla \<turnstile> Abst b t' \<approx> Abst b (swap pi t')"
      apply (rule equ_abst_aa)
      apply (rule Abst.hyps)
      apply (rule ballI)
      subgoal for a 
        apply (rule Fresh_elims(1)[of nabla a b t'])
        using Abst.prems elem_ds[of a pi] eq by auto
      done
    then have "nabla \<turnstile> Abst b t' \<approx> swap pi (Abst b t')" using eq by simp
  }
  moreover
  { assume neq: "b \<noteq> swapas pi b"  
    obtain c where c_def: "c = swapas pi b" by simp
    have "c \<in> ds [] pi"
      by (metis append.right_neutral c_def ds_cancel_pi_front ds_cancel_pi_left ds_elem neq)
    then have one: "nabla \<turnstile> c \<sharp> Abst b t'" using assms Abst.prems by auto
    have two: "b \<noteq> c" using neq c_def by blast
    have "nabla \<turnstile> c \<sharp> t'" using one two by cases auto
    have "nabla \<turnstile> Abst b t' \<approx> Abst c (swap pi t')" 
    proof(rule equ_abst_ab)
      show "b \<noteq> c" using neq c_def by blast
      have b_is_swap: "b = swapas (rev pi) c" using c_def by simp
      show "nabla \<turnstile> b \<sharp> swap pi t'" 
        using Abst.prems Fresh_elims(1) ds_elem fresh_swap_right neq swapas_rev_pi_a by metis
      show "nabla \<turnstile> t' \<approx> swap [(b, c)] (swap pi t')"
      proof -
         have fresh_ext:
          "\<forall>a \<in> ds [] ((b,c) # pi). nabla \<turnstile> a \<sharp> t'"
        proof (rule ballI)
          fix a assume A: "a \<in> ds [] ((b,c)#pi)"
          then have "a = c \<or> a \<in> ds [] pi"
            using c_def ds_7 neq by auto  
          then show "nabla \<turnstile> a \<sharp> t'"
          proof
            assume "a = c"
            with \<open>nabla \<turnstile> c \<sharp> t'\<close> show ?thesis by simp
          next
            assume "a \<in> ds [] pi"
            show ?thesis 
            proof(rule Fresh_elims(1)[of nabla a b t'], goal_cases)
              case 1
              then show ?case
                using Abst.prems \<open>a \<in> ds [] pi\<close>
              by simp
            next
              case 2
              then show ?case by simp
            next
              case 3
              have "a \<noteq> swapas ((b, c) # pi) a" 
                using A elem_ds
                by blast
              hence "a \<noteq> b" using c_def A 
                by (auto simp add: if_split)
              hence False using 3 by simp
              then show ?case by simp
          qed
        qed
      qed
        from Abst.hyps[OF fresh_ext]
        have "nabla \<turnstile> t' \<approx> swap ([(b,c)]@pi) t'"
          by simp
        moreover have "swap ([(b,c)]@pi) t' = swap [(b,c)] (swap pi t')"
          using swap_append by blast
        ultimately show ?thesis by simp
      qed
    qed
   then have "nabla \<turnstile> Abst b t' \<approx> swap pi (Abst b t')" using neq c_def by force
 }

  ultimately show ?case by argo

next
  case (Susp pi' X)
  have "\<forall>a\<in>ds [] pi. nabla \<turnstile> a \<sharp> Susp pi' X" by fact
  then have "nabla \<turnstile> Susp pi' X \<approx> Susp (pi @ pi') X"
   using Fresh_elims(4) equ_susp ds_def ds_cancel_pi_left
   by (metis (lifting) append_self_conv2 swapas_rev_pi_a)
  then show ?case by simp
next
  case Unit
  then show ?case 
    using equ_unit swap.simps(2) by force
next
  case (Atom b)
    then show ?case
      apply simp
    apply (rule equ_atom)
    using Fresh_elims(3) ds_elem_cp
    by metis
next
  case (Paar t1 t2)
  then have hypsp1: "(\<forall>a\<in>ds [] pi.  nabla \<turnstile> a \<sharp> t1)"
    and hypsp2: "(\<forall>a\<in>ds [] pi.  nabla \<turnstile> a \<sharp> t2)"
    using Paar.prems Fresh_elims(5) 
     apply meson
    using Paar.prems Fresh_elims(5) by blast
  have "nabla \<turnstile> Paar t1 t2 \<approx> Paar (swap pi t1) (swap pi t2)"
    apply(rule equ_paar)
     apply(rule Paar.hyps)
     apply (simp add: hypsp1)
    by (simp add: Paar.hyps(2) hypsp2)
  then show ?case by simp
next
  case (Func f t')
  then have hypsf: "\<forall>a\<in>ds [] pi. nabla \<turnstile> a \<sharp> t'" using fresh_func
    by (metis Fresh_elims(6))
  have "nabla \<turnstile> Func f t' \<approx> Func f (swap pi t')"
    apply(rule equ_func)
    apply(rule Func.hyps)
    using hypsf by auto
  then show ?case
    by simp
qed

lemma perm_invariance: 
assumes "\<forall>a \<in> ds pi pi'. nabla \<turnstile> a \<sharp> t"
shows "nabla \<turnstile> swap pi t \<approx> swap pi' t"
proof-
  have "nabla \<turnstile> t \<approx> swap (rev pi @ pi') t"
    using ds_rev equ_pi_right assms
    by simp
  oops

lemma pi_comm: "nabla \<turnstile> (swap (pi @ [(a,b)]) t) \<approx> (swap ([(swapas pi a, swapas pi b)] @ pi) t)"
proof(induct t)
  case (Abst c t)
  then show ?case using swapas_comm by force
next
  case (Susp \<pi>' X)
  have rew1:
    "swap (pi @ [(a,b)]) (Susp \<pi>' X) = Susp (pi @ [(a,b)] @ \<pi>') X"
    by simp
  have rew2:
    "swap ([(swapas pi a, swapas pi b)] @ pi) (Susp \<pi>' X) 
    = Susp ([(swapas pi a, swapas pi b)] @ pi @ \<pi>') X"
    by simp
  have fresh:
  "\<forall>c \<in> ds (pi @ [(a,b)] @ \<pi>') ([(swapas pi a, swapas pi b)] @ pi @ \<pi>'). (c, X) \<in> nabla"
    using swapas_append swapas_comm ds_def by simp
  from rew1 rew2 fresh
  show ?case
    using equ_susp by simp
next
  case Unit
  then show ?case by force
next
  case (Atom c)
  then show ?case 
    using equ_atom swapas_comm by auto
next
  case (Paar t1 t2)
  then show ?case by force
next
  case (Func f t)
  then show ?case by force
qed


lemma l3_jud: 
  assumes "(nabla \<turnstile> t1 \<approx> t2)"
  shows "(nabla \<turnstile> a \<sharp> t1) \<longrightarrow> (nabla \<turnstile> a \<sharp> t2)"
  using assms
proof(induction rule: equ.induct)
  case (equ_abst_ab b c nabla t2 t1)
  then show ?case 
    using fresh_swap_left Fresh_elims(1) fresh_abst_aa fresh_abst_ab rev_singleton_conv swapa.simps swapas.simps(1,2)
    by metis
next
  case (equ_abst_aa nabla t1 t2 b)
  then show ?case using fresh_swap_left Fresh_elims(1) fresh_abst_aa fresh_abst_ab 
    by metis
next
  case (equ_unit nabla)
  then show ?case
    by blast
next
  case (equ_atom b c nabla)
  then show ?case 
    by simp
next
  case (equ_susp pi1 pi2 X nabla)
  then show ?case 
    using Fresh_elims(4) ds_elem_cp ds_rev fresh_susp swapas_append swapas_rev_pi_a
    by metis
next
  case (equ_paar nabla t1 t2 s1 s2)
  then show ?case
    using Fresh_elims(5) by blast
next
  case (equ_func nabla t1 t2 f)
  then show ?case 
    using Fresh_elims(6) by blast
qed

(*lemma equ_symm:
  shows "(nabla \<turnstile> t1 \<approx> t2) \<Longrightarrow> (nabla \<turnstile> t2 \<approx> t1)"
proof(induction rule: equ.induct)
  case (equ_abst_ab a b nabla t2 t1)
  then show ?case sorry
next
  case (equ_abst_aa nabla t1 t2 a)
  then show ?case sorry
next
  case (equ_unit nabla)
  then show ?case sorry
next
  case (equ_atom a b nabla)
  then show ?case sorry
next
  case (equ_susp pi1 pi2 X nabla)
  then show ?case sorry
next
  case (equ_paar nabla t1 t2 s1 s2)
  then show ?case sorry
next
  case (equ_func nabla t1 t2 F)
  then show ?case sorry
qed
*)

lemma big: 
  assumes "n = depth t1"
  shows "(((nabla \<turnstile> t1 \<approx> t2)\<longrightarrow>(nabla \<turnstile> t2 \<approx> t1))\<and>  
              (\<forall>pi. (nabla \<turnstile> t1 \<approx> t2) \<longrightarrow> (nabla \<turnstile> swap pi t1 \<approx> swap pi t2))\<and> 
              ((nabla \<turnstile> t1 \<approx> t2)\<and>(nabla \<turnstile> t2 \<approx> t3) \<longrightarrow> (nabla \<turnstile> t1 \<approx> t3)))"
  using assms
proof(induction n arbitrary: t1 t2 t3 rule: nat_less_induct)
  case (1 n)
  note IH = this
  have IH_usable : "n > depth t1 \<Longrightarrow> nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow>  nabla \<turnstile> t2 \<approx> t1" 
     "n > depth t1 \<Longrightarrow> nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow>  nabla \<turnstile> swap pi t1 \<approx> swap pi t2"
     "n > depth t1 \<Longrightarrow> nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow>  nabla \<turnstile> t2 \<approx> t3 \<Longrightarrow>  nabla \<turnstile> t1 \<approx> t3"
     for t1 t2 t3 pi using IH 
    by blast+
  have "nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow>  nabla \<turnstile> t2 \<approx> t1"
  proof-
    assume "nabla \<turnstile> t1 \<approx> t2" 
    show ?thesis
  proof(cases rule: equ.cases[OF \<open>nabla \<turnstile> t1 \<approx> t2\<close>])
    case (1 a b nabla t2' t1')
    have depth1: "depth t1' < depth t1" 
      using 1(2) depth.simps(4) by simp
    then have i: "nabla \<turnstile> swap [(a, b)] t2' \<approx> t1'"
      using IH 1(1,6) by blast
    have ii: "nabla \<turnstile> b \<sharp> swap [(a, b)] t2'" 
      using fresh_swap_eqvt[of nabla a t2' "[(a,b)]"] "1"(5)
      by fastforce
    from i ii have b_fresh: "nabla \<turnstile> b \<sharp> t1'"
      using l3_jud by blast
    from i have iii: "nabla \<turnstile> swap [(b,a)] (swap [(a, b)] t2') \<approx> swap [(b,a)] t1'"
      using "1"(1) "1.prems" IH_usable(2) depth1 equ_depth by auto
    then have swap_ba_ab_t2: "nabla \<turnstile> swap ([(b,a)]@ [(a, b)]) t2' \<approx> swap [(b,a)] t1'"
      using swap_append by presburger
    have "nabla \<turnstile> swap ([(b,a)]@ [(a, b)]) t2' \<approx> t2'" 
      using rev_pi_pi_equ "1"(1,4,6) "1.prems" IH_usable(1) 
        depth1 ds_baab equ_depth equ_pi_right by auto
    then have "nabla \<turnstile>  t2' \<approx> swap ([(b,a)]@ [(a, b)]) t2'"
      using "1"(1,6) "1.prems" IH_usable(1) depth1 equ_depth swap_depth
      by metis
    then have equ_swap: "nabla \<turnstile> t2' \<approx> swap [(b, a)] t1'"
      using IH_usable(3)[of t2' \<open>swap ([(b,a)]@ [(a, b)]) t2'\<close> \<open>swap [(b, a)] t1'\<close>] iii
        "1"(1) "1.prems" depth1 equ_depth swap_ba_ab_t2 swap_depth
      by metis
    from b_fresh equ_swap show ?thesis
      using "1"(1,2,3,4)
      by fastforce
  next
    case (2 nabla t1' t2' a)
    then show ?thesis 
      using IH by auto
  next
    case (3 nabla)
    then show ?thesis
      by blast
  next
    case (4 a b nabla)
    then show ?thesis 
      by force
  next
    case (5 pi1 pi2 X nabla)
    then show ?thesis 
      using ds_sym by fast
  next
    case (6 nabla t1' t2' s1' s2')
    have depth1: "depth t1' < depth t1" 
      using "6"(2) by simp
    have depth2: "depth s1' < depth t1" 
      using "6"(2) by simp
    from depth1 depth2 have "nabla \<turnstile> t2' \<approx> t1' \<and> nabla \<turnstile> s2' \<approx> s1'"
      using "1.IH" "1.prems" "6"(1,4,5) by blast
    then show ?thesis 
      using equ_paar 6(1,2,3)
      by fast
  next
    case (7 nabla t1' t2' f)
    then show ?thesis
      using "1.prems" IH_usable(1) by auto
  qed
  qed
  moreover have "nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow>  nabla \<turnstile> swap pi t1 \<approx> swap pi t2"
    for pi 
  proof-
    assume "nabla \<turnstile> t1 \<approx> t2"
    show ?thesis 
    proof(cases rule: equ.cases[OF \<open>nabla \<turnstile> t1 \<approx> t2\<close>])
    case (1 a b nabla t2' t1')
    from this have depth_less: "depth t1' < depth t1"
      by force
    then have "nabla \<turnstile> swap pi t1' \<approx> swap pi (swap [(a,b)] t2')"
       using "1"(1,6) "1.IH" "1.prems" by blast
    then have A: "nabla \<turnstile> swap pi t1' \<approx> swap (pi @ [(a,b)]) t2'"
      using swap_append by presburger
    have "nabla \<turnstile> swap (pi @ [(a,b)]) t2' \<approx> (swap ([(swapas pi a, swapas pi b)] @ pi) t2')"
      using pi_comm by force
    then have B: "nabla \<turnstile> swap (pi @ [(a,b)]) t2' \<approx> swap [(swapas pi a, swapas pi b)] (swap pi t2')"
      using swap_append
      by metis
    have pi_a_fresh: "nabla \<turnstile> swapas pi a \<sharp> swap pi t2'"
      using 1(5) fresh_swap_eqvt
      by simp
    have "nabla \<turnstile> swap pi t1' \<approx> swap [(swapas pi a, swapas pi b)] (swap pi t2')"
      apply (rule IH_usable(3)[simplified 1(1), OF _ A B])
      using  depth_less IH(2) 
      by auto
    then show ?thesis
      by (metis "1"(1,2,3,4) equ_abst_ab pi_a_fresh swap.simps(4) swapas_rev_pi_a)
  next
    case (2 nabla t1' t2' a)
    from this have "depth t1' < depth t1"
      by force
    then have "nabla \<turnstile> swap pi t1' \<approx> swap pi t2'"
      using "1.prems" "2"(1,4) IH_usable(2)
      by blast
    then have abst: "nabla \<turnstile> Abst (swapas pi a) (swap pi t1') \<approx> Abst (swapas pi a) (swap pi t2')"
      using equ_abst_aa[of nabla "swap pi t1'" "swap pi t2'" "swapas pi a"]
      by blast
    from abst "2"(1,2,3) show ?thesis
      by simp
  next
    case (3 nabla)
    then show ?thesis
      by force
  next
    case (4 a b nabla)
    then show ?thesis
      by auto
  next
    case (5 pi1 pi2 X nabla)
    then show ?thesis 
      using swap.simps(3) ds_cancel_pi_front[of pi pi1 pi2] equ_susp[of pi1 pi2]
      by auto
  next
    case (6 nabla t1' t2' s1' s2')
    from this 
    have depths1: "depth t1' < depth t1" "depth s1' < depth t1" 
        using depth.simps(6) by auto
      then have depths2: "depth t2' < depth t1" "depth s2' < depth t1"
       using equ_depth "6"(4,5) by auto
    then have "nabla \<turnstile> t2' \<approx> t1'"
      using "1.prems" "6"(1,4,5) IH_usable(1) depths1
      by blast
    then have par1: "nabla \<turnstile> swap pi t2' \<approx> swap pi t1'" 
      using 6(1) "1.prems"  depths2  IH_usable(2)[of t2' t1' pi] 
      by simp
    from depths1 have "nabla \<turnstile> s2' \<approx> s1'"
      using "1.prems" "6"(1,4,5) IH_usable(1) by auto
    then have par2: "nabla \<turnstile> swap pi s2' \<approx> swap pi s1'" 
      using 6(1) "1.prems"  depths2  IH_usable(2)[of s2' s1' pi] 
      by simp
    from par1 par2 show ?thesis 
      using 6 "1.prems" IH_usable(1) depths2 equ_paar swap.simps(5) swap_depth
      by presburger
  next
    case (7 nabla t1' t2' f)
    from this have "depth t1' < depth t1"
      using depth.simps(5)
      by fastforce
    then have "nabla \<turnstile> swap pi t1' \<approx> swap pi t2'"
     using "1.prems" "7"(1,4) IH_usable(2) by auto
    then show ?thesis
      using equ_func 7 by simp
  qed
  qed
  moreover have "nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow> nabla \<turnstile> t2 \<approx> t3 \<Longrightarrow>  nabla \<turnstile> t1 \<approx> t3"
  proof-
    assume t12: "nabla \<turnstile> t1 \<approx> t2" and t23: "nabla \<turnstile> t2 \<approx> t3"
    show ?thesis 
     proof(cases rule: equ.cases[OF \<open>nabla \<turnstile> t1 \<approx> t2\<close>])
       case (1 a b nabla t2' t1')
       note case12 = this
       from t23 show ?thesis 
       proof(cases rule: equ.cases)
         case (equ_abst_ab b c t3' t2')
         have deptht1: "depth t1' < n"
           using depth.simps(4) 1(2) "1.prems"
           by auto
         hence deptht2: "depth t2' < n" 
           using equ_depth 1(3,6) equ_abst_ab(1)
           by auto
         hence deptht3: "depth t3' < n" 
           using equ_depth 1 equ_abst_ab(1,5) by simp
         then show ?thesis 
         proof(cases "a = c")
           case True
           have  t1t2: "nabla \<turnstile> t1' \<approx> swap [(c,b)] t2'"
             using True 1(3,6) equ_abst_ab(1) by auto
           have i: "nabla \<turnstile> t2' \<approx> swap [(b,c)] t3'"
             using 1(1) equ_abst_ab(5)
             by blast
           hence ii: "nabla \<turnstile> swap [(c,b)] t2' \<approx> swap [(c,b)] (swap [(b,c)] t3')"
             using IH_usable(2)[OF deptht2] 1(1)
             by blast
           have iii: "nabla \<turnstile> swap [(c,b)] t2' \<approx> swap ([(c,b)]@[(b,c)]) t3'"
             using swap_append ii
             by presburger
           have v: "nabla \<turnstile> swap ([(c,b)]@ [(b, c)]) t3' \<approx> t3'"
             using IH_usable(1) 1(1) deptht1 ds_baab equ_depth 
               equ_pi_right i local.equ_abst_ab(3) t1t2
              by auto
           from iii v  have iv: "nabla \<turnstile> swap [(c,b)] t2' \<approx> t3'"
             using IH_usable(3)[of \<open>swap [(c,b)] t2'\<close>] 1(1) deptht2
             by auto
           from t1t2 iv have "nabla \<turnstile> t1' \<approx> t3'"
             using deptht1 1(1) IH_usable(3)[of t1' \<open>swap [(c, b)] t2'\<close> t3']
             by blast
           then show ?thesis 
             using True 1(1,2) equ_abst_aa equ_abst_ab(2) by simp
         next
           case False

           have a_fresh_bc_t3: "nabla \<turnstile> a \<sharp> swap [(b,c)] t3'"
             using l3_jud 1(1,3,5) equ_abst_ab(1,5)
             by blast
           hence "nabla \<turnstile> swapas [(b,c)] a \<sharp> t3'"
             using fresh_swap_left
             by fastforce
           hence a_fresh_t3: "nabla \<turnstile> a \<sharp> t3'"
             using False 1(3,4) equ_abst_ab(1,3)
             by fastforce 
            
           have t1t2: "nabla \<turnstile> t1' \<approx> swap [(a,b)] t2'"
             using 1(3,6) equ_abst_ab(1) by auto
           have t2t3: "nabla \<turnstile> t2' \<approx> swap [(b,c)] t3'"
             using 1(1) equ_abst_ab(5)
             by blast
           hence i: "nabla \<turnstile> swap [(a,b)] t2' \<approx> swap ([(a,b)]@[(b,c)]) t3'"
             using 1(1) IH_usable(2)[OF deptht2] swap_append
             by presburger
           from t1t2 i have ii: "nabla \<turnstile> t1' \<approx> swap ([(a,b),(b,c)]) t3'"
             using 1(1) IH_usable(3)[OF deptht1] by auto


           have "ds [] [(a, c), (a, b), (b, c)] = {a, b}"
             using ds_acabbc False 1(3,4) equ_abst_ab(1,3) by auto
           hence "nabla \<turnstile> t3' \<approx> swap [(a, c), (a, b), (b, c)] t3'"
             using 1(1) equ_pi_right equ_abst_ab(4) a_fresh_t3 
             by simp
           hence "nabla \<turnstile> t3' \<approx> swap [(a, c)] (swap [(a, b), (b, c)] t3')"
             using  swap_append Cons_eq_append_conv
             by metis
           hence iii: "nabla \<turnstile> swap [(a,c)] t3' \<approx> swap [(a,c)] (swap [(a, c)] (swap [(a, b), (b, c)] t3'))"
             using IH_usable(2)[OF deptht3] 1(1) by auto
           have iv: "nabla \<turnstile> swap [(a, c)] (swap [(a, c)] (swap [(a, b), (b, c)] t3')) \<approx> (swap [(a, b), (b, c)] t3')" 
             using rev_pi_pi_equ rev_singleton_conv
             by metis
           from iii iv have "nabla \<turnstile> swap [(a,c)] t3' \<approx> swap [(a, b), (b, c)] t3'" 
             using IH_usable(3)[of \<open>swap [(a,c)] t3'\<close> 
                 \<open>swap [(a,c)] (swap [(a, c)] (swap [(a, b), (b, c)] t3'))\<close>
                 \<open>(swap [(a, b), (b, c)] t3')\<close>] 
               swap_depth 1(1) deptht3 by force
           hence v: "nabla \<turnstile> swap [(a, b), (b, c)] t3' \<approx> swap [(a,c)] t3'"
             using IH_usable(1)[of \<open>swap [(a,c)] t3'\<close> \<open>swap [(a, b), (b, c)] t3'\<close>] 
               deptht3 swap_depth 1(1) 
             by simp

           from ii v have t1_equal_ac_t3: "nabla \<turnstile> t1' \<approx> swap [(a, c)] t3'"
             using 1(1) IH_usable(3)[OF deptht1] 
             by blast

           from a_fresh_t3 t1_equal_ac_t3 show ?thesis 
             using 1(1,2) equ_abst_ab(2) equ.equ_abst_ab[OF False] by simp
         qed
       next
         case (equ_abst_aa t2' t3' b)
         have deptht1: "depth t1' < n"
           using depth.simps(4) 1(2) "1.prems"
           by force
         have a_fresh_t2: "nabla \<turnstile> a \<sharp> t2'"
           using 1(3,5) equ_abst_aa(1) by blast
         have i: "nabla \<turnstile> t1' \<approx> swap [(a, b)] t2'"
           using 1(3,6) equ_abst_aa(1) by fast
         hence deptht2: "depth t2' < n"
           using deptht1 equ_depth by simp
         hence ii: "nabla \<turnstile> swap [(a,b)] t2' \<approx> swap [(a,b)] t3'"
           using IH_usable(2)[of t2' t3' \<open>[(a,b)]\<close>] equ_abst_aa(3) 1(1) by blast
         from i ii have iii: "nabla \<turnstile> t1' \<approx> swap [(a,b)] t3'"
           using IH_usable(3) deptht1 1(1) 
           by blast
         from a_fresh_t2 have iv: "nabla \<turnstile> a \<sharp> t3'"
           using 1(1) l3_jud equ_abst_aa(3) by presburger
         from iii iv show ?thesis 
           using equ_abst_ab 1(1,2,3,4) equ_abst_aa(1,2)
           by fast
       next
         case equ_unit
         then show ?thesis
           using t12 by auto
       next
         case (equ_atom b c)
         then show ?thesis using t12 by auto
       next
         case (equ_susp pi2 pi3 X)
         then show ?thesis
           using case12(3) by blast
       next
         case (equ_paar t2' t3' s2' s3')
         then show ?thesis
           using case12(3) by blast
       next
         case (equ_func t2' t3' f)
         then show ?thesis
           using case12(3) by blast
       qed
  next
    case (2 nabla t1' t2' a)
   from t23 show ?thesis 
       proof(cases rule: equ.cases)
         case (equ_abst_ab a c t3' t2')
         have deptht1: "depth t1' < n"
          using IH depth.simps(1) "2"(2) by auto
         have i: "nabla \<turnstile> t1' \<approx> t2'"
           using 2(3,4) equ_abst_ab(1) by blast
         have ii: "nabla \<turnstile> t2' \<approx> swap [(a, c)] t3'"
           using 2(1) local.equ_abst_ab(5) by blast
         from i ii have iii: "nabla \<turnstile> t1' \<approx> swap [(a, c)] t3'"
           using "1.IH" 2(1) deptht1 by blast
         have iv: "nabla \<turnstile> a \<sharp> t3'" 
           using 2(1) equ_abst_ab(4)
           by blast
         from iii iv show ?thesis 
           using  2(1,2,3) local.equ_abst_ab(1,2,3) by blast
       next
         case (equ_abst_aa t2' t3' a)
         have "depth t1' < n" 
           using depth.simps(4) "2"(2) "1.prems" by simp
         then show ?thesis
           using "2"(1,2,3,4) IH_usable(3) local.equ_abst_aa(1,2,3) by blast
       next
         case equ_unit
         then show ?thesis
           using t12 by blast
       next
         case (equ_atom b c)
         then show ?thesis
           using t12 by blast
       next
         case (equ_susp pi2 pi3 X)
         then show ?thesis
          using 2(3) by simp 
       next
         case (equ_paar t2' t3' s2' s3')
         then show ?thesis 
           using 2(3) by simp 
       next
         case (equ_func t2' t3' f)
         then show ?thesis 
           using 2(3) by simp 
       qed
  next
    case (3 nabla)
    from t23 show ?thesis 
       proof(cases rule: equ.cases)
         case (equ_abst_ab a b t3' t2')
         then show ?thesis 
           using 3(3) by simp 
       next
         case (equ_abst_aa t2' t3' b)
         then show ?thesis
            using 3(3) by simp 
       next
         case equ_unit
         then show ?thesis
           using t12 by auto
       next
         case (equ_atom b c)
         then show ?thesis 
           using t12 by blast
       next
         case (equ_susp pi2 pi3 X)
         then show ?thesis 
           using 3(3) by simp 
       next
         case (equ_paar t2' t3' s2' s3')
         then show ?thesis 
           using 3(3) by simp 
       next
         case (equ_func t2' t3' f)
         then show ?thesis 
           using 3(3) by simp 
       qed
  next
    case (4 a b nabla)
    from t23 show ?thesis 
       proof(cases rule: equ.cases)
         case (equ_abst_ab a b t3' t2')
         then show ?thesis 
           using 4 by blast
       next
         case (equ_abst_aa t2' t3' b)
         then show ?thesis
           using 4 by blast
       next
         case equ_unit
         then show ?thesis 
          using 4 by blast
       next
         case (equ_atom b c)
         then show ?thesis 
          using 4 by blast
       next
         case (equ_susp pi2 pi3 X)
         then show ?thesis 
          using 4 by blast
       next
         case (equ_paar t2' t3' s2' s3')
         then show ?thesis 
          using 4 by blast
       next
         case (equ_func t2' t3' f)
         then show ?thesis 
           using 4 by blast
       qed
  next
    case (5 pi1 pi2 X nabla)
    from t23 show ?thesis 
       proof(cases rule: equ.cases)
         case (equ_abst_ab a b t3' t2')
         then show ?thesis 
           using 5 by blast
       next
         case (equ_abst_aa t2' t3' b)
         then show ?thesis
          using 5 by blast
       next
         case equ_unit
         then show ?thesis
          using 5 by blast
       next
         case (equ_atom b c)
         then show ?thesis
          using 5 by blast
       next
         case (equ_susp pi2 pi3 X)
         have a: "\<forall>c\<in>ds pi1 pi2. (c, X) \<in> nabla"
           using 5(3,4) equ_susp by simp
         have b: "\<forall>c\<in>ds pi2 pi3. (c, X) \<in> nabla" 
           using 5(1) equ_susp(3) by auto
         from a b have "\<forall>c\<in>ds pi1 pi3. (c, X) \<in> nabla"
           using ds_trans by blast
         hence "nabla \<turnstile> Susp pi1 X \<approx> Susp pi3 X"
           by blast
         then show ?thesis 
           using "5"(1,2,3) equ_susp(1,2)
           by blast
       next
         case (equ_paar t2' t3' s2' s3')
         then show ?thesis
           using 5 by blast
       next
         case (equ_func t2' t3' f)
         then show ?thesis 
           using 5 by blast
       qed
  next
    case (6 nabla t1' t2' s1' s2')
    from t23 show ?thesis 
       proof(cases rule: equ.cases)
         case (equ_abst_ab a b t3' t2')
         then show ?thesis 
           using 6 by blast
       next
         case (equ_abst_aa t2' t3' b)
         then show ?thesis 
          using 6 by blast
       next
         case equ_unit
         then show ?thesis 
          using 6 by blast
       next
         case (equ_atom b c)
         then show ?thesis 
          using 6 by blast
       next
         case (equ_susp pi2 pi3 X)
         then show ?thesis 
          using 6 by blast
       next
         case (equ_paar t2' t3' s2' s3')
         have deptht1: "depth t1' < n" 
           using IH depth.simps(6) "6"(2) by auto
         have depths1: "depth s1' < n" 
           using IH depth.simps(6) "6"(2) by auto
         have a: "nabla \<turnstile> t1' \<approx> t2'" 
           using "6"(3,4) equ_paar by auto
         have b: "nabla \<turnstile> s1' \<approx> s2'" 
           using "6" equ_paar by auto
         from a have t1_equal_t3: "nabla \<turnstile> t1' \<approx> t3'" 
           using IH_usable(3)[of t1' t2' t3'] equ_paar(3) 6(1) deptht1
           by fast
         from b have s1_equal_s3: "nabla \<turnstile> s1' \<approx> s3'" 
           using IH_usable(3)[of s1' s2' s3'] equ_paar(4) 6(1) depths1
           by fast
         from t1_equal_t3 s1_equal_s3 show ?thesis 
           using equ.equ_paar[of nabla t1' t3' s1' s3'] 6(1,2) equ_paar(2)
           by fast
       next
         case (equ_func t2' t3' f)
         then show ?thesis 
          using 6 by blast
       qed
  next
    case (7 nabla t1' t2' f)
    from t23 show ?thesis 
       proof(cases rule: equ.cases)
         case (equ_abst_ab a b t3' t2')
         then show ?thesis 
           using 7 by blast
       next
         case (equ_abst_aa t2' t3' b)
         then show ?thesis 
           using 7 by blast
       next
         case equ_unit
         then show ?thesis
          using 7 by blast
       next
         case (equ_atom b c)
         then show ?thesis 
          using 7 by blast
       next
         case (equ_susp pi2 pi3 X)
         then show ?thesis
          using 7 by blast
       next
         case (equ_paar t2' t3' s2' s3')
         then show ?thesis
          using 7 by blast
       next
         case (equ_func t2' t3' f)
         have deptht1: "depth t1' < n" 
           using IH depth.simps(5) "7"(2) by auto
         have "nabla \<turnstile>  t1' \<approx> t2'" 
           using "7"(3,4) equ_func(1) by auto
         hence "nabla \<turnstile> t1' \<approx> t3'" 
           using IH_usable(3)[of t1' t2' t3'] 7(1) deptht1 equ_func(3)
           by blast
         then show ?thesis 
           using equ.equ_func[of nabla t1' t3' f] 7(1,2,3) equ_func(1,2)
           by fast
       qed
  qed
  qed
  ultimately show ?case by simp
qed


(*
Case abab:
t1 = Abst a t1'
t2 = Abst b t2'
t3 = Abst c t3'

a\<noteq>b
b\<noteq>c
a\<noteq>c

i: nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow> nabla \<turnstile> a \<sharp> t2' and nabla \<turnstile> t1' \<approx> (a b) t2'
ii: nabla \<turnstile> t2 \<approx> t3 \<Longrightarrow> nabla \<turnstile> b \<sharp> t3' and nabla \<turnstile> t2' \<approx> (b c) t3'

eqv in ii pi =(ab)

iii: nabla \<turnstile> (a b) b \<sharp> (a b) t3' and nabla \<turnstile> (a b) t2' \<approx> (a b)(b c) t3'

iv: nabla \<turnstile> t1' \<approx> (a b)(b c) t3'

Goal:  nabla \<turnstile> Abs a t1' \<approx> Abst c t3'
       Subgoals: nabla \<turnstile> a \<sharp> t3' and nabla \<turnstile> t1' \<approx> (a c) t3'
*)



lemma pi_right_equ_help:
  assumes "(n=depth t)"
  shows "nabla \<turnstile> t \<approx> swap pi t \<Longrightarrow> \<forall> a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t"
  using assms
proof(induction n arbitrary: t pi rule: nat_less_induct)
  case (1 n)
  note IH = this
  then show ?case 
    proof(cases rule: equ.cases[OF \<open>nabla \<turnstile> t \<approx> swap pi t\<close>])
      case (1 b c nabla t2 t1)
        have deptht1: "depth t1 < n"
          using 1 depth.simps(4) IH by simp
        have swap_pi_t1_is_t2: "swap pi t1 = t2"
          using 1(2,3) by auto
        have swap_pi_b_is_c: "swapas pi b = c"
          using 1(2,3) by auto
        with swap_pi_t1_is_t2 have "nabla \<turnstile> t1 \<approx> swap [(b, swapas pi b)] (swap pi t1)"
          using 1(1,6) by simp
        then have "nabla \<turnstile> t1 \<approx> swap ([(b, swapas pi b)] @ pi) t1"
          using swap_append[of \<open>[(b, swapas pi b)]\<close> pi t1] by simp
        with deptht1 have "\<forall> a \<in> ds [] ((b, swapas pi b)#pi). nabla \<turnstile> a \<sharp> t1"
          using "1.IH" 1 by auto
        then have ds_minus_bc: "\<forall> a \<in> ds [] pi - {b, c}. nabla \<turnstile> a \<sharp> t1"
          using ds_equality swap_pi_b_is_c by auto
        have c_fresh_t1: "nabla \<turnstile> c \<sharp> t1"
          using 1(4,5,6) l3_jud big fresh_swap_eqvt Equ_elims(7) equ_abst_ab by metis
        with ds_minus_bc have "\<forall> a \<in> ds [] pi - {b}. nabla \<turnstile> a \<sharp> t1"
          by auto
        then have ds_minus_b: "\<forall> a \<in> ds [] pi - {b}. nabla \<turnstile> a \<sharp> Abst b t1"
          using fresh_abst_ab by blast
        have b_fresh_abst_t1: "nabla \<turnstile> b \<sharp> Abst b t1"
          using fresh_abst_aa by simp
        with ds_minus_b have "\<forall> a \<in> ds [] pi. nabla \<turnstile> a \<sharp> Abst b t1"
          using member_remove remove_def
          by metis
        with 1 show ?thesis
          by auto
    next
      case (2 nabla t1 t2 b)
      have deptht1: "depth t1 < n"
        using 2 depth.simps(4) IH by simp
      have swap_pi_t1_is_t2: "swap pi t1 = t2"
        using 2(2,3) by auto
      from swap_pi_t1_is_t2 deptht1 
      have "\<forall> a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t1"
        using "1.IH" 2(1,4) by auto
      then show ?thesis 
        using 2(1,2,3) elem_ds by fastforce
    next
      case (3 nabla)
      then show ?thesis 
        by blast
    next
      case (4 a b nabla)
      then show ?thesis
        using elem_ds by force
    next
      case (5 pi1 pi2 X nabla)
      have "swap pi t = Susp (pi@pi1) X" 
        using "5"(2) by auto
      also have "... = Susp pi2 X"
        using 5(3) calculation by simp
      then have "pi@pi1 = pi2" by simp
      hence "\<forall>c\<in>ds pi1 (pi@pi1). (c, X) \<in> nabla"
        using 5(4) by blast
      then show ?thesis 
        using "5"(1,2) fresh_susp ds_cancel_pi_right[of _ _ "[]" _]
          by force
    next
      case (6 nabla t1 t2 s1 s2)
      have deptht1: "depth t1 < n"
        using 6 depth.simps(5) IH
        by simp
      have depths1: "depth s1 < n"
        using 6 depth.simps(5) IH
        by simp
      from deptht1 depths1 show ?thesis 
        using "1.IH" 6 by auto
    next
      case (7 nabla t1 t2 f)
      have deptht1: "depth t1 < n"
        using 7(2) depth.simps(5) IH 
        by auto
      have "nabla \<turnstile> t1 \<approx> swap pi t1"
        using 7 by simp
      then have "\<forall> a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t1"
        using 7(1) IH deptht1 by simp
      then show ?thesis 
        using 7(1,2) fresh_func[of nabla _ t1 f] 
        by simp
    qed
  qed


end 
