theory Equ

imports Main  Terms  Fresh  PreEqu

begin

lemma equ_refl: 
  "nabla\<turnstile>t\<approx>t"
  by(induct t, auto simp add: ds_def)

lemma 
  equ_sym:    "nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow> nabla \<turnstile> t2 \<approx> t1" and
  equ_trans:  "\<lbrakk>nabla \<turnstile> t1 \<approx> t2 ; nabla \<turnstile> t2 \<approx> t3\<rbrakk> \<Longrightarrow> nabla \<turnstile> t1 \<approx> t3" and
  equ_add_pi: "nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow> nabla \<turnstile> swap pi t1 \<approx> swap pi t2"
  using big by blast+


lemma equ_dec_pi:
  "nabla \<turnstile> swap pi t1 \<approx> swap pi t2 \<Longrightarrow> nabla \<turnstile> t1 \<approx> t2"
proof-
  have i: "nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> t1"
    "nabla \<turnstile> swap (rev pi) (swap pi t2) \<approx> t2"
    using rev_pi_pi_equ by auto
  assume "nabla \<turnstile> swap pi t1 \<approx> swap pi t2"
  then have "nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> swap (rev pi) (swap pi t2)"
    using equ_add_pi by simp
  then show ?thesis using i equ_sym equ_trans by meson
qed


lemma equ_involutive_left: 
  "nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> t2 = nabla \<turnstile> t1 \<approx> t2"
proof(auto)
  have i: "nabla \<turnstile> t1 \<approx> swap (rev pi) (swap pi t1)"
    using rev_pi_pi_equ equ_sym by blast
  show "nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> t2 \<Longrightarrow> nabla \<turnstile> t1 \<approx> t2"
    using i equ_trans by blast
  show "nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow> nabla \<turnstile> swap (rev pi) (swap pi t1) \<approx> t2"
    using i equ_trans equ_sym by blast
qed


lemma equ_pi_to_left: 
  "nabla \<turnstile> swap (rev pi) t1 \<approx> t2 = nabla \<turnstile> t1 \<approx> swap pi t2"
proof

  {assume i: "nabla \<turnstile> swap (rev pi) t1 \<approx> t2"
  have "nabla \<turnstile> swap pi (swap (rev pi) t1) \<approx> swap pi t2"
    using equ_add_pi[OF i, of pi] by simp
  then show "nabla \<turnstile> t1 \<approx> swap pi t2"
    using equ_involutive_left[of nabla \<open>rev pi\<close> t1 \<open>swap pi t2\<close>] rev_rev_ident[of pi]
    by simp}

  {assume i: "nabla \<turnstile> t1 \<approx> swap pi t2"
  have ii: "nabla \<turnstile> swap (rev pi) t1 \<approx> swap (rev pi) (swap pi t2)"
    using equ_add_pi[OF i, of \<open>rev pi\<close>] by simp
  then have iii: "nabla \<turnstile> swap (rev pi) (swap pi t2) \<approx> swap (rev pi) t1"
    using equ_symm[OF ii] by simp
  then have iv: "nabla \<turnstile> t2 \<approx> swap (rev pi) t1"
    using equ_involutive_left[of nabla pi t2 \<open>swap (rev pi) t1\<close>] by simp
  then show "nabla \<turnstile> swap (rev pi) t1 \<approx> t2"
    using equ_symm[OF iv] by simp}

qed
    

lemma equ_pi_to_right: 
  "nabla\<turnstile>t1 \<approx> swap (rev pi) t2 = nabla\<turnstile>swap pi t1\<approx>t2"
proof
  {assume i: "nabla \<turnstile> t1 \<approx> swap (rev pi) t2"
    then show "nabla \<turnstile> swap pi t1 \<approx>  t2"
      using equ_involutive_left equ_dec_pi by blast}
  {assume ii: "nabla \<turnstile> swap pi t1 \<approx> t2"
    then show "nabla \<turnstile> t1 \<approx> swap (rev pi) t2"
      using equ_involutive_left equ_add_pi by blast}
qed


lemma equ_involutive_right: 
  "nabla \<turnstile> t1 \<approx> swap (rev pi) (swap pi t2) = nabla \<turnstile> t1 \<approx> t2"
apply(simp only: swap_append[THEN sym])
apply(simp only: equ_pi_to_left[THEN sym])
apply(simp)
apply(simp only: swap_append)
apply(simp only: equ_involutive_left)
done

lemma equ_pi1_pi2_add: 
  "(\<forall>a\<in> ds pi1 pi2. nabla\<turnstile>a\<sharp>t) \<Longrightarrow> (nabla\<turnstile>swap pi1 t \<approx> swap pi2 t)"
apply(simp only: equ_pi_to_right[THEN sym])
apply(simp only: swap_append[THEN sym])
apply(rule equ_pi_right)
apply(auto)
apply(simp only: ds_rev)
done

lemma pi_right_equ: "(nabla \<turnstile> t \<approx> swap pi t) \<Longrightarrow> (\<forall>a\<in> ds [] pi. nabla \<turnstile> a \<sharp> t)"
  using pi_right_equ_help by blast


lemma equ_pi1_pi2_dec:  
  "(nabla \<turnstile> swap pi1 t \<approx> swap pi2 t) \<Longrightarrow> (\<forall> a \<in> ds pi1 pi2. nabla\<turnstile>a \<sharp> t)"
apply(simp only: equ_pi_to_right[THEN sym])
apply(simp only: swap_append[THEN sym])
apply(drule pi_right_equ)
apply(simp only: ds_rev)
done

lemma equ_weak: 
  "nabla1 \<turnstile> t1 \<approx> t2 \<Longrightarrow> (nabla1 \<union> nabla2) \<turnstile> t1 \<approx> t2"
  by(erule equ.induct, auto simp add: fresh_weak)



(* no term can be equal to one of its proper subterm *)


lemma psub_trm_not_equ: 
  "\<forall> t2 \<in> psub_trms t1. (\<not>(\<exists> pi. (nabla \<turnstile> t1 \<approx> swap pi t2)))"
proof
  fix t2
  assume A: "t2 \<in> psub_trms t1"
  show "\<not> (\<exists>pi. nabla \<turnstile> t1 \<approx> swap pi t2)"
  proof
    assume "\<exists>pi. nabla \<turnstile> t1 \<approx> swap pi t2"
    then obtain pi where H:
      "nabla \<turnstile> t1 \<approx> swap pi t2" by blast

    from equ_depth[OF H]
    have "depth t1 = depth (swap pi t2)" .

    hence "depth t1 = depth t2" by simp

    moreover have "depth t2 < depth t1"
      using A by (rule depth_psub_trms)

    ultimately show False by auto
  qed
qed

end 
