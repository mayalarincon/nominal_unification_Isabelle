
theory Disagreement 

imports Main Swap  Atoms

begin

(*consts 
  ds :: "(string \<times> string) list \<Rightarrow> (string \<times> string) list \<Rightarrow> string set"
defs   
  ds_def: "ds xs ys  \<equiv>  { a . a \<in> (atms xs \<union> atms ys) \<and> (swapas xs a \<noteq> swapas ys a) }"*)

definition  ds :: "(string \<times> string) list \<Rightarrow> (string \<times> string) list \<Rightarrow> string set" where
  ds_def: "ds xs ys  \<equiv>  { a . a \<in> (atms xs \<union> atms ys) \<and> (swapas xs a \<noteq> swapas ys a) }"



lemma 
  ds_elem: "\<lbrakk>swapas pi a\<noteq>a\<rbrakk>\<Longrightarrow>a\<in>ds [] pi"
apply(simp add: ds_def)
apply(auto simp add: swapas_pi_ineq_a)
  done

corollary ds_elem_cp: "a \<notin> ds [] pi \<Longrightarrow> swapas pi a = a"
  using ds_elem by blast

lemma 
  elem_ds: "\<lbrakk>a\<in>ds [] pi\<rbrakk>\<Longrightarrow>a\<noteq>swapas pi a"
apply(simp add: ds_def)
  done


lemma 
  ds_sym: "ds pi1 pi2 = ds pi2 pi1"
apply(simp only: ds_def)
apply(auto)
  done



lemma 
  ds_trans: "c\<in>ds pi1 pi3\<longrightarrow>(c\<in>ds pi1 pi2 \<or> c\<in>ds pi2 pi3)"
apply(auto)
apply(simp only: ds_def)
apply(auto)
apply(drule a_not_in_atms)+
apply(simp)
apply(drule a_not_in_atms)
apply(simp)
apply(drule swapas_pi_ineq_a)
apply(assumption)
  done



lemma ds_cancel_pi_left:
  assumes "(c\<in> ds (pi1@pi) (pi2@pi))"
  shows "(swapas pi c \<in> ds pi1 pi2)"
  using ds_def swapas_append a_ineq_swapas_pi a_not_in_atms
  by (metis (mono_tags, lifting) Un_iff assms mem_Collect_eq)



lemma ds_cancel_pi_right: 
  "(swapas pi c\<in> ds pi1 pi2) \<longrightarrow> (c\<in> ds (pi1@pi) (pi2@pi))"
apply(simp only: ds_def)
apply(auto)
apply(simp_all add: swapas_append)
apply(rule a_ineq_swapas_pi,clarify,
      drule a_not_in_atms,drule a_not_in_atms,simp)+
  done



lemma ds_equality: 
  "(ds [] pi)-{a,swapas pi a} = (ds [] ((a,swapas pi a)#pi))-{swapas pi a}"
apply(simp only: ds_def)
apply(auto)
  done



lemma ds_7: 
  "\<lbrakk>b\<noteq> swapas pi b;a\<in>ds [] ((b,swapas pi b)#pi)\<rbrakk>\<Longrightarrow>a\<in>ds [] pi"
apply(simp only: ds_def)
apply(case_tac "b=a")
apply(auto)
apply(rule swapas_pi_in_atms)
apply(drule a_ineq_swapas_pi)
apply(assumption)
apply(drule sym)
apply(drule swapas_rev_pi_a)
apply(simp)
apply(case_tac "swapas pi b = a")
apply(auto)
apply(drule sym)
apply(drule swapas_rev_pi_a)
apply(simp)
done



lemma ds_cancel_pi_front: 
  "ds (pi@pi1) (pi@pi2) = ds pi1 pi2"
apply(simp only: ds_def)
apply(auto)
apply(simp_all add: swapas_append)
apply(rule swapas_pi_ineq_a, clarify, drule a_not_in_atms, simp)+
apply(drule swapas_rev_pi_a, simp)+
done

lemma ds_rev_pi_pi: 
  "ds ((rev pi1)@pi1) pi2 = ds [] pi2"
apply(simp only: ds_def)
apply(auto)
apply(simp_all add: swapas_append)
apply(drule a_ineq_swapas_pi, assumption)+
done

lemma ds_rev: 
  "ds [] ((rev pi1)@pi2) = ds pi1 pi2"
apply(subgoal_tac "ds pi1 pi2 = ds ((rev pi1)@pi1) ((rev pi1)@pi2)")
apply(simp add: ds_rev_pi_pi)
apply(simp only: ds_cancel_pi_front)
done

lemma ds_acabbc: 
  "\<lbrakk>a\<noteq>b;b\<noteq>c;c\<noteq>a\<rbrakk>\<Longrightarrow>ds [] [(a, c), (a, b), (b, c)] = {a, b}"
apply(simp only: ds_def)
apply(auto)
done

lemma ds_baab: 
  "\<lbrakk>a\<noteq>b\<rbrakk>\<Longrightarrow>ds [] [(b, a), (a, b)] = {}"
apply(simp only: ds_def)
apply(auto)
done

lemma ds_abab: 
  "\<lbrakk>a\<noteq>b\<rbrakk>\<Longrightarrow>ds [] [(a, b), (a, b)] = {}"
apply(simp only: ds_def)
apply(auto)
  done


(* disagreement set as list *)

 
fun flatten :: "(string \<times> string)list \<Rightarrow> string list" where
"flatten []     = []" |
"flatten (x#xs) = (fst x)#(snd x)#(flatten xs)"

definition ds_list :: "(string \<times> string)list \<Rightarrow> (string \<times> string)list \<Rightarrow> string list" where
  ds_list_def: "ds_list pi1 pi2 \<equiv> remdups ([x. x <- (flatten (pi1@pi2)), x\<in>ds pi1 pi2])"


lemma set_flatten_eq_atms: 
  "set (flatten pi) = atms pi"
apply(induct_tac pi)
apply(auto)
done

lemma ds_list_equ_ds: 
  "set (ds_list pi1 pi2) = ds pi1 pi2"
apply(auto)
apply(simp add: ds_list_def)
apply(simp add: ds_list_def)
apply(simp add: set_flatten_eq_atms)
apply(simp add: ds_def)
  done



end