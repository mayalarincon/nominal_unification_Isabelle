
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
  using ds_def swapas_pi_ineq_a by simp


corollary ds_elem_cp: "a \<notin> ds [] pi \<Longrightarrow> swapas pi a = a"
  using ds_elem by blast

lemma 
  elem_ds: "\<lbrakk>a\<in>ds [] pi\<rbrakk>\<Longrightarrow>a\<noteq>swapas pi a"
  using ds_def by simp


lemma 
  ds_sym: "ds pi1 pi2 = ds pi2 pi1"
  using ds_def by auto


lemma 
  ds_trans: "c \<in> ds pi1 pi3 \<Longrightarrow> (c \<in> ds pi1 pi2 \<or> c \<in> ds pi2 pi3)"
using ds_def a_not_in_atms swapas_pi_ineq_a by auto



lemma ds_cancel_pi_left:
  assumes "(c\<in> ds (pi1@pi) (pi2@pi))"
  shows "(swapas pi c \<in> ds pi1 pi2)"
  using assms ds_def swapas_append a_ineq_swapas_pi a_not_in_atms
  by (metis (mono_tags, lifting) Un_iff mem_Collect_eq)



lemma ds_cancel_pi_right: 
  "(swapas pi c\<in> ds pi1 pi2) \<Longrightarrow> (c\<in> ds (pi1@pi) (pi2@pi))"
apply(simp only: ds_def)
apply(auto)
apply(simp_all add: swapas_append)
apply(rule a_ineq_swapas_pi,clarify,
      drule a_not_in_atms,drule a_not_in_atms,simp)+
  done



lemma ds_equality: 
  "(ds [] pi)-{a,swapas pi a} = (ds [] ((a,swapas pi a)#pi))-{swapas pi a}"
  using ds_def by auto


lemma ds_7: 
  "\<lbrakk>b\<noteq> swapas pi b;a\<in>ds [] ((b,swapas pi b)#pi)\<rbrakk>\<Longrightarrow>a\<in>ds [] pi"
  using ds_def swapas_pi_in_atms a_ineq_swapas_pi swapas_rev_pi_a 
    ds_elem elem_ds swapa.simps swapas.simps(2)
  by metis



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
  using ds_cancel_pi_front ds_rev_pi_pi by blast

lemma ds_acabbc: 
  "\<lbrakk>a\<noteq>b;b\<noteq>c;c\<noteq>a\<rbrakk>\<Longrightarrow>ds [(a, b), (b, c)] [(a, c)] = {a, b}"
  using ds_def by auto

lemma ds_baab: 
  "\<lbrakk>a\<noteq>b\<rbrakk>\<Longrightarrow>ds [(b,a)] [(a, b)] = {}"
  using ds_def by auto

lemma ds_baab_id: 
"\<lbrakk>a\<noteq>b\<rbrakk>\<Longrightarrow>ds ([(b,a)]@[(a, b)]) [] = {}"
  using ds_def ds_rev ds_baab by simp

lemma ds_abab: 
  "\<lbrakk>a\<noteq>b\<rbrakk>\<Longrightarrow>ds [] [(a, b), (a, b)] = {}"
  using ds_def by auto

lemma ds_comm:
"ds (pi @ [(a,b)]) ([(swapas pi a, swapas pi b)] @ pi) = {}"
  using swapas_comm ds_def by simp

lemma ds_rev_pi_id:
"ds (rev pi @ pi) [] = {}"
  using ds_rev_pi_pi[of pi \<open>[]\<close>] elem_ds
    ds_sym[of \<open>(rev pi @ pi)\<close> \<open>[]\<close>] by fastforce

lemma ds_pi_rev_id:
"ds (pi @ rev pi) [] = {}"
  using ds_rev_pi_id[of \<open>rev pi\<close>] rev_rev_ident[of pi]
  by simp

lemma ds_swapas_eq:
"ds pi1 pi2 = {} \<Longrightarrow> swapas pi1 a = swapas pi2 a"
  using ds_elem[of \<open>rev pi1 @ pi2\<close>] ds_rev[of pi1 pi2] 
  empty_iff[of a] swapas_append[of \<open>rev pi1\<close> pi2 a] swapas_inv by metis


(* disagreement set as list *)

 
fun flatten :: "(string \<times> string)list \<Rightarrow> string list" where
"flatten []     = []" |
"flatten (x#xs) = (fst x)#(snd x)#(flatten xs)"

definition ds_list :: "(string \<times> string)list \<Rightarrow> (string \<times> string)list \<Rightarrow> string list" where
  ds_list_def: "ds_list pi1 pi2 \<equiv> remdups ([x. x <- (flatten (pi1@pi2)), x\<in>ds pi1 pi2])"


lemma set_flatten_eq_atms: 
  "set (flatten pi) = atms pi"
  by (induct pi) auto

lemma ds_list_equ_ds: 
  "set (ds_list pi1 pi2) = ds pi1 pi2"
  using ds_list_def ds_def set_flatten_eq_atms by auto



end