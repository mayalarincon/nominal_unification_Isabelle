
theory Atoms 

imports Main Swap Terms

begin

fun atms :: "(string \<times> string) list \<Rightarrow> string set" where
"atms [] = {}" | 
"atms (x#xs) = ((atms xs) \<union>  {fst(x),snd(x)})"


lemma [simp]: 
  "atms (xs@ys) = atms xs \<union> atms ys"
  by (induct xs) auto


lemma [simp]: 
  "atms (rev pi) = atms pi"
  by (induct pi) auto


lemma a_not_in_atms: 
  assumes "a \<notin> atms pi"
  shows "a = swapas pi a"
  using assms by (induct pi) auto


lemma swapas_pi_ineq_a: 
  "swapas pi a \<noteq> a \<longrightarrow> a \<in> atms pi"
  using a_not_in_atms by metis


lemma a_ineq_swapas_pi: 
  "a \<noteq> swapas pi a \<longrightarrow> a \<in> atms pi"
  using a_not_in_atms by metis


lemma swapas_pi_in_atms: 
  assumes "a \<in> atms pi" 
  shows"swapas pi a \<in> atms pi"
  using assms by (metis a_not_in_atms swapas_rev_pi_a)


end