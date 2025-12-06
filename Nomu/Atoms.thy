
theory Atoms = Main + Swap + Terms:

consts atms   :: "(string \<times> string) list \<Rightarrow> string set"
primrec
"atms [] = {}"
"atms (x#xs) = ((atms xs) \<union>  {fst(x),snd(x)})"

lemma [simp]: 
  "atms (xs@ys) = atms xs \<union> atms ys"
apply(induct_tac xs, auto)
done

lemma [simp]: 
  "atms (rev pi) = atms pi"
apply(induct_tac pi, simp_all)
done

lemma a_not_in_atms: 
  "a\<notin>atms pi \<longrightarrow> a = swapas pi a" 
apply(induct_tac pi, auto)
done

lemma swapas_pi_ineq_a: 
  "swapas pi a \<noteq> a \<longrightarrow> a\<in>atms pi"
apply(case_tac "a\<in>atms pi")
apply(simp)+
apply(drule a_not_in_atms[THEN mp])
apply(simp)
done

lemma a_ineq_swapas_pi: 
  "a \<noteq> swapas pi a \<longrightarrow> a\<in>atms pi"
apply(case_tac "a\<in>atms pi")
apply(simp_all add: a_not_in_atms)
done

lemma swapas_pi_in_atms[THEN mp]: 
  "a\<in>atms pi \<longrightarrow> swapas pi a\<in>atms pi"
apply(subgoal_tac "\<forall>pi1. (a\<in>atms pi1) \<longrightarrow> swapas pi a\<in>(atms pi1 \<union> atms pi)")
apply(force)
apply(induct_tac pi)
apply(auto)
done

end