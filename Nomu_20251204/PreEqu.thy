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

lemma teste:
  assumes "\<forall>a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t"
  shows "a \<in> ds [] pi \<Longrightarrow> nabla \<turnstile> a \<sharp> t"
  using bspec assms by simp

  


thm fresh_swap_left fresh_swap_eqvt a_ineq_swapas_pi swapas_pi_in_atms

lemma equ_pi_right: 
  assumes "\<forall>a \<in> ds [] pi. nabla \<turnstile> a \<sharp> t"
  shows "nabla \<turnstile> t \<approx> swap pi t"
  using assms
proof(induct t)
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
    have "nabla \<turnstile> Abst b t' \<approx> Abst c (swap pi t')"
    proof(rule equ_abst_ab)
      show "b \<noteq> c" using neq c_def by blast
      show "nabla \<turnstile> b \<sharp> swap pi t'"sorry
      show "nabla \<turnstile> t' \<approx> swap [(b, c)] (swap pi t')" sorry
      (*proof-
        have "swap [(b, c)] (swap pi t') = swap ([(b,c)]@pi) t'" using swap_append
          by presburger*)
    qed
   then have "nabla \<turnstile> Abst b t' \<approx> swap pi (Abst b t')" using neq c_def by force
      (* ? ? ? *)
  }
  ultimately show ?case by argo

next
  case (Susp pi' X)
  then show ?case sorry
next
  case Unit
  then show ?case sorry
next
  case (Atom b)
  then show ?case sorry
next
  case (Paar t1 t2)
  then show ?case sorry
next
  case (Func f t')
  then have star: "\<forall>a\<in>ds [] pi. nabla \<turnstile> a \<sharp> t'" using fresh_func
    by (metis Fresh_elims(6))
  have "nabla \<turnstile> Func f t' \<approx> Func f (swap pi t')"
    apply(rule equ_func)
    apply(rule Func.hyps)
    using star by auto
  then show ?case
    by simp
qed



(*apply(induct_tac t)
apply(simp_all)
(*Abst*)
apply(force simp add: swapas_comm)
(*Susp*)
apply(rule equ_susp)
apply(rule ballI)
apply(simp only: ds_def)
apply(simp only: mem_Collect_eq)
apply(erule conjE)
apply(subgoal_tac "swapas (pi@[(a,b)]) (swapas list1 c) =
                   swapas ([(swapas pi a,swapas pi b)] @ pi) (swapas list1 c)")
       apply(simp add: swapas_append[THEN sym])
(*A*)
       apply(simp only: swapas_comm)
(*Units*)
apply(rule equ_unit)
(*Atom*)
apply(force dest!: swapas_rev_pi_b swapas_rev_pi_a simp add: swapas_append)
(*Paar*)
apply(force)
(*Func*)
apply(force)
  done
*)

lemma l3_jud: 
  assumes "(nabla \<turnstile> t1\<approx>t2)"
  shows "(nabla \<turnstile> a\<sharp>t1) \<longrightarrow> (nabla \<turnstile> a\<sharp>t2)"
proof(induction)
  case (Abst x1 x2)
  then show ?case using fresh_abst_aa fresh_abst_ab by metis
next
  case (Susp x1 x2)
  then show ?case sorry
next
  case Unit
  then show ?case using equ_unit by auto
next
  case (Atom x)
  then show ?case sorry
next
  case (Paar x1 x2)
  then show ?case by force
next
  case (Func x1 x2)
  then show ?case by force
qed

(*apply(rule equ.induct)
apply(simp_all)
(*Abst.ab*)
apply(case_tac "aa=a")
apply(force)
apply(case_tac "b=a")
apply(force)
      apply(force dest!: Fresh_elims(1) fresh_swap_left)
(*Abst.aa*)
apply(case_tac "a=aa")
apply(force)
apply(force dest!: Fresh_elims(1))
(*Susp*)
apply(rule impI)
    apply(drule Fresh_elims(4), rule fresh_susp)
apply(case_tac "swapas (rev pi1) a = swapas (rev pi2) a") 
apply(simp)
     apply(drule_tac x="swapas (rev pi2) a" in bspec)


      apply(rule ds_cancel_pi_left)

  apply(subgoal_tac "swapas (pi1@(rev pi2)) a \<noteq> a")--A
      apply(drule ds_elem)

      apply(force simp add: ds_def swapas_append)

(*A*)
      apply(clarify)

      apply(simp only: swapas_append)

      apply(drule swapas_rev_pi_a)

      apply(force)

      apply(assumption)

(*Paar*)
apply(force dest!: fresh_paar_elim)
(*Func*)
apply(force dest!: fresh_func_elim)
  done*)


lemma big: "\<forall>t1 t2 t3. (n=depth t1) \<longrightarrow>
             (((nabla\<turnstile>t1\<approx>t2)\<longrightarrow>(nabla\<turnstile>t2\<approx>t1))\<and>  
              (\<forall>pi. (nabla\<turnstile>t1\<approx>t2)\<longrightarrow>(nabla\<turnstile>swap pi t1\<approx>swap pi t2))\<and> 
              ((nabla\<turnstile>t1\<approx>t2)\<and>(nabla\<turnstile>t2\<approx>t3)\<longrightarrow>(nabla\<turnstile>t1\<approx>t3)))"

  sorry
(*apply(induct_tac n rule: nat_less_induct)
apply(rule allI)+apply(rule impI)
apply(rule conjI)
(*SYMMETRY*)
apply(rule impI)
apply(ind_cases "nabla \<turnstile> t1 \<approx> t2")
apply(simp_all)
(*Abst.ab*)
apply(rule equ_abst_ab)
apply(force) --abst.ab.first.premise
apply(rule_tac "t1.1"="swap [(a,b)] t2a" in l3_jud[THEN mp])
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(rule fresh_swap_right[THEN mp])
apply(simp) --abst.ab.second.premise
apply(subgoal_tac "nabla \<turnstile> swap [(b, a)] t1a \<approx> t2a")
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(subgoal_tac "nabla \<turnstile> swap [(b,a)] t1a \<approx> swap ([(b,a)]@[(a,b)]) t2a") --A
apply(subgoal_tac "nabla \<turnstile> swap ([(b,a)]@[(a,b)]) t2a \<approx> t2a") --B
apply(drule_tac x="depth t1a" in spec)
apply(simp (no_asm_use))
apply(drule_tac x="swap [(b,a)] t1a" in spec)
apply(simp (no_asm_use))
apply(drule_tac x="swap [(b,a),(a,b)] t2a" in spec)
apply(force)
(*B*)
apply(subgoal_tac "nabla\<turnstile>t2a \<approx> swap ([(b, a)] @ [(a, b)]) t2a")--C
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="t2a" in spec)
apply(drule mp)
apply(drule equ_depth)
apply(force)
apply(best)
(*C*)
apply(rule equ_pi_right[THEN spec,THEN mp])
apply(subgoal_tac "ds [] ([(b, a)] @ [(a, b)])={}")
apply(simp)
apply(simp add: ds_baab)
(*A*)
apply(force simp only: swap_append)
(*Abst.aa*)
apply(force)
(*Unit*)
apply(rule equ_unit)
(*Atom*)
apply(force)
(*Susp*)
apply(force simp only: ds_sym)
(*Paar*)
apply(rule equ_paar)
apply(drule_tac x="depth t1a" in spec)
apply(simp add: Suc_max_left)
apply(drule_tac x="depth s1" in spec)
apply(simp add: Suc_max_right)
(*Func*)
apply(best)
(*ADD.PI*)
apply(rule conjI)
apply(rule impI)
apply(ind_cases "nabla \<turnstile> t1 \<approx> t2")
apply(simp_all)
(*Abst.ab*)
apply(rule allI)
apply(rule equ_abst_ab)
(* abst.ab.first.premise*)
apply(clarify)
apply(drule swapas_rev_pi_a)
apply(simp)
(*abst.ab.second.premise*)
apply(rule fresh_swap_right[THEN mp])
apply(simp)
(*abst.ab.third.premise*)
apply(subgoal_tac "nabla \<turnstile> swap pi t1a \<approx> swap (pi@[(a,b)]) t2a") --A
apply(subgoal_tac "nabla \<turnstile> swap (pi@[(a,b)]) t2a \<approx> swap ([(swapas pi a,swapas pi b)]@pi) t2a") --B
apply(drule_tac x="depth t1a" in spec)
apply(simp (no_asm_use))
apply(drule_tac x="swap pi t1a" in spec)
apply(simp (no_asm_use)) 
apply(drule_tac x="swap (pi@[(a,b)]) t2a" in spec)
apply(drule conjunct2)+
apply(drule_tac x="swap ((swapas pi a, swapas pi b) # pi) t2a" in spec)
apply(simp add: swap_append[THEN sym])
--B
apply(rule pi_comm)
apply(force simp only: swap_append)
-- A
apply(force simp only: swap_append)
-- Unit
apply(rule equ_unit)
-- Atom
apply(force)
-- Susp
apply(force simp only: ds_cancel_pi_front)
-- Paar
apply(rule allI)
apply(rule equ_paar)
apply(drule_tac x="depth t1a" in spec)
apply(simp only: Suc_max_left)
apply(drule_tac x="depth s1" in spec)
apply(simp only: Suc_max_right)
-- Func
apply(best)
-- TRANSITIVITY
apply(rule impI)
apply(erule conjE)
apply(ind_cases "nabla \<turnstile> t1 \<approx> t2")
apply(simp_all)
-- Abst.ab
apply(ind_cases "nabla \<turnstile> Abst b t2a \<approx> t3")
apply(simp)
apply(case_tac "ba=a")
apply(simp)
apply(rule equ_abst_aa)
apply(subgoal_tac "nabla\<turnstile>swap [(a,b)] t2a \<approx> t2b") --A
apply(best)
--A
apply(subgoal_tac "nabla\<turnstile>swap [(a,b)] t2a\<approx> swap ([(a,b)]@[(b,a)]) t2b") --B
apply(subgoal_tac "nabla\<turnstile>swap ([(a,b)]@[(b,a)]) t2b \<approx> t2b") --C
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="swap [(a,b)] t2a" in spec)
apply(drule equ_depth)
apply(simp (no_asm_use))
apply(best)
--C
apply(subgoal_tac "nabla\<turnstile>t2b \<approx> swap ([(a,b)]@[(b,a)]) t2b")--D
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="t2b" in spec)
apply(drule mp)
apply(force dest!: equ_depth)
apply(best)
--D
apply(rule equ_pi_right[THEN spec, THEN mp])
apply(simp add: ds_baab)
--B
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="t2a" in spec)
apply(drule equ_depth)
apply(simp) 
apply(drule_tac x="swap [(b, a)] t2b" in spec)
apply(drule conjunct2)
apply(drule conjunct1)
apply(simp)
apply(drule_tac x="[(a,b)]" in spec)
apply(simp add: swap_append[THEN sym])
-- Abst.ab
apply(rule equ_abst_ab)
-- abst.ab.first.premise
apply(force)
-- abst.ab.second.premise
apply(rule_tac "t1.1"="swap [(b,ba)] t2a" in l3_jud[THEN mp])
apply(subgoal_tac "nabla \<turnstile> swap [(b,ba)] t2a \<approx> swap ([(b,ba)]@[(b, ba)]) t2b") --A
apply(subgoal_tac "nabla\<turnstile>swap ([(b,ba)]@[(b,ba)]) t2b \<approx> t2b") --B
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="swap [(b, ba)] t2a" in spec)
apply(drule mp)
apply(force dest!: equ_depth)
apply(best)
--B
apply(subgoal_tac "nabla\<turnstile>t2b \<approx> swap ([(b,ba)] @ [(b,ba)]) t2b")--C
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="t2b" in spec)
apply(drule mp)
apply(force dest!: equ_depth)
apply(best)
-- C
apply(rule equ_pi_right[THEN spec, THEN mp])
apply(simp add: ds_abab)
--A
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="t2a" in spec)
apply(drule mp)
apply(force dest!: equ_depth)
apply(drule_tac x="swap [(b,ba)] t2b" in spec)
apply(drule conjunct2)
apply(drule conjunct1)
apply(simp)
apply(drule_tac x="[(b,ba)]" in spec)
apply(simp add: swap_append[THEN sym])
-- abst.ab.third.premise
apply(force intro!: fresh_swap_right[THEN mp])
-- very.complex
apply(subgoal_tac "nabla\<turnstile>t1a \<approx> swap ([(a,b)]@[(b,ba)]) t2b") --A
apply(subgoal_tac "nabla\<turnstile>swap ([(a,b)]@[(b,ba)]) t2b \<approx> swap [(a,ba)] t2b") --B
apply(drule_tac x="depth t1a" in spec)
apply(simp (no_asm_use))
apply(best)
--B
apply(subgoal_tac "nabla\<turnstile>swap [(a, ba)] t2b \<approx> swap [(a,b),(b,ba)] t2b")--C
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="swap [(a, ba)] t2b" in spec)
apply(drule mp)
apply(force dest!: equ_depth)
apply(force)
apply(subgoal_tac "nabla\<turnstile>swap [(a,ba)] t2b\<approx> swap [(a,ba)] (swap [(a,ba),(a,b),(b,ba)] t2b)") --D
apply(subgoal_tac "nabla\<turnstile>swap (rev [(a,ba)]) (swap [(a,ba)] (swap [(a,b),(b,ba)] t2b)) 
                        \<approx>swap [(a,b),(b,ba)] t2b") --E
apply(simp add: swap_append[THEN sym])
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="swap [(a,ba)] t2b" in spec)
apply(drule mp)
apply(force dest!: equ_depth)
apply(drule_tac x="swap [(a, ba), (a, ba), (a, b), (b, ba)] t2b" in spec)
apply(drule conjunct2)+
apply(best)
-- D
apply(rule rev_pi_pi_equ)
-- E
apply(subgoal_tac "nabla\<turnstile>t2b\<approx>swap [(a, ba), (a, b), (b, ba)] t2b") --F
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="t2b" in spec)
apply(drule mp)
apply(force dest!: equ_depth)
apply(best)
--F
apply(rule equ_pi_right[THEN spec, THEN mp])
apply(subgoal_tac "ds [] [(a,ba),(a,b),(b,ba)]={a,b}") -- G
apply(simp)
apply(drule_tac "t1.1"="t2a" and "t2.1"="swap [(b, ba)] t2b" and a1="a" in l3_jud[THEN mp])
apply(assumption)
apply(subgoal_tac "nabla \<turnstile> swapas (rev [(b,ba)]) a \<sharp> t2b") --H
apply(simp)
apply(case_tac "b=a")
apply(force)
apply(force)
--H
apply(rule fresh_swap_left[THEN mp])
apply(assumption)
--G
apply(rule ds_acabbc)
apply(assumption)+
--A
apply(subgoal_tac "nabla\<turnstile>swap [(a,b)] t2a\<approx>swap [(a,b)] (swap [(b,ba)] t2b)")--I
apply(drule_tac x="depth t1a" in spec)
apply(simp (no_asm_use))
apply(drule_tac x="t1a" in spec)
apply(simp (no_asm_use))
apply(drule_tac x="swap [(a,b)] t2a" in spec)
apply(drule conjunct2)+
apply(drule_tac x="swap [(a, b)] (swap [(b, ba)] t2b)" in spec)
apply(force simp add: swap_append[THEN sym])
--I 
apply(drule_tac x="depth t1a" in spec)
apply(simp (no_asm_use))
apply(drule_tac x="t2a" in spec)
apply(drule mp)
apply(force dest!: equ_depth)
apply(drule_tac x="swap [(b,ba)] t2b" in spec)
apply(best)
-- Abst.ab
apply(simp)
apply(rule equ_abst_ab)
apply(assumption)
apply(drule_tac "t1.1"="t2a" and "t2.1"="t2b" and a1="a" in l3_jud[THEN mp])
apply(assumption)+
apply(subgoal_tac "nabla\<turnstile>swap [(a, b)] t2a\<approx>swap [(a, b)] t2b") --A
apply(best)
--A
apply(drule_tac x="depth t1a" in spec)
apply(simp (no_asm_use))
apply(drule_tac x="t2a" in spec)
apply(drule mp)
apply(force dest!: equ_depth)
apply(drule_tac x="t2b" in spec)
apply(best)
-- Abst
apply(ind_cases "nabla \<turnstile> Abst a t2a \<approx> t3")
apply(best)
apply(best)
-- Susp
apply(ind_cases "nabla \<turnstile> Susp pi2 X \<approx> t3")
apply(simp)
apply(rule equ_susp)
apply(rule ballI)
apply(drule_tac "pi2.1"="pi2" in ds_trans[THEN mp])
apply(force)
-- Paar
apply(ind_cases "nabla \<turnstile> Paar t2a s2 \<approx> t3")
apply(simp)
apply(rule equ_paar)
apply(drule_tac x="depth t1a" in spec)
apply(simp (no_asm_use) add: Suc_max_left)
apply(best)
apply(drule_tac x="depth s1" in spec)
apply(simp (no_asm_use) add: Suc_max_right)
apply(best)
-- Func
apply(ind_cases "nabla \<turnstile> Func F t2a \<approx> t3")
apply(best)
done*)

lemma pi_right_equ_help:
      "\<forall>t. (n=depth t) \<longrightarrow> (\<forall>pi. nabla\<turnstile>t\<approx>swap pi t\<longrightarrow>(\<forall>a\<in> ds [] pi. nabla\<turnstile>a\<sharp>t))"
apply(induct n rule: nat_less_induct)
apply(rule allI)+
apply(rule impI)
apply(rule allI)+
apply(rule impI)
apply(ind_cases "nabla \<turnstile> t \<approx> swap pi t")
apply(simp_all)
--Abst.ab
apply(rule ballI)
apply(case_tac "aa=a")
apply(force)
apply(rule fresh_abst_ab)
apply(case_tac "aa=swapas (rev pi) a")
apply(simp)
apply(drule fresh_swap_left[THEN mp])
apply(assumption)
apply(drule_tac x="depth t1" in spec)
apply(simp)
apply(drule_tac x="t1" in spec)
apply(simp add: swap_append[THEN sym])
apply(drule_tac x="[(a, swapas pi a)] @ pi" in spec)
apply(simp)
apply(case_tac "aa=swapas pi a")
apply(simp)
apply(drule_tac x="swapas pi a" in bspec)
apply(simp (no_asm) only: ds_def)
apply(simp only: mem_Collect_eq)
apply(rule conjI)
apply(simp)
apply(simp)
apply(rule impI)
apply(clarify)
apply(drule sym)
apply(drule swapas_rev_pi_a)
apply(force)
apply(assumption)
apply(drule_tac x="aa" in bspec)
apply(subgoal_tac "\<forall>A. aa\<in>A-{swapas pi a} \<and> aa\<noteq>swapas pi a \<longrightarrow>aa\<in>A")--A
apply(drule_tac x="ds [] ((a,swapas pi a) # pi)" in spec)
apply(simp add: ds_equality[THEN sym])
--A
apply(force)
apply(assumption)+
--Abst.aa
apply(rule ballI)
apply(case_tac "aa=a")
apply(force)
apply(best)
--Unit
apply(force)
--Atom
apply(force simp add: ds_def)
--Susp
apply(rule ballI)
apply(rule fresh_susp)
apply(drule_tac x="swapas (rev pi1) a" in bspec)
apply(rule ds_cancel_pi_right[of _ _ "[]" _, simplified, THEN mp])
apply(simp)
apply(assumption)
--Paar
apply(rule ballI)
apply(rule fresh_paar)
apply(drule_tac x="depth t1" in spec)
apply(force simp add: Suc_max_left)
apply(drule_tac x="depth s1" in spec)
apply(force simp add: Suc_max_right)
--Func
apply(best)
done*)

end 
