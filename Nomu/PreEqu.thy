

theory PreEqu = Main + Swap + Terms + Disagreement + Fresh:

consts 
  equ :: "(fresh_envs \<times> trm \<times> trm) set"

syntax 
  "_equ_judge"   :: "fresh_envs \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" (" _ \<turnstile> _ \<approx> _" [80,80,80] 80)
translations 
  "nabla \<turnstile> t1 \<approx> t2" \<rightleftharpoons> "(nabla,t1,t2) \<in> equ"

inductive equ 
intros
equ_abst_ab[intro!]: "\<lbrakk>a\<noteq>b;(nabla \<turnstile> a \<sharp> t2);(nabla \<turnstile> t1 \<approx> (swap [(a,b)] t2))\<rbrakk> 
                      \<Longrightarrow> (nabla \<turnstile> Abst a t1 \<approx> Abst b t2)"
equ_abst_aa[intro!]: "(nabla \<turnstile> t1 \<approx> t2) \<Longrightarrow> (nabla \<turnstile> Abst a t1 \<approx> Abst a t2)" 
equ_unit[intro!]:    "(nabla \<turnstile> Unit \<approx> Unit)"
equ_atom[intro!]:    "a=b\<Longrightarrow>nabla \<turnstile> Atom a \<approx> Atom b"
equ_susp[intro!]:    "(\<forall> c \<in> ds pi1 pi2. (c,X) \<in> nabla) \<Longrightarrow> (nabla \<turnstile> Susp pi1 X \<approx> Susp pi2 X)"
equ_paar[intro!]:    "\<lbrakk>(nabla \<turnstile> t1\<approx>t2);(nabla \<turnstile> s1\<approx>s2)\<rbrakk> \<Longrightarrow> (nabla \<turnstile> Paar t1 s1 \<approx> Paar t2 s2)"
equ_func[intro!]:    "(nabla \<turnstile> t1 \<approx> t2) \<Longrightarrow> (nabla \<turnstile> Func F t1 \<approx> Func F t2)" 

lemma equ_atom_elim[elim!]: "nabla\<turnstile>Atom a \<approx> Atom b \<Longrightarrow> a=b"
apply(ind_cases "nabla \<turnstile> Atom a \<approx> Atom b", auto)
done

lemma equ_susp_elim[elim!]: "(nabla \<turnstile> Susp pi1 X \<approx> Susp pi2 X) 
                             \<Longrightarrow> (\<forall> c \<in> ds pi1 pi2. (c,X)\<in> nabla)"
apply(ind_cases "nabla \<turnstile> Susp pi1 X \<approx> Susp pi2 X", auto)
done
lemma equ_paar_elim[elim!]: "(nabla \<turnstile> Paar s1 t1 \<approx> Paar s2 t2) \<Longrightarrow> 
                             (nabla \<turnstile> s1 \<approx> s2)\<and>(nabla \<turnstile> t1 \<approx> t2)"
apply(ind_cases "nabla \<turnstile> Paar s1 t1 \<approx> Paar s2 t2", auto)
done
lemma equ_func_elim[elim!]: "(nabla \<turnstile> Func F t1 \<approx> Func F t2) \<Longrightarrow> (nabla \<turnstile> t1 \<approx> t2)"
apply(ind_cases "nabla \<turnstile> Func F t1 \<approx> Func F t2", auto)
done
lemma equ_abst_aa_elim[elim!]: "(nabla \<turnstile> Abst a t1 \<approx> Abst a t2) \<Longrightarrow> (nabla \<turnstile> t1 \<approx> t2)"
apply(ind_cases "nabla \<turnstile> Abst a t1 \<approx> Abst a t2", auto)
done
lemma equ_abst_ab_elim[elim!]: "\<lbrakk>(nabla \<turnstile> Abst a t1 \<approx> Abst b t2);a\<noteq>b\<rbrakk> \<Longrightarrow> 
                                (nabla \<turnstile> t1 \<approx> (swap [(a,b)] t2))\<and>(nabla\<turnstile>a\<sharp>t2)"
apply(ind_cases "(nabla \<turnstile> Abst a t1 \<approx> Abst b t2)", auto)
done

lemma equ_depth: "nabla \<turnstile> t1 \<approx> t2 \<Longrightarrow> depth t1 = depth t2"
apply(erule equ.induct)
apply(simp_all)
done

lemma rev_pi_pi_equ: "(nabla\<turnstile>swap (rev pi) (swap pi t)\<approx>t)"
apply(induct_tac t)
apply(auto)
-- Susp
apply(drule_tac ds_cancel_pi_left[of _ "rev pi @ pi" _ "[]", THEN mp, simplified])
apply(simp only: ds_rev_pi_pi)
apply(simp only: ds_def)
apply(force)
done

lemma equ_pi_right: "\<forall>pi. (\<forall>a\<in>ds [] pi. nabla\<turnstile>a\<sharp>t) \<longrightarrow> (nabla\<turnstile>t\<approx>swap pi t)"
apply(induct_tac t)
apply(simp_all)
-- Abst
apply(rule allI)
apply(case_tac "(swapas pi list)=list") 
apply(simp)
apply(rule impI)
apply(rule equ_abst_aa)
apply(drule_tac x="pi" in spec)
apply(subgoal_tac "(\<forall>a\<in>ds [] pi.  nabla \<turnstile> a \<sharp> trm)")--A
apply(force)
--A
apply(rule ballI)
apply(drule_tac x=a in bspec)
apply(assumption)
apply(case_tac "list\<noteq>a")
apply(force dest!: fresh_abst_ab_elim)
apply(simp add: ds_def)
apply(rule impI)
apply(rule equ_abst_ab)
apply(force)
apply(drule_tac x="swapas (rev pi) list" in bspec)
apply(simp add: ds_def)
apply(rule conjI)
apply(subgoal_tac "swapas (rev pi) list \<in> atms (rev pi)") --B
apply(simp)
--B
apply(drule swapas_pi_ineq_a[THEN mp])
apply(rule swapas_pi_in_atms)
apply(simp)
apply(clarify)
apply(drule swapas_rev_pi_b)
apply(simp)
apply(force dest!: fresh_abst_ab_elim  swapas_rev_pi_b intro!: fresh_swap_right[THEN mp])
apply(drule_tac x="(list, swapas pi list)#pi" in spec)
apply(subgoal_tac "(\<forall>a\<in>ds [] ((list, swapas pi list) # pi).  nabla \<turnstile> a \<sharp> trm)")--C
apply(force simp add: swap_append[THEN sym])
--C
apply(rule ballI)
apply(drule_tac x="a" in bspec)
apply(rule_tac b="list" in ds_7)
apply(force)
apply(assumption)
apply(case_tac "list=a")
apply(simp)
apply(simp only: ds_def mem_Collect_eq)
apply(erule conjE)
apply(subgoal_tac "a\<noteq>swapas pi a")
apply(simp)
apply(force)
apply(force dest!: fresh_abst_ab_elim)
-- Susp
apply(rule allI)
apply(rule impI)
apply(rule equ_susp)
apply(rule ballI)
apply(subgoal_tac "swapas list1 c\<in>ds [] pi")--A
apply(force dest!: fresh_susp_elim)
--A
apply(rule ds_cancel_pi_left[THEN mp])
apply(simp)
-- Unit
apply(force)
-- Atom
apply(rule allI)
apply(rule impI)
apply(case_tac "(swapas pi list) = list")
apply(force)
apply(drule ds_elem)
apply(force dest!: fresh_atom_elim)
-- Paar
apply(force dest!: fresh_paar_elim)
-- Func
apply(force)
done

lemma pi_comm: "nabla\<turnstile>(swap (pi@[(a,b)]) t)\<approx>(swap ([(swapas pi a, swapas pi b)]@pi) t)"
apply(induct_tac t)
apply(simp_all)
-- Abst
apply(force simp add: swapas_comm)
-- Susp
apply(rule equ_susp)
apply(rule ballI)
apply(simp only: ds_def)
apply(simp only: mem_Collect_eq)
apply(erule conjE)
apply(subgoal_tac "swapas (pi@[(a,b)]) (swapas list1 c) =
                   swapas ([(swapas pi a,swapas pi b)]@pi) (swapas list1 c)")--A
apply(simp add: swapas_append[THEN sym])
--A
apply(simp only: swapas_comm)
-- Units
apply(rule equ_unit)
-- Atom
apply(force dest!: swapas_rev_pi_b swapas_rev_pi_a simp add: swapas_append)
--Paar
apply(force)
--Func
apply(force)
done


lemma l3_jud: "(nabla \<turnstile> t1\<approx>t2) \<Longrightarrow> (nabla \<turnstile> a\<sharp>t1) \<longrightarrow> (nabla \<turnstile> a\<sharp>t2)"
apply(erule equ.induct)
apply(simp_all)
--Abst.ab
apply(rule impI)
apply(case_tac "aa=a")
apply(force)
apply(case_tac "b=a")
apply(force)
apply(force dest!: fresh_abst_ab_elim fresh_swap_left[THEN mp])
-- Abst.aa
apply(case_tac "a=aa")
apply(force)
apply(force dest!: fresh_abst_ab_elim)
-- Susp
apply(rule impI)
apply(drule fresh_susp_elim, rule fresh_susp)
apply(case_tac "swapas (rev pi1) a = swapas (rev pi2) a") 
apply(simp)
apply(drule_tac x="swapas (rev pi2) a" in bspec)
apply(rule ds_cancel_pi_left[THEN mp])
apply(subgoal_tac "swapas (pi1@(rev pi2)) a \<noteq> a")--A
apply(drule ds_elem)
apply(force simp add: ds_def swapas_append)
--A
apply(clarify)
apply(simp only: swapas_append)
apply(drule swapas_rev_pi_a)
apply(force)
apply(assumption)
-- Paar
apply(force dest!: fresh_paar_elim)
-- Func
apply(force dest!: fresh_func_elim)
done

lemma big: "\<forall>t1 t2 t3. (n=depth t1) \<longrightarrow>
             (((nabla\<turnstile>t1\<approx>t2)\<longrightarrow>(nabla\<turnstile>t2\<approx>t1))\<and>  
              (\<forall>pi. (nabla\<turnstile>t1\<approx>t2)\<longrightarrow>(nabla\<turnstile>swap pi t1\<approx>swap pi t2))\<and> 
              ((nabla\<turnstile>t1\<approx>t2)\<and>(nabla\<turnstile>t2\<approx>t3)\<longrightarrow>(nabla\<turnstile>t1\<approx>t3)))" 
apply(induct_tac n rule: nat_less_induct)
apply(rule allI)+apply(rule impI)
apply(rule conjI)
-- SYMMETRY
apply(rule impI)
apply(ind_cases "nabla \<turnstile> t1 \<approx> t2")
apply(simp_all)
-- Abst.ab
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
--B
apply(subgoal_tac "nabla\<turnstile>t2a \<approx> swap ([(b, a)] @ [(a, b)]) t2a")--C
apply(drule_tac x="depth t1a" in spec)
apply(simp)
apply(drule_tac x="t2a" in spec)
apply(drule mp)
apply(drule equ_depth)
apply(force)
apply(best)
--C
apply(rule equ_pi_right[THEN spec,THEN mp])
apply(subgoal_tac "ds [] ([(b, a)] @ [(a, b)])={}")
apply(simp)
apply(simp add: ds_baab)
--A
apply(force simp only: swap_append)
-- Abst.aa
apply(force)
-- Unit
apply(rule equ_unit)
-- Atom
apply(force)
-- Susp
apply(force simp only: ds_sym)
-- Paar
apply(rule equ_paar)
apply(drule_tac x="depth t1a" in spec)
apply(simp add: Suc_max_left)
apply(drule_tac x="depth s1" in spec)
apply(simp add: Suc_max_right)
-- Func
apply(best)
-- ADD.PI
apply(rule conjI)
apply(rule impI)
apply(ind_cases "nabla \<turnstile> t1 \<approx> t2")
apply(simp_all)
-- Abst.ab
apply(rule allI)
apply(rule equ_abst_ab)
-- abst.ab.first.premise
apply(clarify)
apply(drule swapas_rev_pi_a)
apply(simp)
-- abst.ab.second.premise
apply(rule fresh_swap_right[THEN mp])
apply(simp)
-- abst.ab.third.premise
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
done

lemma pi_right_equ_help: 
      "\<forall>t. (n=depth t) \<longrightarrow> (\<forall>pi. nabla\<turnstile>t\<approx>swap pi t\<longrightarrow>(\<forall>a\<in> ds [] pi. nabla\<turnstile>a\<sharp>t))"
apply(induct_tac n rule: nat_less_induct)
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
done

end 
