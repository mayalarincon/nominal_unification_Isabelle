theory Fresh

imports Main Swap Terms Disagreement

begin

type_synonym fresh_envs = "(string \<times> string) set"


(*locale test3 =
  fixes fresh :: "(fresh_envs \<times> string \<times> trm) set"

begin *)

(*abbreviation "fresh_judge nabla a t fresh \<equiv> (nabla,a,t) \<in> fresh" 

notation "fresh_judge" (" _ \<turnstile> _ \<sharp> _" [80,80,80] 80) *)

(*syntax 
  "_fresh_judge" :: "fresh_envs \<Rightarrow> string \<Rightarrow> trm \<Rightarrow> bool" (" _ \<turnstile> _ \<sharp> _" [80,80,80] 80)
translations
  "nabla \<turnstile> a \<sharp> t"  \<rightleftharpoons> "(nabla,a,t) \<in> fresh"*)

inductive fresh :: "fresh_envs \<Rightarrow> string \<Rightarrow> trm \<Rightarrow> bool" (" _ \<turnstile> _ \<sharp> _" [80,80,80] 80) where
  fresh_abst_ab[intro!]: "\<lbrakk>(nabla\<turnstile>a\<sharp>t); a\<noteq>b\<rbrakk> \<Longrightarrow> (nabla\<turnstile>a\<sharp>Abst b t)" |
  fresh_abst_aa[intro!]: "(nabla\<turnstile>a\<sharp>Abst a t)" |
  fresh_unit[intro!]:    "(nabla\<turnstile>a\<sharp>Unit)" |
  fresh_atom[intro!]:    "a\<noteq>b \<Longrightarrow> (nabla\<turnstile>a\<sharp>Atom b)" |
  fresh_susp[intro!]:    "(swapas (rev pi) a,X)\<in>nabla \<Longrightarrow> (nabla\<turnstile>a\<sharp>Susp pi X)" |
  fresh_paar[intro!]:    "\<lbrakk>(nabla\<turnstile>a\<sharp>t1);(nabla\<turnstile>a\<sharp>t2)\<rbrakk> \<Longrightarrow> (nabla\<turnstile>a\<sharp>Paar t1 t2)" |
  fresh_func[intro!]:    "(nabla\<turnstile>a\<sharp>t) \<Longrightarrow> (nabla\<turnstile>a\<sharp>Func F t)"

lemma fresh_atom_elim[elim!]: "(nabla\<turnstile>a\<sharp>Atom b) \<Longrightarrow> a\<noteq>b"
apply(ind_cases "(nabla \<turnstile>a\<sharp>Atom b)")
apply(auto)
done
lemma fresh_susp_elim[elim!]: "(nabla\<turnstile>a\<sharp>Susp pi X) \<Longrightarrow> (swapas (rev pi) a,X)\<in>nabla"
apply(ind_cases "(nabla\<turnstile>a\<sharp>Susp pi X)")
apply(auto)
done
lemma fresh_paar_elim[elim!]: "(nabla\<turnstile>a\<sharp>Paar t1 t2) \<Longrightarrow> (nabla\<turnstile>a\<sharp>t1)\<and>(nabla \<turnstile>a\<sharp>t2)"
apply(ind_cases "(nabla\<turnstile>a\<sharp>Paar t1 t2)")
apply(auto)
done
lemma fresh_func_elim[elim!]: "(nabla\<turnstile>a\<sharp>Func F t) \<Longrightarrow> (nabla\<turnstile>a\<sharp>t)"
apply(ind_cases "nabla\<turnstile>a\<sharp>Func F t")
apply(auto)
done
lemma fresh_abst_ab_elim[elim!]: "\<lbrakk>nabla\<turnstile>a\<sharp>Abst b t;a\<noteq>b\<rbrakk> \<Longrightarrow> (nabla\<turnstile>a\<sharp>t)"
apply(ind_cases "nabla\<turnstile>a\<sharp>Abst b t", auto)
done

lemma fresh_swap_left: "(nabla\<turnstile>a\<sharp>swap pi t) \<Longrightarrow> (nabla\<turnstile>swapas (rev pi) a\<sharp>t)"
apply(induct t)
apply(simp_all)
(*Abst*)
  subgoal for list t
apply(cases "swapas (rev pi) a = list")
apply(force)
    apply(force dest!: fresh_abst_ab_elim)
    done
(*Susp *)
apply(force dest!: fresh_susp_elim simp add: swapas_append[THEN sym]) 
(*Unit*)
apply(force)
(*Atom*)
apply(force dest!: fresh_atom_elim)
(*Paar*)
apply(force dest!: fresh_paar_elim)
(*Func*)
apply(force dest!: fresh_func_elim)
done

lemma fresh_swap_right: "(nabla\<turnstile>swapas (rev pi) a\<sharp>t) \<Longrightarrow> (nabla\<turnstile>a\<sharp>swap pi t)"
apply(induct t)
apply(simp_all)
(*Abst*)
  subgoal for list t
    apply(case_tac "a = swapas pi list")
apply(force)
    apply(force dest!: fresh_abst_ab_elim)
    done
(*Susp*)
apply(force dest!: fresh_susp_elim simp add: swapas_append[THEN sym])
(*Unit*)
apply(force)
(*Atom*)
apply(force dest!: fresh_atom_elim)
(*Paar*)
apply(force dest!: fresh_paar_elim)
(*Func*)
apply(force dest!: fresh_func_elim)
done

lemma fresh_weak: "nabla1\<turnstile>a\<sharp>t\<longrightarrow>(nabla1\<union>nabla2)\<turnstile>a\<sharp>t"
apply(rule impI)
apply(erule fresh.induct)
apply(auto)
done

end 
