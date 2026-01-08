theory Fresh

imports Swap Terms Disagreement

begin

type_synonym fresh_envs = "(string \<times> string) set"

inductive fresh :: "fresh_envs \<Rightarrow> string \<Rightarrow> trm \<Rightarrow> bool" (" _ \<turnstile> _ \<sharp> _" [80,80,80] 80) 
  where
  fresh_abst_ab[intro!]: "\<lbrakk>nabla \<turnstile> a \<sharp> t; a\<noteq>b\<rbrakk> \<Longrightarrow> nabla \<turnstile> a \<sharp> Abst b t" |
  fresh_abst_aa[intro!]: "nabla \<turnstile> a \<sharp> Abst a t" |
  fresh_unit[intro!]:    "nabla \<turnstile> a \<sharp> Unit" |
  fresh_atom[intro!]:    "a \<noteq> b \<Longrightarrow> nabla \<turnstile> a \<sharp> Atom b" |
  fresh_susp[intro!]:    "(swapas (rev pi) a,X) \<in> nabla \<Longrightarrow> nabla \<turnstile> a \<sharp> Susp pi X" |
  fresh_paar[intro!]:    "\<lbrakk>nabla \<turnstile> a \<sharp> t1; nabla \<turnstile> a \<sharp> t2\<rbrakk> \<Longrightarrow> nabla \<turnstile> a \<sharp> Paar t1 t2" |
  fresh_func[intro!]:    "nabla \<turnstile> a \<sharp> t \<Longrightarrow> nabla \<turnstile> a \<sharp> Func F t"

inductive_cases Fresh_elims:
  "nabla \<turnstile> a \<sharp> Abst b t"
  "nabla \<turnstile> a \<sharp> Unit"
  "nabla \<turnstile> a \<sharp> Atom b"
  "nabla \<turnstile> a \<sharp> Susp pi X"
  "nabla \<turnstile> a \<sharp> Paar t1 t2"
  "nabla \<turnstile> a \<sharp> Func F t"

lemma fresh_swap_eqvt: 
  assumes "nabla \<turnstile> a \<sharp> t"
  shows "nabla \<turnstile> swapas pi a \<sharp> swap pi t"
using assms
  apply(induct arbitrary: pi rule: fresh.induct)
  apply(auto simp add: swapas_append dest: swapas_rev_pi_a)
done  

lemma fresh_swap_left: 
  assumes "nabla \<turnstile> a \<sharp> swap pi t"
  shows "nabla \<turnstile> swapas (rev pi) a \<sharp> t"
  using assms
proof(induct t arbitrary: a pi)
  case (Abst x1 t)
  have "nabla \<turnstile> a \<sharp> swap pi (Abst x1 t)" by fact
  then have "(nabla \<turnstile> a \<sharp> swap pi t \<and> a \<noteq> swapas pi x1) \<or> (a = swapas pi x1)"
    by (metis Fresh_elims(1) swap.simps(4))
  moreover {
    assume as: "nabla \<turnstile> a \<sharp> swap pi t \<and> a \<noteq> swapas pi x1" 
    have "nabla \<turnstile> swapas (rev pi) a \<sharp> Abst x1 t"
      using Abst.hyps as by auto 
  }
  moreover {
    assume as: "a = swapas pi x1"
    then have "nabla \<turnstile> swapas (rev pi) a \<sharp> Abst x1 t"
      by (simp add: fresh_abst_aa)      
  } 
  ultimately show "nabla \<turnstile> swapas (rev pi) a \<sharp> Abst x1 t" 
    by (metis) 
next
  case (Susp x1 x2)
  have "nabla \<turnstile> a \<sharp> swap pi (Susp x1 x2)" by fact
  have "(swapas (rev x1) (swapas (rev pi) a), x2) \<in> nabla"
    by (metis Fresh_elims(4) Susp rev_append swap.simps(3) swapas_append) 
  then show "nabla \<turnstile> swapas (rev pi) a \<sharp> Susp x1 x2"
    by (simp add: fresh_susp)
next
  case (Atom x)
  have "nabla \<turnstile> a \<sharp> swap pi (Atom x)" by fact
  then have "swapas pi x \<noteq> a" by (auto elim: Fresh_elims)
  then have "x \<noteq> swapas (rev pi) a" using swapas_rev_pi_b by blast  
  then show "nabla \<turnstile> swapas (rev pi) a \<sharp> Atom x"
    by (simp add: fresh_atom) 
qed (auto elim: Fresh_elims)


lemma fresh_swap_right: 
  assumes "nabla \<turnstile> swapas (rev pi) a \<sharp> t"
  shows "nabla \<turnstile> a \<sharp> swap pi t"
  by (metis assms fresh_swap_eqvt swapas_rev_pi_b)

lemma fresh_weak: 
  assumes "nabla1 \<turnstile> a \<sharp> t"
  shows "(nabla1 \<union> nabla2) \<turnstile> a \<sharp> t"
  using assms
  by(induct rule: fresh.induct)(auto)


end 
