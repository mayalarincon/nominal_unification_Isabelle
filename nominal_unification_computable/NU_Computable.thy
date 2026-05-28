(*<*)
theory NU_Computable
  imports "Nominal_Unification_20260508/NU_Completeness"
begin
(*>*)

definition rank_sred :: "((((trm \<times> trm) list \<times> (char list \<times> trm) list) \<times> substs \<times> bool) \<times>
      ((trm \<times> trm) list \<times> (char list \<times> trm) list) \<times> substs \<times> bool) set" where
"rank_sred =
  measures [
    \<lambda>((eprobs, fprobs), s, B). card (vars_eprobs eprobs),
    \<lambda>((eprobs, fprobs), s, B). size_eprobs eprobs,
    \<lambda>((eprobs, fprobs), s, B). size_fprobs fprobs
  ]"


function (sequential) sred_fun :: "(problem_type \<times> substs \<times> bool) \<Rightarrow> (problem_type \<times> substs \<times> bool)" where
 "sred_fun (((Unit \<approx>? Unit) # xs, ys), s, B) = sred_fun ((xs,ys), s, B)" |
 "sred_fun (((Paar t1 t2 \<approx>? Paar s1 s2)#xs,ys), s, B) = sred_fun (((t1\<approx>?s1)#(t2\<approx>?s2)#xs,ys), s, B)" |
 "sred_fun (((Func F t1 \<approx>? Func G t2)#xs,ys), s, B) = (if F = G then
                                                        sred_fun(((t1\<approx>?t2)#xs,ys),s, B)         
                                                       else
                                                        (((Func F t1 \<approx>? Func G t2)#xs,ys), s, False))" |
 "sred_fun (((Abst a t1 \<approx>? Abst b t2)#xs,ys), s, B) = (if a = b then
                                                        sred_fun (((t1\<approx>?t2)#xs,ys), s, B)
                                                       else
                                                        sred_fun (((t1\<approx>?swap [(a,b)] t2)#xs,(a\<sharp>?t2)#ys), s, B))"|
 "sred_fun (((Atom a\<approx>?Atom b)#xs,ys), s, B) = (if a = b then
                                                sred_fun ((xs,ys), s, B)
                                               else
                                                (((Atom a \<approx>? Atom b)#xs,ys), s, False))" |
 "sred_fun (((Susp pi1 X\<approx>?Susp pi2 Y)#xs,ys), s, B) = (if X =Y then 
                                                        sred_fun ((xs,(map (\<lambda>a. a\<sharp>? Susp [] X) (ds_list pi1 pi2))@ys), s, B)
                                                       else
                                                        sred_fun (apply_subst [(X,swap (rev pi1) (Susp pi2 Y))] (xs,ys), [(X,swap (rev pi1) (Susp pi2 Y))] \<bullet> s, B))"|
 "sred_fun (((Susp pi X\<approx>?t)#xs,ys), s, B) = (if \<not> (occurs X t) then
                                              sred_fun (apply_subst [(X,swap (rev pi) t)] (xs,ys), [(X,swap (rev pi) t)] \<bullet> s, B)
                                             else
                                              (((Susp pi X\<approx>?t)#xs,ys), s, False))" |
 "sred_fun (((t\<approx>?Susp pi X)#xs,ys), s, B) = (if \<not> (occurs X t) then
                                              sred_fun (apply_subst [(X,swap (rev pi) t)] (xs,ys), [(X,swap (rev pi) t)] \<bullet> s, B)
                                             else
                                              (((t\<approx>?Susp pi X)#xs,ys), s, False))" |
 "sred_fun (([],ys), s, B) = (([], ys), s, B)" |
 "sred_fun ((e#xs, ys), s, B) = ((e#xs, ys), s, False)" 
  by pat_completeness auto


termination
proof(relation rank_sred)

  show "wf rank_sred" 
    unfolding rank_sred_def by simp

  show "\<And>xs ys s B. (((xs, ys), s, B), ((Unit, Unit) # xs, ys), s, B) \<in> rank_sred"
    unfolding rank_sred_def by simp

  show "\<And>t1 t2 s1 s2 xs ys s B.
       ((((t1, s1) # (t2, s2) # xs, ys), s, B), ((Paar t1 t2, Paar s1 s2) # xs, ys), s, B) \<in> rank_sred"
    unfolding rank_sred_def vars_eprobs.simps size_eprobs.simps size_trm.simps vars_trm.simps
    by (simp add: Un_commute Un_left_commute)

  show "\<And>t1 F G t2 xs ys s B. F = G \<Longrightarrow>
       ((((t1, t2) # xs, ys), s, B), ((trm.Func F t1, trm.Func G t2) # xs, ys), s, B)
       \<in> rank_sred"
    unfolding rank_sred_def vars_eprobs.simps size_eprobs.simps size_trm.simps vars_trm.simps
    by simp

  show  "\<And>a t1 b t2 xs ys s B. a = b \<Longrightarrow>
       ((((t1, t2) # xs, ys), s, B), ((Abst a t1, Abst b t2) # xs, ys), s, B) \<in> rank_sred"
    unfolding rank_sred_def vars_eprobs.simps 
      size_eprobs.simps size_trm.simps vars_trm.simps
    by simp

  show "\<And>a t1 b t2 xs ys s B.
       a \<noteq> b \<Longrightarrow>
       ((((t1, swap [(a, b)] t2) # xs, (a, t2) # ys), s, B), ((Abst a t1, Abst b t2) # xs, ys),
        s, B)
       \<in> rank_sred"
    using vars_swap unfolding rank_sred_def vars_eprobs.simps 
        size_eprobs.simps size_trm.simps vars_trm.simps
    by simp

  show "\<And>a b xs ys s B. a = b \<Longrightarrow>
  (((xs, ys), s, B), ((Atom a, Atom b) # xs, ys), s, B) \<in> rank_sred"
    unfolding rank_sred_def vars_eprobs.simps 
      size_eprobs.simps size_trm.simps vars_trm.simps 
    by simp

  show "\<And>pi1 X pi2 Y xs ys s B.
       X = Y \<Longrightarrow>
       (((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), s, B)
       \<in> rank_sred"
  proof-
    fix pi1 pi2 xs ys s B and X Y :: string
    assume "X = Y"
    hence vars: "vars_eprobs ((Susp pi1 X, Susp pi2 Y) # xs) = {X} \<union> vars_eprobs xs" and
          size: "size_eprobs ((Susp pi1 X, Susp pi2 Y) # xs) = 2 + size_eprobs xs"
      unfolding vars_eprobs.simps size_eprobs.simps by simp+
    have size_leq: "size_eprobs xs < size_eprobs ((Susp pi1 Y, Susp pi2 Y) # xs)"
      by simp
    have "(((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), s, B)
       \<in> rank_sred"
    proof(cases "X \<in> vars_eprobs xs")
      case True
      hence "card ({X} \<union> vars_eprobs xs) = card (vars_eprobs xs)"
         by (simp add: insert_absorb)
      then show ?thesis 
        using size_leq vars unfolding rank_sred_def by simp
    next
      case False
      hence "card ({X} \<union> vars_eprobs xs) = 1 + card (vars_eprobs xs)"
        by auto
      then show ?thesis 
        using \<open>X = Y\<close> unfolding rank_sred_def by simp
    qed
    thus "(((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), s, B)
       \<in> rank_sred" by simp
  qed

  have aux1: "\<not> occurs X t \<Longrightarrow> ((apply_subst [(X, swap (rev pi) t)] (xs, ys),
         [(X, swap (rev pi) t)] \<bullet> s, B),
        ((Susp pi X, t) # xs, ys), s, B)
       \<in> rank_sred" for X t pi xs ys s B
  proof-
    let ?union = "insert X (vars_trm t \<union> vars_eprobs xs)"
      and ?size = "size_trm t + size_eprobs xs"
    assume assm: " \<not>occurs X t"
    have 
     vars: "vars_eprobs ((Susp pi X, t) # xs) = ?union" and
     size: "size_eprobs ((Susp pi X, t) # xs) = 1 + ?size"
      unfolding vars_eprobs.simps size_eprobs.simps by simp+
    moreover have 
      "apply_subst [(X, swap (rev pi) t)] (xs, ys) = (apply_subst_eprobs [(X, swap (rev pi) t)] xs, 
    apply_subst_fprobs [(X, swap (rev pi) t)] ys)"
      using apply_subst_equivalence by auto
    ultimately show ?thesis
      using vars_decrease[OF assm] unfolding rank_sred_def by simp
  qed

  have aux2: "\<not> occurs X t \<Longrightarrow> ((apply_subst [(X, swap (rev pi) t)] (xs, ys),
         [(X, swap (rev pi) t)] \<bullet> s, B),
        ((t, Susp pi X) # xs, ys), s, B)
       \<in> rank_sred" for X t pi xs ys s B
  proof-
    let ?union = "insert X (vars_trm t \<union> vars_eprobs xs)"
      and ?size = "size_trm t + size_eprobs xs"
    assume assm: " \<not>occurs X t"
    have 
     vars: "vars_eprobs ((t, Susp pi X) # xs) = ?union" and
     size: "size_eprobs ((t, Susp pi X) # xs) = 1 + ?size"
      unfolding vars_eprobs.simps size_eprobs.simps by simp+
    moreover have 
      "apply_subst [(X, swap (rev pi) t)] (xs, ys) = (apply_subst_eprobs [(X, swap (rev pi) t)] xs, 
    apply_subst_fprobs [(X, swap (rev pi) t)] ys)"
      using apply_subst_equivalence by auto
    ultimately show ?thesis
      using vars_decrease[OF assm] unfolding rank_sred_def by simp
  qed

  show "\<And>pi1 X pi2 Y xs ys s B.
       X \<noteq> Y \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi1) (Susp pi2 Y))] (xs, ys),
         [(X, swap (rev pi1) (Susp pi2 Y))] \<bullet> s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), s, B)
       \<in> rank_sred"
  proof-
    fix X Y :: string and pi1 pi2 xs ys s B
    assume "X \<noteq> Y"
    hence not_occurs: "\<not> occurs X (Susp pi2 Y)" 
      unfolding occurs.simps by simp
    thus "X \<noteq> Y \<Longrightarrow>
        X \<noteq> Y \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi1) (Susp pi2 Y))] (xs, ys),
         [(X, swap (rev pi1) (Susp pi2 Y))] \<bullet> s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), s, B)
       \<in> rank_sred" 
       using aux1[OF not_occurs] unfolding rank_sred_def by simp
   qed

   show "\<And>pi X v va xs ys s B.
       \<not> occurs X (Abst v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Abst v va))] (xs, ys),
         [(X, swap (rev pi) (Abst v va))] \<bullet> s, B),
        ((Susp pi X, Abst v va) # xs, ys), s, B)
       \<in> rank_sred"
     using aux1 by blast

   show "\<And>pi X xs ys s B.
       \<not> occurs X Unit \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) Unit)] (xs, ys), [(X, swap (rev pi) Unit)] \<bullet> s, B),
        ((Susp pi X, Unit) # xs, ys), s, B)
       \<in> rank_sred" using aux1 by blast

   show "\<And>pi X v xs ys s B.
       \<not> occurs X (Atom v) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Atom v))] (xs, ys), [(X, swap (rev pi) (Atom v))] \<bullet> s,
         B),
        ((Susp pi X, Atom v) # xs, ys), s, B)
       \<in> rank_sred" using aux1 by blast

   show "\<And>pi X v va xs ys s B.
       \<not> occurs X (Paar v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Paar v va))] (xs, ys),
         [(X, swap (rev pi) (Paar v va))] \<bullet> s, B),
        ((Susp pi X, Paar v va) # xs, ys), s, B)
       \<in> rank_sred" using aux1 by blast

   show "\<And>pi X v va xs ys s B.
       \<not> occurs X (trm.Func v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (trm.Func v va))] (xs, ys),
         [(X, swap (rev pi) (trm.Func v va))] \<bullet> s, B),
        ((Susp pi X, trm.Func v va) # xs, ys), s, B)
       \<in> rank_sred" using aux1 by blast

   show "\<And>v va pi X xs ys s B.
       \<not> occurs X (Abst v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Abst v va))] (xs, ys),
         [(X, swap (rev pi) (Abst v va))] \<bullet> s, B),
        ((Abst v va, Susp pi X) # xs, ys), s, B)
       \<in> rank_sred" using aux2 by blast

   show "\<And>pi X xs ys s B.
       \<not> occurs X Unit \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) Unit)] (xs, ys), [(X, swap (rev pi) Unit)] \<bullet> s, B),
        ((Unit, Susp pi X) # xs, ys), s, B)
       \<in> rank_sred" using aux2 by blast

   show "\<And>v pi X xs ys s B.
       \<not> occurs X (Atom v) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Atom v))] (xs, ys), [(X, swap (rev pi) (Atom v))] \<bullet> s,
         B),
        ((Atom v, Susp pi X) # xs, ys), s, B)
       \<in> rank_sred" using aux2 by blast

   show "\<And>v va pi X xs ys s B.
       \<not> occurs X (Paar v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Paar v va))] (xs, ys),
         [(X, swap (rev pi) (Paar v va))] \<bullet> s, B),
        ((Paar v va, Susp pi X) # xs, ys), s, B)
       \<in> rank_sred" using aux2 by blast

   show "\<And>v va pi X xs ys s B.
       \<not> occurs X (trm.Func v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (trm.Func v va))] (xs, ys),
         [(X, swap (rev pi) (trm.Func v va))] \<bullet> s, B),
        ((trm.Func v va, Susp pi X) # xs, ys), s, B)
       \<in> rank_sred" using aux2 by blast
qed

lemma sred_rtc_to_sred_fun:
  assumes "P1 \<turnstile> s1 \<leadsto>\<^sup>* P2"
  shows "sred_fun (P1, [], True) = (P2, s1, True)"
  sorry 

lemma sred_fun_to_sred_rtc:
  assumes  "sred_fun (P1, [], True) = (P2, s1, True)"
  shows "P1 \<turnstile> s1 \<leadsto>\<^sup>* P2"
  sorry

(*show these lemmas

next steps:
0. add nabla in the sred_fun 
1. define the function for freshness (cred_fun)
2. prove termination
3. prove equivalence
4. define the unif computable function that takes as input a problem and calls the functions
sred_fun and cred_fun
5. prove termination of unif*)







(*<*)
end
(*>*)