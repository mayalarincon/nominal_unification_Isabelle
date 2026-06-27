(*<*)
theory NU_Computable
  imports NU_Completeness
begin
(*>*)

definition rank_fun :: "((((trm \<times> trm) list \<times> (char list \<times> trm) list) \<times> fresh_envs \<times> substs \<times> bool) \<times>
      ((trm \<times> trm) list \<times> (char list \<times> trm) list) \<times> fresh_envs \<times> substs \<times> bool) set" where
"rank_fun =
  measures [
    \<lambda>((eprobs, fprobs), s, B). card (vars_eprobs eprobs),
    \<lambda>((eprobs, fprobs), s, B). size_eprobs eprobs,
    \<lambda>((eprobs, fprobs), s, B). size_fprobs fprobs
  ]"


fun prj :: "trm \<Rightarrow> (string \<times> string) list" where
  "prj (Susp pi t) = pi" |
  "prj _ = []"


function sred_fun ::  "(problem_type \<times> fresh_envs \<times> substs \<times> bool) \<Rightarrow> (problem_type \<times> fresh_envs \<times> substs \<times> bool)" where
"sred_fun (([],ys), nabla, s, B) = (([], ys), nabla, s, B)" |
"sred_fun ((e#xs, ys), nabla, s, B) = 
                        (case e of 
                              Unit \<approx>? Unit \<Rightarrow> sred_fun ((xs,ys), nabla, s, B) |
                              Paar t1 t2 \<approx>? Paar s1 s2 \<Rightarrow> sred_fun (((t1\<approx>?s1)#(t2\<approx>?s2)#xs,ys), nabla, s, B) |
                              Func F t1 \<approx>? Func G t2 \<Rightarrow> (if F = G then
                                                          sred_fun (((t1\<approx>?t2)#xs,ys), nabla, s, B) 
                                                         else
                                                         (((Func F t1 \<approx>? Func G t2)#xs,ys), nabla, s, False))|
                              Abst a t1 \<approx>? Abst b t2 \<Rightarrow> (if a = b then
                                                        sred_fun (((t1\<approx>?t2)#xs,ys), nabla, s, B)
                                                        else
                                                        sred_fun (((t1\<approx>?swap [(a,b)] t2)#xs,(a\<sharp>?t2)#ys), nabla, s, B))|
                              Atom a\<approx>?Atom b \<Rightarrow> (if a = b then
                                                        sred_fun ((xs,ys), nabla, s, B) 
                                                 else
                                                   (((Atom a \<approx>? Atom b)#xs,ys), nabla, s, False))|
                              Susp pi X\<approx>?t \<Rightarrow> (case t of 
                                               Susp pi2 X \<Rightarrow> sred_fun ((xs,(map (\<lambda>a. a\<sharp>? Susp [] X) (ds_list pi pi2))@ys), nabla, s, B) |
                                               _ \<Rightarrow> (if occurs X t then
                                                       (((Susp pi X\<approx>?t)#xs,ys), nabla, s, False)
                                                     else
                                                      sred_fun (apply_subst [(X,swap (rev pi) t)] (xs,ys), nabla, [(X,swap (rev pi) t)] \<bullet> s, B))) |
                             t \<approx>? Susp pi X \<Rightarrow> (case t of 
                                               Susp pi2 X \<Rightarrow> sred_fun ((xs,(map (\<lambda>a. a\<sharp>? Susp [] X) (ds_list pi pi2))@ys), nabla, s, B) |
                                               _ \<Rightarrow> (if occurs X t then
                                                       (((Susp pi X\<approx>?t)#xs,ys), nabla, s, False)
                                                     else
                                                      sred_fun (apply_subst [(X,swap (rev pi) t)] (xs,ys), nabla, [(X,swap (rev pi) t)] \<bullet> s, B))))"
  by pat_completeness auto




(*case t of Susp pi2 X' => (if X' = X then <actual case> else default) | _ => default*)

text\<open>Auxiliary lemmata for termination\<close>

lemma rank_r_fun_susp_same_var:
  assumes "X = Y"
  shows "(((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), nabla, s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), nabla, s, B)
       \<in> rank_fun"
proof-
   have vars: "vars_eprobs ((Susp pi1 X, Susp pi2 Y) # xs) = {X} \<union> vars_eprobs xs" and
          size: "size_eprobs ((Susp pi1 X, Susp pi2 Y) # xs) = 2 + size_eprobs xs"
     using assms unfolding vars_eprobs.simps size_eprobs.simps by simp+
    have size_leq: "size_eprobs xs < size_eprobs ((Susp pi1 Y, Susp pi2 Y) # xs)"
      by simp
    have "(((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), nabla, s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), nabla, s, B)
       \<in> rank_fun"
    proof(cases "X \<in> vars_eprobs xs")
      case True
      hence "card ({X} \<union> vars_eprobs xs) = card (vars_eprobs xs)"
         by (simp add: insert_absorb)
      then show ?thesis 
        using size_leq vars unfolding rank_fun_def by simp
    next
      case False
      hence "card ({X} \<union> vars_eprobs xs) = 1 + card (vars_eprobs xs)"
        by auto
      then show ?thesis 
        using \<open>X = Y\<close> unfolding rank_fun_def by simp
    qed
    thus ?thesis by simp
  qed

lemma rank_r_fun_susp_left: 
  assumes "\<not> occurs X t"
  shows "((apply_subst [(X, swap (rev pi) t)] (xs, ys), nabla, [(X, swap (rev pi) t)] \<bullet> s, B),
         ((Susp pi X, t) # xs, ys), nabla, s, B)
       \<in> rank_fun"
proof-
    let ?union = "insert X (vars_trm t \<union> vars_eprobs xs)"
      and ?size = "size_trm t + size_eprobs xs"
    have 
     vars: "vars_eprobs ((Susp pi X, t) # xs) = ?union" and
     size: "size_eprobs ((Susp pi X, t) # xs) = 1 + ?size"
      unfolding vars_eprobs.simps size_eprobs.simps by simp+
    moreover have 
      "apply_subst [(X, swap (rev pi) t)] (xs, ys) = (apply_subst_eprobs [(X, swap (rev pi) t)] xs, 
    apply_subst_fprobs [(X, swap (rev pi) t)] ys)"
      using apply_subst_equivalence by auto
    ultimately show ?thesis
      using vars_decrease[OF assms] unfolding rank_fun_def by simp
  qed

lemma rank_r_fun_susp_right:
  assumes "\<not> occurs X t"
  shows "((apply_subst [(X, swap (rev pi) t)] (xs, ys), nabla, [(X, swap (rev pi) t)] \<bullet> s, B),
        ((t, Susp pi X) # xs, ys), nabla, s, B)
       \<in> rank_fun"
 proof-
    let ?union = "insert X (vars_trm t \<union> vars_eprobs xs)"
      and ?size = "size_trm t + size_eprobs xs"
    have 
     vars: "vars_eprobs ((t, Susp pi X) # xs) = ?union" and
     size: "size_eprobs ((t, Susp pi X) # xs) = 1 + ?size"
      unfolding vars_eprobs.simps size_eprobs.simps by simp+
    moreover have 
      "apply_subst [(X, swap (rev pi) t)] (xs, ys) = (apply_subst_eprobs [(X, swap (rev pi) t)] xs, 
    apply_subst_fprobs [(X, swap (rev pi) t)] ys)"
      using apply_subst_equivalence by auto
    ultimately show ?thesis
      using vars_decrease[OF assms] unfolding rank_fun_def by simp
  qed

termination sred_fun
proof
  show "wf rank_fun" 
    unfolding rank_fun_def by simp

  fix t1 t2 :: trm and
      xs :: "(trm \<times> trm) list" and
      nabla ys s B
  have "((((t1\<approx>?t2)#xs, ys), nabla, s, B), ((xs, ys), nabla, s, B)) \<in> rank_fun"
    unfolding rank_fun_def size_eprobs.simps size_trm.simps

 (* show "\<And>xs ys nabla s B. (((xs, ys), nabla, s, B), ((Unit, Unit) # xs, ys), nabla, s, B) \<in> rank_fun"
    unfolding rank_fun_def by simp

  show "\<And>t1 t2 s1 s2 xs ys nabla s B.
       ((((t1, s1) # (t2, s2) # xs, ys), nabla, s, B), ((Paar t1 t2, Paar s1 s2) # xs, ys), nabla, s, B) \<in> rank_fun"
    unfolding rank_fun_def vars_eprobs.simps size_eprobs.simps size_trm.simps vars_trm.simps
    by (simp add: Un_commute Un_left_commute)

  show "\<And>t1 F G t2 xs ys nabla s B. F = G \<Longrightarrow>
       ((((t1, t2) # xs, ys), nabla, s, B), ((trm.Func F t1, trm.Func G t2) # xs, ys), nabla, s, B)
       \<in> rank_fun"
    unfolding rank_fun_def vars_eprobs.simps size_eprobs.simps size_trm.simps vars_trm.simps
    by simp

  show  "\<And>a t1 b t2 xs ys nabla s B. a = b \<Longrightarrow>
       ((((t1, t2) # xs, ys), nabla, s, B), ((Abst a t1, Abst b t2) # xs, ys), nabla, s, B) \<in> rank_fun"
    unfolding rank_fun_def vars_eprobs.simps 
      size_eprobs.simps size_trm.simps vars_trm.simps
    by simp

  show "\<And>a t1 b t2 xs ys nabla s B.
       a \<noteq> b \<Longrightarrow>
       ((((t1, swap [(a, b)] t2) # xs, (a, t2) # ys), nabla, s, B), ((Abst a t1, Abst b t2) # xs, ys),
        nabla, s, B)
       \<in> rank_fun"
    using vars_swap unfolding rank_fun_def vars_eprobs.simps 
        size_eprobs.simps size_trm.simps vars_trm.simps
    by simp

  show "\<And>a b xs ys nabla s B. a = b \<Longrightarrow>
  (((xs, ys), nabla, s, B), ((Atom a, Atom b) # xs, ys), nabla, s, B) \<in> rank_fun"
    unfolding rank_fun_def vars_eprobs.simps 
      size_eprobs.simps size_trm.simps vars_trm.simps 
    by simp

  show "\<And>pi1 X pi2 Y xs ys nabla s B.
       X = Y \<Longrightarrow>
       (((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), nabla, s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), nabla, s, B)
       \<in> rank_fun"
  proof-
    fix pi1 pi2 xs ys nabla s B and X Y :: string
    assume "X = Y"
    hence vars: "vars_eprobs ((Susp pi1 X, Susp pi2 Y) # xs) = {X} \<union> vars_eprobs xs" and
          size: "size_eprobs ((Susp pi1 X, Susp pi2 Y) # xs) = 2 + size_eprobs xs"
      unfolding vars_eprobs.simps size_eprobs.simps by simp+
    have size_leq: "size_eprobs xs < size_eprobs ((Susp pi1 Y, Susp pi2 Y) # xs)"
      by simp
    have "(((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), nabla, s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), nabla, s, B)
       \<in> rank_fun"
    proof(cases "X \<in> vars_eprobs xs")
      case True
      hence "card ({X} \<union> vars_eprobs xs) = card (vars_eprobs xs)"
         by (simp add: insert_absorb)
      then show ?thesis 
        using size_leq vars unfolding rank_fun_def by simp
    next
      case False
      hence "card ({X} \<union> vars_eprobs xs) = 1 + card (vars_eprobs xs)"
        by auto
      then show ?thesis 
        using \<open>X = Y\<close> unfolding rank_fun_def by simp
    qed
    thus "(((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), nabla, s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), nabla, s, B)
       \<in> rank_fun" by simp
  qed

  have aux1: "\<not> occurs X t \<Longrightarrow> ((apply_subst [(X, swap (rev pi) t)] (xs, ys), nabla,
         [(X, swap (rev pi) t)] \<bullet> s, B),
        ((Susp pi X, t) # xs, ys), nabla, s, B)
       \<in> rank_fun" for X t pi xs ys nabla s B
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
      using vars_decrease[OF assm] unfolding rank_fun_def by simp
  qed

  have aux2: "\<not> occurs X t \<Longrightarrow> ((apply_subst [(X, swap (rev pi) t)] (xs, ys), nabla,
         [(X, swap (rev pi) t)] \<bullet> s, B),
        ((t, Susp pi X) # xs, ys), nabla, s, B)
       \<in> rank_fun" for X t pi xs ys nabla s B
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
      using vars_decrease[OF assm] unfolding rank_fun_def by simp
  qed

  show "\<And>pi1 X pi2 Y xs ys nabla s B.
       X \<noteq> Y \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi1) (Susp pi2 Y))] (xs, ys), nabla,
         [(X, swap (rev pi1) (Susp pi2 Y))] \<bullet> s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), nabla, s, B)
       \<in> rank_fun"
  proof-
    fix X Y :: string and pi1 pi2 xs ys nabla s B
    assume "X \<noteq> Y"
    hence not_occurs: "\<not> occurs X (Susp pi2 Y)" 
      unfolding occurs.simps by simp
    thus "X \<noteq> Y \<Longrightarrow>
        X \<noteq> Y \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi1) (Susp pi2 Y))] (xs, ys), nabla,
         [(X, swap (rev pi1) (Susp pi2 Y))] \<bullet> s, B),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), nabla, s, B)
       \<in> rank_fun" 
       using aux1[OF not_occurs] unfolding rank_fun_def by simp
   qed

   show "\<And>pi X v va xs ys nabla s B.
       \<not> occurs X (Abst v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Abst v va))] (xs, ys), nabla,
         [(X, swap (rev pi) (Abst v va))] \<bullet> s, B),
        ((Susp pi X, Abst v va) # xs, ys), nabla, s, B)
       \<in> rank_fun"
     using aux1 by blast

   show "\<And>pi X xs ys nabla s B.
       \<not> occurs X Unit \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) Unit)] (xs, ys), nabla, [(X, swap (rev pi) Unit)] \<bullet> s, B),
        ((Susp pi X, Unit) # xs, ys), nabla, s, B)
       \<in> rank_fun" using aux1 by blast

   show "\<And>pi X v xs ys nabla s B.
       \<not> occurs X (Atom v) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Atom v))] (xs, ys), nabla, [(X, swap (rev pi) (Atom v))] \<bullet> s,
         B),
        ((Susp pi X, Atom v) # xs, ys), nabla, s, B)
       \<in> rank_fun" using aux1 by blast

   show "\<And>pi X v va xs ys nabla s B.
       \<not> occurs X (Paar v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Paar v va))] (xs, ys), nabla,
         [(X, swap (rev pi) (Paar v va))] \<bullet> s, B),
        ((Susp pi X, Paar v va) # xs, ys), nabla, s, B)
       \<in> rank_fun" using aux1 by blast

   show "\<And>pi X v va xs ys nabla s B.
       \<not> occurs X (trm.Func v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (trm.Func v va))] (xs, ys), nabla,
         [(X, swap (rev pi) (trm.Func v va))] \<bullet> s, B),
        ((Susp pi X, trm.Func v va) # xs, ys), nabla, s, B)
       \<in> rank_fun" using aux1 by blast

   show "\<And>v va pi X xs ys nabla s B.
       \<not> occurs X (Abst v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Abst v va))] (xs, ys), nabla,
         [(X, swap (rev pi) (Abst v va))] \<bullet> s, B),
        ((Abst v va, Susp pi X) # xs, ys), nabla, s, B)
       \<in> rank_fun" using aux2 by blast

   show "\<And>pi X xs ys nabla s B.
       \<not> occurs X Unit \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) Unit)] (xs, ys), nabla, [(X, swap (rev pi) Unit)] \<bullet> s,
         B),
        ((Unit, Susp pi X) # xs, ys), nabla, s, B)
       \<in> rank_fun" using aux2 by blast

   show "\<And>v pi X xs ys nabla s B.
       \<not> occurs X (Atom v) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Atom v))] (xs, ys), nabla,
         [(X, swap (rev pi) (Atom v))] \<bullet> s, B),
        ((Atom v, Susp pi X) # xs, ys), nabla, s, B)
       \<in> rank_fun" using aux2 by blast

   show "\<And>v va pi X xs ys nabla s B.
       \<not> occurs X (Paar v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (Paar v va))] (xs, ys), nabla,
         [(X, swap (rev pi) (Paar v va))] \<bullet> s, B),
        ((Paar v va, Susp pi X) # xs, ys), nabla, s, B)
       \<in> rank_fun" using aux2 by blast

   show "\<And>v va pi X xs ys nabla s B.
       \<not> occurs X (trm.Func v va) \<Longrightarrow>
       ((apply_subst [(X, swap (rev pi) (trm.Func v va))] (xs, ys), nabla,
         [(X, swap (rev pi) (trm.Func v va))] \<bullet> s, B),
        ((trm.Func v va, Susp pi X) # xs, ys), nabla, s, B)
       \<in> rank_fun" using aux2 by blast
 qed*)



lemma sred_fun_sound:
  assumes  "sred_fun (P1, nabla, s, True) = (P2, nabla', s', B)"
  shows "\<exists> s1. P1 \<turnstile> s1 \<leadsto>\<^sup>* P2"
  using assms
proof(induction "(P1, nabla, s, True)" arbitrary: P1 nabla s rule: sred_fun.induct)
  case (1 xs ys nabla s)
  then show ?case sorry
next
  case (2 t1 t2 s1 s2 xs ys nabla s)
  then show ?case sorry
next
  case (3 F t1 G t2 xs ys nabla s)
  then show ?case sorry
next
  case (4 a t1 b t2 xs ys nabla s)
  then show ?case sorry
next
  case (5 a b xs ys nabla s)
  then show ?case sorry
next
  case (6 pi X t xs ys nabla s)
  then show ?case sorry
next
  case ("7_1" v va pi X xs ys nabla s)
  then show ?case sorry
next
  case ("7_2" pi X xs ys nabla s)
  then show ?case sorry
next
  case ("7_3" v pi X xs ys nabla s)
  then show ?case sorry
next
  case ("7_4" v va pi X xs ys nabla s)
  then show ?case sorry
next
  case ("7_5" v va pi X xs ys nabla s)
  then show ?case sorry
qed(auto)


  (*case (1 xs ys nabla s)
  hence fun_step:
    "sred_fun ((xs, ys), nabla, s, True) = (P2, nabla', s', B)"
    by simp
  with 1(1) show "\<exists>s1. ((Unit, Unit) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
    by auto
next
  case (2 t1 t2 s1 s2 xs ys nabla s)
  hence fun_step:
    "sred_fun (((t1, s1) # (t2, s2) # xs, ys), nabla, s, True) = (P2, nabla', s', B)"
    by simp
   with 2(1) show "\<exists>\<sigma>. ((Paar t1 t2, Paar s1 s2) # xs, ys) \<turnstile> \<sigma> \<leadsto>\<^sup>* P2" 
     by auto
next
  case (3 F t1 G t2 xs ys nabla s)
  then show "\<exists>s1. ((Func F t1, Func G t2) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
  proof(cases "F = G")
    case True
    with 3(2) have "sred_fun (((t1, t2) # xs, ys), nabla, s, True) = (P2, nabla', s', B)"
      by simp
    with 3(1) True
    show "\<exists>s1. ((Func F t1, Func G t2) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
      by auto
  next
    case False
    hence "sred_fun (((Func F t1, Func G t2) # xs, ys), nabla, s, True) 
    = (((Func F t1 \<approx>? Func G t2)#xs,ys), nabla, s, False)" 
      by simp
    with 3(2) have P2_def: "P2 = ((Func F t1 \<approx>? Func G t2)#xs,ys)" 
      by simp
    have "((Func F t1, Func G t2) # xs, ys) \<turnstile> [] \<leadsto>\<^sup>* P2"
      using P2_def sred_refl by simp
    thus "\<exists>s1. ((Func F t1, Func G t2) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  qed
next
  case (4 a t1 b t2 xs ys nabla s)
  then show "\<exists>s1. ((Abst a t1, Abst b t2) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
  proof(cases "a = b")
    case True
    with 4(3) have "sred_fun (((t1, t2) # xs, ys), nabla, s, True) = (P2, nabla', s', B)"
      by simp
    with 4(1) True
    show "\<exists>s1. ((Abst a t1, Abst b t2) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
      by auto
  next
    case False
    with 4(3) have "sred_fun (((t1, swap [(a, b)] t2) # xs, (a, t2) # ys), nabla, s, True) =
    (P2, nabla', s', B)" by simp
    with 4(2) False
    show "\<exists>s1. ((Abst a t1, Abst b t2) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
      by auto
  qed
next
  case (5 a b xs ys nabla s)
  then show "\<exists>s1. ((Atom a, Atom b) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
  proof(cases "a=b")
    case True
    with 5(2) have "sred_fun ((xs, ys), nabla, s, True) = (P2, nabla', s', B)"
      by simp
    with 5(1) True show "\<exists>s1. ((Atom a, Atom b) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
      by auto
  next
    case False
    hence "sred_fun (((Atom a, Atom b) # xs, ys), nabla, s, True) 
    = (((Atom a \<approx>? Atom b)#xs,ys), nabla, s, False)" 
      by simp
    with 5(2) have "P2 = ((Atom a \<approx>? Atom b)#xs,ys)" 
      by simp
    hence "((Atom a, Atom b) # xs, ys) \<turnstile> [] \<leadsto>\<^sup>* P2"
      using sred_refl by simp
    then show "\<exists>s1. ((Atom a, Atom b) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
      by auto
  qed
next
  case (6 pi1 X pi2 Y xs ys nabla s)
  then show "\<exists>s1. ((Susp pi1 X, Susp pi2 Y) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
  proof(cases "X = Y")
    case True
    with 6(3) have "sred_fun ((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), nabla, s, True) =
    (P2, nabla', s', B)"
      by simp
    with 6(1) True show "\<exists>s1. ((Susp pi1 X, Susp pi2 Y) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
      by auto
  next
    case False
    with 6(3) have "sred_fun
     (apply_subst [(X, swap (rev pi1) (Susp pi2 Y))] (xs, ys), nabla,
      [(X, swap (rev pi1) (Susp pi2 Y))] \<bullet> s, True) =
    (P2, nabla', s', B)" by simp
    with 6(2) False obtain s2 where 
      more: "apply_subst [(X, swap (rev pi1) (Susp pi2 Y))] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
      by auto
    moreover have first: "((Susp pi1 X, Susp pi2 Y) # xs, ys) \<turnstile> [(X, swap (rev pi1) (Susp pi2 Y))]
                                       \<leadsto> apply_subst [(X, swap (rev pi1) (Susp pi2 Y))] (xs, ys)"
      using False var_1_sred occurs.simps by force
    ultimately have 
      "((Susp pi1 X, Susp pi2 Y) # xs, ys) \<turnstile> s2 \<bullet> [(X, swap (rev pi1) (Susp pi2 Y))] \<leadsto>\<^sup>* P2"
      using sred_rtc_step by simp
    then show "\<exists>s1. ((Susp pi1 X, Susp pi2 Y) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
      by auto
  qed
next
  case ("7_1" pi X a t xs ys nabla s)
  then show "\<exists>s1. ((Susp pi X, Abst a t) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
  proof(cases "occurs X (Abst a t)")
    case True
    hence "sred_fun (((Susp pi X, Abst a t) # xs, ys), nabla, s, True) 
      = (((Susp pi X, Abst a t) # xs, ys), nabla, s, False)" by simp
    with "7_1"(2) have "((Susp pi X, Abst a t) # xs, ys) \<turnstile> [] \<leadsto>\<^sup>* P2" 
      by auto
    then show "\<exists>s1. ((Susp pi X, Abst a t) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  next
    case False
    with "7_1"(2) have "sred_fun
     (apply_subst [(X, swap (rev pi) (Abst a t))] (xs, ys), nabla,
      [(X, swap (rev pi) (Abst a t))] \<bullet> s, True) =
    (P2, nabla', s', B)" by simp
    with "7_1"(1) False obtain s2 where
    more: "apply_subst [(X, swap (rev pi) (Abst a t))] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
      by auto
    moreover have first: "((Susp pi X, Abst a t) # xs, ys) \<turnstile> 
        [(X, swap (rev pi) (Abst a t))] \<leadsto> apply_subst [(X, swap (rev pi) (Abst a t))] (xs, ys)"
      using False var_1_sred occurs.simps by force
    ultimately have "((Susp pi X, Abst a t) # xs, ys) \<turnstile> 
              s2 \<bullet> [(X, swap (rev pi) (Abst a t))] \<leadsto>\<^sup>* P2"
      using sred_rtc_step by simp
    then show "\<exists>s1. ((Susp pi X, Abst a t) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  qed
next
  case ("7_2" pi X xs ys nabla s)
  hence "sred_fun
     (apply_subst [(X, swap (rev pi) Unit)] (xs, ys), nabla, [(X, swap (rev pi) Unit)] \<bullet> s,
      True) =
    (P2, nabla', s', B)" by simp
  moreover have not_occurs: "\<not> occurs X Unit" by simp
  ultimately obtain s2 where
    more: "apply_subst [(X, swap (rev pi) Unit)] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
    using "7_2"(1) by auto
  moreover have first: "((Susp pi X, Unit) # xs, ys) \<turnstile> [(X, swap (rev pi) Unit)]
      \<leadsto> apply_subst [(X, swap (rev pi) Unit)] (xs, ys)"
    using not_occurs var_1_sred by blast
  ultimately have "((Susp pi X, Unit) # xs, ys) \<turnstile> s2 \<bullet> [(X, swap (rev pi) Unit)] \<leadsto>\<^sup>* P2"
    using sred_rtc_step by simp
  then show "\<exists>s1. ((Susp pi X, Unit) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
    by auto
next
  case ("7_3" pi X a xs ys nabla s)
  hence "sred_fun
     (apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys), nabla, [(X, swap (rev pi) (Atom a))] \<bullet> s,
      True) =
    (P2, nabla', s', B)" by simp
  moreover have not_occurs: "\<not> occurs X (Atom a)" by simp
  ultimately obtain s2 where
    more: "apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
    using "7_3"(1) by auto
  moreover have first: "((Susp pi X, Atom a) # xs, ys) \<turnstile> [(X, swap (rev pi) (Atom a))]
      \<leadsto> apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys)"
    using not_occurs var_1_sred by blast
  ultimately have "((Susp pi X, Atom a) # xs, ys) \<turnstile> s2 \<bullet> [(X, swap (rev pi) (Atom a))] \<leadsto>\<^sup>* P2"
    using sred_rtc_step by simp
  then show "\<exists>s1. ((Susp pi X, Atom a) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
    by auto
next
  case ("7_4" pi X t1 t2 xs ys nabla s)
  then show "\<exists>s1. ((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
  proof(cases "occurs X (Paar t1 t2)")
    case True
    hence "sred_fun (((Susp pi X, Paar t1 t2) # xs, ys), nabla, s, True) 
      = (((Susp pi X, Paar t1 t2) # xs, ys), nabla, s, False)" by simp
    with "7_4"(2) have "((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> [] \<leadsto>\<^sup>* P2" 
      by auto
    then show "\<exists>s1. ((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  next
    case False
    with "7_4"(2) have "sred_fun
     (apply_subst [(X, swap (rev pi) (Paar t1 t2))] (xs, ys), nabla,
      [(X, swap (rev pi) (Paar t1 t2))] \<bullet> s, True) =
    (P2, nabla', s', B)" by simp
    with "7_4"(1) False obtain s2 where
    more: "apply_subst [(X, swap (rev pi) (Paar t1 t2))] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
      by auto
    moreover have first: "((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> 
        [(X, swap (rev pi) (Paar t1 t2))] \<leadsto> apply_subst [(X, swap (rev pi) (Paar t1 t2))] (xs, ys)"
      using False var_1_sred occurs.simps by force
    ultimately have "((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> 
              s2 \<bullet> [(X, swap (rev pi) (Paar t1 t2))] \<leadsto>\<^sup>* P2"
      using sred_rtc_step by simp
    then show "\<exists>s1. ((Susp pi X, Paar t1 t2) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  qed
next
  case ("7_5" pi X F t xs ys nabla s)
  then show "\<exists>s1. ((Susp pi X, Func F t) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
  proof(cases "occurs X (Func F t)")
    case True
    hence "sred_fun (((Susp pi X, Func F t) # xs, ys), nabla, s, True) 
      = (((Susp pi X, Func F t) # xs, ys), nabla, s, False)" by simp
    with "7_5"(2) have "((Susp pi X, Func F t) # xs, ys) \<turnstile> [] \<leadsto>\<^sup>* P2" 
      by auto
    then show "\<exists>s1. ((Susp pi X, Func F t) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  next
    case False
    with "7_5"(2) have "sred_fun
     (apply_subst [(X, swap (rev pi) (Func F t))] (xs, ys), nabla,
      [(X, swap (rev pi) (Func F t))] \<bullet> s, True) =
    (P2, nabla', s', B)" by simp
    with "7_5"(1) False obtain s2 where
    more: "apply_subst [(X, swap (rev pi) (Func F t))] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
      by auto
    moreover have first: "((Susp pi X, Func F t) # xs, ys) \<turnstile> 
        [(X, swap (rev pi) (Func F t))] \<leadsto> apply_subst [(X, swap (rev pi) (Func F t))] (xs, ys)"
      using False var_1_sred occurs.simps by force
    ultimately have "((Susp pi X, Func F t) # xs, ys) \<turnstile> 
              s2 \<bullet> [(X, swap (rev pi) (Func F t))] \<leadsto>\<^sup>* P2"
      using sred_rtc_step by simp
    then show "\<exists>s1. ((Susp pi X, Func F t) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  qed
next
  case ("8_1" a t pi X xs ys nabla s)
   then show "\<exists>s1. ((Abst a t, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
  proof(cases "occurs X (Abst a t)")
    case True
    hence "sred_fun (((Abst a t, Susp pi X) # xs, ys), nabla, s, True) 
      = (((Abst a t, Susp pi X) # xs, ys), nabla, s, False)" by simp
    with "8_1"(2) have "((Abst a t, Susp pi X) # xs, ys) \<turnstile> [] \<leadsto>\<^sup>* P2" 
      by auto
    then show "\<exists>s1. ((Abst a t, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  next
    case False
    with "8_1"(2) have "sred_fun
     (apply_subst [(X, swap (rev pi) (Abst a t))] (xs, ys), nabla,
      [(X, swap (rev pi) (Abst a t))] \<bullet> s, True) =
    (P2, nabla', s', B)" by simp
    with "8_1"(1) False obtain s2 where
    more: "apply_subst [(X, swap (rev pi) (Abst a t))] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
      by auto
    moreover have first: "((Abst a t, Susp pi X) # xs, ys) \<turnstile> 
        [(X, swap (rev pi) (Abst a t))] \<leadsto> apply_subst [(X, swap (rev pi) (Abst a t))] (xs, ys)"
      using False var_2_sred occurs.simps by force
    ultimately have "((Abst a t, Susp pi X) # xs, ys) \<turnstile> 
              s2 \<bullet> [(X, swap (rev pi) (Abst a t))] \<leadsto>\<^sup>* P2"
      using sred_rtc_step by simp
    then show "\<exists>s1. ((Abst a t, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  qed
next
  case ("8_2" pi X xs ys nabla s)
  hence "sred_fun
     (apply_subst [(X, swap (rev pi) Unit)] (xs, ys), nabla, [(X, swap (rev pi) Unit)] \<bullet> s,
      True) =
    (P2, nabla', s', B)" by simp
  moreover have not_occurs: "\<not> occurs X Unit" by simp
  ultimately obtain s2 where
    more: "apply_subst [(X, swap (rev pi) Unit)] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
    using "8_2"(1) by auto
  moreover have first: "((Unit, Susp pi X) # xs, ys) \<turnstile> [(X, swap (rev pi) Unit)]
      \<leadsto> apply_subst [(X, swap (rev pi) Unit)] (xs, ys)"
    using not_occurs var_2_sred by blast
  ultimately have "((Unit, Susp pi X) # xs, ys) \<turnstile> s2 \<bullet> [(X, swap (rev pi) Unit)] \<leadsto>\<^sup>* P2"
    using sred_rtc_step by simp
  then show "\<exists>s1. ((Unit, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
    by auto
next
  case ("8_3" a pi X xs ys nabla s)
  hence "sred_fun
     (apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys), nabla, [(X, swap (rev pi) (Atom a))] \<bullet> s,
      True) =
    (P2, nabla', s', B)" by simp
  moreover have not_occurs: "\<not> occurs X (Atom a)" by simp
  ultimately obtain s2 where
    more: "apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
    using "8_3"(1) by auto
  moreover have first: "((Atom a, Susp pi X) # xs, ys) \<turnstile> [(X, swap (rev pi) (Atom a))]
      \<leadsto> apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys)"
    using not_occurs var_2_sred by blast
  ultimately have "((Atom a, Susp pi X) # xs, ys) \<turnstile> s2 \<bullet> [(X, swap (rev pi) (Atom a))] \<leadsto>\<^sup>* P2"
    using sred_rtc_step by simp
  then show "\<exists>s1. ((Atom a, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
    by auto
next
  case ("8_4" t1 t2 pi X xs ys nabla s)
  then show "\<exists>s1. ((Paar t1 t2, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
  proof(cases "occurs X (Paar t1 t2)")
    case True
    hence "sred_fun (((Paar t1 t2, Susp pi X) # xs, ys), nabla, s, True) 
      = (((Paar t1 t2, Susp pi X) # xs, ys), nabla, s, False)" by simp
    with "8_4"(2) have "((Paar t1 t2, Susp pi X) # xs, ys) \<turnstile> [] \<leadsto>\<^sup>* P2" 
      by auto
    then show "\<exists>s1. ((Paar t1 t2, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  next
    case False
    with "8_4"(2) have "sred_fun
     (apply_subst [(X, swap (rev pi) (Paar t1 t2))] (xs, ys), nabla,
      [(X, swap (rev pi) (Paar t1 t2))] \<bullet> s, True) =
    (P2, nabla', s', B)" by simp
    with "8_4"(1) False obtain s2 where
    more: "apply_subst [(X, swap (rev pi) (Paar t1 t2))] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
      by auto
    moreover have first: "((Paar t1 t2, Susp pi X) # xs, ys) \<turnstile> 
        [(X, swap (rev pi) (Paar t1 t2))] \<leadsto> apply_subst [(X, swap (rev pi) (Paar t1 t2))] (xs, ys)"
      using False var_2_sred occurs.simps by force
    ultimately have "((Paar t1 t2, Susp pi X) # xs, ys) \<turnstile> 
              s2 \<bullet> [(X, swap (rev pi) (Paar t1 t2))] \<leadsto>\<^sup>* P2"
      using sred_rtc_step by simp
    then show "\<exists>s1. ((Paar t1 t2, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  qed
next
  case ("8_5" F t pi X xs ys nabla s)
  then show "\<exists>s1. ((Func F t, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2"
  proof(cases "occurs X (Func F t)")
    case True
    hence "sred_fun (((Func F t, Susp pi X) # xs, ys), nabla, s, True) 
      = (((Func F t, Susp pi X) # xs, ys), nabla, s, False)" by simp
    with "8_5"(2) have "((Func F t, Susp pi X) # xs, ys) \<turnstile> [] \<leadsto>\<^sup>* P2" 
      by auto
    then show "\<exists>s1. ((Func F t, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  next
    case False
    with "8_5"(2) have "sred_fun
     (apply_subst [(X, swap (rev pi) (Func F t))] (xs, ys), nabla,
      [(X, swap (rev pi) (Func F t))] \<bullet> s, True) =
    (P2, nabla', s', B)" by simp
    with "8_5"(1) False obtain s2 where
    more: "apply_subst [(X, swap (rev pi) (Func F t))] (xs, ys) \<turnstile> s2 \<leadsto>\<^sup>* P2"
      by auto
    moreover have first: "((Func F t, Susp pi X) # xs, ys) \<turnstile> 
        [(X, swap (rev pi) (Func F t))] \<leadsto> apply_subst [(X, swap (rev pi) (Func F t))] (xs, ys)"
      using False var_2_sred occurs.simps by force
    ultimately have "((Func F t, Susp pi X) # xs, ys) \<turnstile> 
              s2 \<bullet> [(X, swap (rev pi) (Func F t))] \<leadsto>\<^sup>* P2"
      using sred_rtc_step by simp
    then show "\<exists>s1. ((Func F t, Susp pi X) # xs, ys) \<turnstile> s1 \<leadsto>\<^sup>* P2" 
      by auto
  qed
qed (auto)



lemma sred_to_sred_fun:
  assumes "P1 \<turnstile> s \<leadsto> P2"
  shows  "sred_fun (P1, nabla, s2, True) = sred_fun (P2, nabla, s \<bullet> s2, True)"
proof(induct rule: s_red.induct[OF assms])
  case (8 X t pi xs ys)
  then show ?case
    by (induct t, auto)
next
  case (9 X t pi xs ys)
  then show ?case
  proof(induct t)
    case (Susp pi' Y)
    then show ?case sorry
  qed (auto)
qed(simp_all)

(*pi' Y \<approx> pi X \<Rightarrow> Y \<rightarrow> (pi'^-1 \<bullet> pi) X
[X \<rightarrow> swap (rev pi) (Susp pi' Y))]
*)


lemma sred_fun_completeness: 
  assumes "P1 \<turnstile> s \<leadsto>\<^sup>* P2" and "P1 \<noteq> P2"
  shows "\<exists>s1 B. sred_fun (P1, nabla, s2, True) = (P2, nabla, s1, B) 
         \<and> (nabla \<Turnstile> subst (s \<bullet> s2) \<approx> subst s1)"
  using assms
proof(induct rule: sred_rtc.induct[OF assms(1)])
  case (1 P1)
  then show ?case by simp
next
  case (2 P1 s P2 s' P3)
  then show ?case
  proof(cases "P2 = P3")
    case True
    with 2(2) have "s' = []"
      using sred_rtc_no_cycle by simp
    moreover with 2(1) True have
     "sred_fun (P1, nabla, s2, True) = sred_fun (P3, nabla, s \<bullet> s2, True)"
      using sred_to_sred_fun by simp
    then show ?thesis sorry
  next
    case False
    then obtain s1 B where 
      "sred_fun (P2, nabla, s2, True) = (P3, nabla, s1, B)"
      "nabla \<Turnstile> subst (s' \<bullet> s2) \<approx> subst s1"
      using 2(2,3) by auto

    then show ?thesis sorry
  qed
qed*)



function (sequential) cred_fun:: "(problem_type \<times> fresh_envs \<times> substs \<times> bool) \<Rightarrow> (problem_type \<times> fresh_envs \<times> substs \<times> bool)" 
  where
"cred_fun ((xs, (a \<sharp>? Unit)#ys), nabla, s, B) = cred_fun ((xs, ys), nabla, s, B)" |
"cred_fun ((xs, (a \<sharp>? Paar t1 t2)#ys), nabla, s, B) = cred_fun ((xs, (a\<sharp>?t1)#(a\<sharp>?t2)#ys), nabla, s, B)" |
"cred_fun ((xs, (a \<sharp>? Func F t)#ys), nabla, s, B) = cred_fun ((xs, (a\<sharp>?t)#ys), nabla, s, B)" |
"cred_fun ((xs, (a \<sharp>? Abst b t)#ys), nabla, s, B) = (if a = b then
                                                      cred_fun ((xs, ys), nabla, s, B)
                                                    else
                                                      cred_fun ((xs, (a\<sharp>?t)#ys), nabla, s, B))" |
"cred_fun ((xs, (a \<sharp>? Atom b)#ys), nabla, s, B) = (if a = b then
                                                      ((xs, (a \<sharp>? Atom a)#ys), nabla, s, False)
                                                    else
                                                      cred_fun ((xs, ys), nabla, s, B))" |
"cred_fun ((xs, (a \<sharp>? Susp pi X)#ys), nabla, s, B) = cred_fun ((xs, ys), {((swapas (rev pi) a),X)}\<union>nabla, s, B)" |
"cred_fun ((xs, []), nabla, s, B) = ((xs, []), nabla, s, B)"
  by pat_completeness auto

termination by (relation rank_fun, unfold rank_fun_def, auto)

lemma cred_fun_sound:
  assumes "fst P1 = []"
    and "cred_fun (P1, nabla, s, True) = (P2, nabla', s, B)"
  shows "\<exists> nabla1. P1 \<turnstile> nabla1 \<rightarrow>\<^sup>* P2"
  using assms
proof(induction "(P1, nabla, s, True)"  arbitrary: P1 nabla s rule: cred_fun.induct)
  case (4 xs a b t ys nabla s)
  then show "\<exists>nabla1. (xs, (a, Abst b t) # ys) \<turnstile> nabla1 \<rightarrow>\<^sup>* P2"
    by (cases "a = b", auto)
next
  case (5 xs a b ys nabla s)
  then show "\<exists>nabla1. (xs, (a, Atom b) # ys) \<turnstile> nabla1 \<rightarrow>\<^sup>* P2"
    by(cases "a = b", auto) 
qed (auto)

lemma cred_to_cred_fun: 
  assumes "P1 \<turnstile> nabla \<rightarrow> P2"
  shows "cred_fun (P1, nabla1, s, True) = cred_fun (P2, nabla \<union> nabla1, s, True)"
  by (induct rule: c_red.induct[OF assms], auto)
  

lemma cred_fun_completeness:
  assumes "P1 \<turnstile> nabla \<rightarrow>\<^sup>* P2" and "P1 \<noteq> P2"
  shows "\<exists> nabla1 B. cred_fun (P1, nabla2, s, True) = (P2, nabla1, s, B)"
  using assms
proof(induct  rule: cred_rtc.induct[OF assms(1)])
  case (1 P1)
  then show ?case by simp
next
  case (2 P1 nabla1 P2 nabla2 P3)
  then show ?case
  proof(cases "P2 = P3")
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed

(*show these lemmas

next steps:
0. add nabla in the sred_fun (DONE)
1. define the function for freshness (cred_fun) (DONE)
2. prove termination (DONE)
3. prove equivalence
4. define the unif computable function that takes as input a problem and calls the functions
sred_fun and cred_fun
5. prove termination of unif*)







(*<*)
end
(*>*)