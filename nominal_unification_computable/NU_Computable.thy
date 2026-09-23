(*<*)
theory NU_Computable
  imports NU_Completeness
begin
(*>*)


text\<open>Option-typed version of sred_fun. The boolean B success flag of the
original function is replaced by the None/Some structure of the option type,
so the state tuple does not need the boolean component anymore. Failure cases
of the original (returning the stuck state with False) now return None.\<close>

definition rank_fun :: "(((((trm \<times> trm) list \<times> (char list \<times> trm) list) \<times> fresh_envs \<times> substs) \<times>
      ((trm \<times> trm) list \<times> (char list \<times> trm) list) \<times> fresh_envs \<times> substs)) set" where
"rank_fun =
  measures [
    \<lambda>((eprobs, fprobs), s). card (vars_eprobs eprobs),
    \<lambda>((eprobs, fprobs), s). size_eprobs eprobs,
    \<lambda>((eprobs, fprobs), s). size_fprobs fprobs
  ]"

lemma wf_rank_fun:
  shows "wf rank_fun"
  unfolding rank_fun_def by simp

lemma unit_rank_fun:
  shows "(((xs, ys), nabla, s), ((Unit, Unit) # xs, ys), nabla, s) \<in> rank_fun"
  unfolding rank_fun_def by simp

lemma paar_rank_fun:
  shows "((((t1, s1) # (t2, s2) # xs, ys), nabla, s), ((Paar t1 t2, Paar s1 s2) # xs, ys), nabla, s) \<in> rank_fun"
proof-
 let ?vars = "vars_trm s1 \<union> vars_trm s2 \<union> vars_trm t1 \<union> vars_trm t2 \<union> vars_eprobs xs"
    and ?size = "size_trm t1 + size_trm t2 + size_trm s1 + size_trm s2 + size_eprobs xs"
 have "vars_eprobs ((Paar t1 t2, Paar s1 s2) # xs) = ?vars"
   unfolding vars_eprobs.simps vars_trm.simps by auto
  moreover have "size_eprobs ((Paar t1 t2, Paar s1 s2) # xs) = 2 + ?size"
    unfolding size_eprobs.simps using size_trm.simps(6) by auto
  have "vars_eprobs ((t1, s1) # (t2, s2) # xs) = ?vars"
    unfolding vars_eprobs.simps by auto
  moreover have  "size_eprobs ((t1, s1) # (t2, s2) # xs) = ?size"
    unfolding size_eprobs.simps by simp
  ultimately have 
    "size_eprobs ((t1, s1) # (t2, s2) # xs) < size_eprobs ((Paar t1 t2, Paar s1 s2) # xs)"
    "card (vars_eprobs ((t1, s1) # (t2, s2) # xs)) = card (vars_eprobs ((Paar t1 t2, Paar s1 s2) # xs))"
    by simp+
  thus ?thesis unfolding rank_fun_def by simp
qed

lemma func_rank_fun:
  shows "((((t1, t2) # xs, ys), nabla, s), ((Func F t1, Func F t2) # xs, ys), nabla, s) \<in> rank_fun"
  unfolding rank_fun_def by simp

lemma atom_rank_fun:
   shows "(((xs, ys), nabla, s), ((Atom a, Atom a) # xs, ys), nabla, s) \<in> rank_fun"
  unfolding rank_fun_def by simp

lemma abst_aa_rank_fun:
  shows "((((t1, t2) # xs, ys), nabla, s), ((Abst a t1, Abst a t2) # xs, ys), nabla, s) \<in> rank_fun"
  unfolding rank_fun_def by auto

lemma abst_ab_rank_fun:
  assumes "a \<noteq> b"
  shows "((((t1, swap [(a, b)] t2) # xs, (a, t2) # ys), nabla, s), ((Abst a t1, Abst b t2) # xs, ys), nabla, s) \<in> rank_fun"
  using assms vars_swap unfolding rank_fun_def by simp

lemma susp_rank_fun:
  assumes "X = Y"
  shows "(((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), nabla, s),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), nabla, s)
       \<in> rank_fun"
proof-
   have vars: "vars_eprobs ((Susp pi1 X, Susp pi2 Y) # xs) = {X} \<union> vars_eprobs xs" and
          size: "size_eprobs ((Susp pi1 X, Susp pi2 Y) # xs) = 2 + size_eprobs xs"
     using assms unfolding vars_eprobs.simps size_eprobs.simps by simp+
    have size_leq: "size_eprobs xs < size_eprobs ((Susp pi1 Y, Susp pi2 Y) # xs)"
      by simp
    have "(((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), nabla, s),
        ((Susp pi1 X, Susp pi2 Y) # xs, ys), nabla, s)
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

lemma var_left_rank_fun:
  assumes "\<not> occurs X t"
  shows "((apply_subst [(X, swap (rev pi) t)] (xs, ys), nabla, [(X, swap (rev pi) t)] \<bullet> s),
         ((Susp pi X, t) # xs, ys), nabla, s)
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

lemma var_right_rank_fun:
  assumes "\<not> occurs X t"
  shows "((apply_subst [(X, swap (rev pi) t)] (xs, ys), nabla, [(X, swap (rev pi) t)] \<bullet> s),
        ((t, Susp pi X) # xs, ys), nabla, s)
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

function sred_fun :: "(problem_type \<times> fresh_envs \<times> substs) \<Rightarrow> (problem_type \<times> fresh_envs \<times> substs) option" where
"sred_fun (([], ys), nabla, s) = Some (([], ys), nabla, s)" |
"sred_fun (((t1 \<approx>? t2) # xs, ys), nabla, s) =
  (case t1 of
    Unit \<Rightarrow> (case t2 of
               Unit \<Rightarrow> sred_fun ((xs, ys), nabla, s)
             | Susp pi X \<Rightarrow> sred_fun (apply_subst [(X, swap (rev pi) Unit)] (xs, ys),
                                              nabla, [(X, swap (rev pi) Unit)] \<bullet> s)
             | _ \<Rightarrow> None)
   | Paar u1 u2 \<Rightarrow> (case t2 of
                      Paar v1 v2 \<Rightarrow> sred_fun (((u1 \<approx>? v1) # (u2 \<approx>? v2) # xs, ys), nabla, s)
                    | Susp pi X \<Rightarrow>
                        if \<not> occurs X (Paar u1 u2)
                        then sred_fun (apply_subst [(X, swap (rev pi) (Paar u1 u2))] (xs, ys),
                                            nabla, [(X, swap (rev pi) (Paar u1 u2))] \<bullet> s)
                        else None
                    | _ \<Rightarrow> None)
   | Func F u \<Rightarrow> (case t2 of
                     Func G v \<Rightarrow> if F = G
                                  then sred_fun (((u \<approx>? v) # xs, ys), nabla, s)
                                  else None
                   | Susp pi X \<Rightarrow>
                       if \<not> occurs X (Func F u)
                       then sred_fun (apply_subst [(X, swap (rev pi) (Func F u))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Func F u))] \<bullet> s)
                       else None
                   | _ \<Rightarrow> None)
   | Abst a u \<Rightarrow> (case t2 of
                    Abst b v \<Rightarrow> if a = b
                                 then sred_fun (((u \<approx>? v) # xs, ys), nabla, s)
                                 else sred_fun (((u \<approx>? swap [(a, b)] v) # xs, (a \<sharp>? v) # ys), nabla, s)
                  | Susp pi X \<Rightarrow>
                      if \<not> occurs X (Abst a u)
                      then sred_fun (apply_subst [(X, swap (rev pi) (Abst a u))] (xs, ys),
                                          nabla, [(X, swap (rev pi) (Abst a u))] \<bullet> s)
                      else None
                  | _ \<Rightarrow> None)
   | Atom a \<Rightarrow> (case t2 of
                  Atom b \<Rightarrow> if a = b then sred_fun ((xs, ys), nabla, s) else None
                | Susp pi X \<Rightarrow> sred_fun (apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys),
                                                nabla, [(X, swap (rev pi) (Atom a))] \<bullet> s)
                | _ \<Rightarrow> None)
   | Susp pi X \<Rightarrow> (case t2 of
                     Unit \<Rightarrow> sred_fun (apply_subst [(X, swap (rev pi) Unit)] (xs, ys),
                                            nabla, [(X, swap (rev pi) Unit)] \<bullet> s)
                   | Atom a \<Rightarrow> sred_fun (apply_subst [(X, swap (rev pi) (Atom a))] (xs, ys),
                                              nabla, [(X, swap (rev pi) (Atom a))] \<bullet> s)
                   | Paar v1 v2 \<Rightarrow>
                       if \<not> occurs X (Paar v1 v2)
                       then sred_fun (apply_subst [(X, swap (rev pi) (Paar v1 v2))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Paar v1 v2))] \<bullet> s)
                       else None
                   | Func G v \<Rightarrow>
                       if \<not> occurs X (Func G v)
                       then sred_fun (apply_subst [(X, swap (rev pi) (Func G v))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Func G v))] \<bullet> s)
                       else None
                   | Abst a v \<Rightarrow>
                       if \<not> occurs X (Abst a v)
                       then sred_fun (apply_subst [(X, swap (rev pi) (Abst a v))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Abst a v))] \<bullet> s)
                       else None
                   | Susp pi2 Y \<Rightarrow>
                       if X = Y
                       then sred_fun ((xs, map (\<lambda>a. a \<sharp>? Susp [] X) (ds_list pi pi2) @ ys), nabla, s)
                       else sred_fun (apply_subst [(X, swap (rev pi) (Susp pi2 Y))] (xs, ys),
                                           nabla, [(X, swap (rev pi) (Susp pi2 Y))] \<bullet> s)))"
by pat_completeness auto

termination sred_fun
proof(relation rank_fun, auto)
  show "wf rank_fun"
    unfolding rank_fun_def by simp
next
  fix xs ys nabla s t1 a t2
  show "((((t1, t2) # xs, ys), nabla, s), ((Abst a t1, Abst a t2) # xs, ys), nabla, s) \<in> rank_fun"
    using abst_aa_rank_fun by simp
next
  fix xs :: "(trm \<times> trm) list"
    and ys :: "(string \<times> trm) list"
    and nabla s and a b :: string and t1 t2 :: trm
  assume "a \<noteq> b"
  show "((((t1, swap [(a, b)] t2) # xs, (a, t2) # ys), nabla, s),
        ((Abst a t1, Abst b t2) # xs, ys), nabla, s)
       \<in> rank_fun"
    using abst_ab_rank_fun[OF \<open>a \<noteq> b\<close>] by simp
next
  fix xs :: "(trm \<times> trm) list"
    and ys :: "(string \<times> trm) list"
    and nabla s pi X t1 and a :: string
  assume "\<not> occurs X t1"
  hence "\<not> occurs X (Abst a t1)" by simp
  thus "((apply_subst [(X, Abst (swapas (rev pi) a) (swap (rev pi) t1))] (xs, ys), nabla,
         [(X, Abst (swapas (rev pi) a) (swap (rev pi) t1))] \<bullet> s),
        ((Abst a t1, Susp pi X) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_right_rank_fun[OF \<open>\<not> occurs X (Abst a t1)\<close>, of pi xs ys] by auto
next
  fix xs :: "(trm \<times> trm) list"
    and ys :: "(string \<times> trm) list"
    and nabla s pi X t1 and a :: string
  assume "\<not> occurs X t1"
  hence "\<not> occurs X (Abst a t1)" by simp
  show "((apply_subst [(X, Abst (swapas (rev pi) a) (swap (rev pi) t1))] (xs, ys), nabla,
         [(X, Abst (swapas (rev pi) a) (swap (rev pi) t1))] \<bullet> s),
        ((Susp pi X, Abst a t1) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_left_rank_fun[OF \<open>\<not> occurs X (Abst a t1)\<close>, of pi xs ys] by auto
next
  fix xs ys nabla s pi1 pi2 X
  show "(((xs, map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys), nabla, s),
        ((Susp pi1 X, Susp pi2 X) # xs, ys), nabla, s)
       \<in> rank_fun"
    using susp_rank_fun by simp
next
  fix xs ys nabla s pi X pi' and Y :: string
  assume "X \<noteq> Y"
  have "\<not> occurs X (Susp pi' Y)"
    using occurs.simps(3) \<open>X \<noteq> Y\<close> by simp
  thus "((apply_subst [(X, Susp (rev pi @ pi') Y)] (xs, ys), nabla, [(X, Susp (rev pi @ pi') Y)] \<bullet> s),
        ((Susp pi X, Susp pi' Y) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_left_rank_fun[OF \<open>\<not> occurs X (Susp pi' Y)\<close>, of pi xs ys] by auto
next
  fix xs ys nabla s pi X
  have "\<not> occurs X Unit" by simp
  thus "((apply_subst [(X, Unit)] (xs, ys), nabla, [(X, Unit)] \<bullet> s), ((Susp pi X, Unit) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_left_rank_fun[of X Unit pi xs ys nabla s] by auto
next
  fix xs ys nabla s pi X a
  have "\<not> occurs X (Atom a)" by simp
  thus "((apply_subst [(X, Atom (swapas (rev pi) a))] (xs, ys), nabla, [(X, Atom (swapas (rev pi) a))] \<bullet> s),
        ((Susp pi X, Atom a) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_left_rank_fun[OF \<open>\<not> occurs X (Atom a)\<close>, of pi xs ys] by auto
next
  fix xs ys nabla s pi X t1 t2
  assume "\<not> (if occurs X t1 then True else occurs X t2)"
  hence "\<not> occurs X (Paar t1 t2)" by simp
  thus "((apply_subst [(X, Paar (swap (rev pi) t1) (swap (rev pi) t2))] (xs, ys), nabla,
         [(X, Paar (swap (rev pi) t1) (swap (rev pi) t2))] \<bullet> s),
        ((Susp pi X, Paar t1 t2) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_left_rank_fun[OF \<open>\<not> occurs X (Paar t1 t2)\<close>, of pi xs ys] by auto
next
  fix xs ys nabla s pi X F t
  assume "\<not> occurs X t"
  hence "\<not> occurs X (Func F t)" by simp
  thus "((apply_subst [(X, Func F (swap (rev pi) t))] (xs, ys), nabla,
         [(X, Func F (swap (rev pi) t))] \<bullet> s),
        ((Susp pi X, Func F t) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_left_rank_fun[OF \<open>\<not> occurs X (Func F t)\<close>, of pi xs ys] by auto
next
  fix xs ys nabla s pi X
  have "\<not> occurs X Unit" by simp
  thus "((apply_subst [(X, Unit)] (xs, ys), nabla, [(X, Unit)] \<bullet> s), ((Unit, Susp pi X) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_right_rank_fun[of X Unit pi xs ys nabla s] by auto
next
  fix xs ys nabla s
  show "(((xs, ys), nabla, s), ((Unit, Unit) # xs, ys), nabla, s) \<in> rank_fun"
    using unit_rank_fun by simp
next
  fix xs ys nabla s pi X a
  have "\<not> occurs X (Atom a)" by simp
  thus "((apply_subst [(X, Atom (swapas (rev pi) a))] (xs, ys), nabla, [(X, Atom (swapas (rev pi) a))] \<bullet> s),
        ((Atom a, Susp pi X) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_right_rank_fun[OF \<open>\<not> occurs X (Atom a)\<close>, of pi xs ys] by auto
next
  fix xs ys nabla s a
  show "(((xs, ys), nabla, s), ((Atom a, Atom a) # xs, ys), nabla, s) \<in> rank_fun"
    using atom_rank_fun by simp
next
  fix xs ys nabla s pi X t1 t2
  assume "\<not> (if occurs X t1 then True else occurs X t2)"
  hence "\<not> occurs X (Paar t1 t2)" by simp
  thus "((apply_subst [(X, Paar (swap (rev pi) t1) (swap (rev pi) t2))] (xs, ys), nabla,
         [(X, Paar (swap (rev pi) t1) (swap (rev pi) t2))] \<bullet> s),
        ((Paar t1 t2, Susp pi X) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_right_rank_fun[OF \<open>\<not> occurs X (Paar t1 t2)\<close>, of pi xs ys] by auto
next
  fix xs ys nabla s t1 t2 s1 s2
  show "((((t1, s1) # (t2, s2) # xs, ys), nabla, s), ((Paar t1 t2, Paar s1 s2) # xs, ys), nabla, s)
       \<in> rank_fun"
    using paar_rank_fun by simp
next
  fix xs ys nabla s pi X F t
  assume "\<not> occurs X t"
  hence "\<not> occurs X (Func F t)" by simp
  thus "((apply_subst [(X, Func F (swap (rev pi) t))] (xs, ys), nabla, [(X, Func F (swap (rev pi) t))] \<bullet> s),
        ((Func F t, Susp pi X) # xs, ys), nabla, s)
       \<in> rank_fun"
    using var_right_rank_fun[OF \<open>\<not> occurs X (Func F t)\<close>, of pi xs ys] by auto
next
  fix xs ys nabla s F t1 t2
  show "((((t1, t2) # xs, ys), nabla, s), ((Func F t1, Func F t2) # xs, ys), nabla, s) \<in> rank_fun"
    using func_rank_fun by simp
qed


function  cred_fun :: "(problem_type \<times> fresh_envs \<times> substs) \<Rightarrow> (problem_type \<times> fresh_envs \<times> substs) option"
  where
"cred_fun ((xs, (a \<sharp>? Unit)#ys), nabla, s) = cred_fun ((xs, ys), nabla, s)" |
"cred_fun ((xs, (a \<sharp>? Paar t1 t2)#ys), nabla, s) = cred_fun ((xs, (a\<sharp>?t1)#(a\<sharp>?t2)#ys), nabla, s)" |
"cred_fun ((xs, (a \<sharp>? Func F t)#ys), nabla, s) = cred_fun ((xs, (a\<sharp>?t)#ys), nabla, s)" |
"cred_fun ((xs, (a \<sharp>? Abst b t)#ys), nabla, s) = (if a = b then
                                                      cred_fun ((xs, ys), nabla, s)
                                                    else
                                                      cred_fun ((xs, (a\<sharp>?t)#ys), nabla, s))" |
"cred_fun ((xs, (a \<sharp>? Atom b)#ys), nabla, s) = (if a = b then
                                                  None
                                                else
                                                  cred_fun ((xs, ys), nabla, s))" |
"cred_fun ((xs, (a \<sharp>? Susp pi X)#ys), nabla, s) = cred_fun ((xs, ys), {((swapas (rev pi) a),X)}\<union>nabla, s)" |
"cred_fun ((xs, []), nabla, s) = Some ((xs, []), nabla, s)"
  by pat_completeness auto

termination cred_fun
  by (relation "measure (\<lambda>((xs, ys), nabla, s). size_fprobs ys)", auto)

text\<open>Combines sred_fun (equation reductions) and cred_fun (freshness reductions),
mirroring the red_plus relation: equations are solved first, then freshness
constraints.\<close>

fun red_plus_fun :: "(problem_type \<times> fresh_envs \<times> substs) \<Rightarrow> (problem_type \<times> fresh_envs \<times> substs) option" where
"red_plus_fun (P, nabla, s) = (case sred_fun (P, nabla, s) of
                                 Some (([], ys), nabla', s') \<Rightarrow> cred_fun (([],ys), nabla', s')
                               | None \<Rightarrow> None)"

fun nomu_unify :: "problem_type \<Rightarrow> (fresh_envs \<times> substs) option" where
  "nomu_unify P = (case red_plus_fun (P, {}, []) of 
                    Some (([],[]), nabla', s') \<Rightarrow> Some (nabla', s')
                    | None \<Rightarrow> None)"

text\<open>Whenever sred_fun succeeds, the first (equation) list of the resulting problem is empty:
all equations have been solved, only freshness constraints remain.\<close>

lemma sred_fun_some_fst_empty:
  assumes "sred_fun (P, nabla, s) = Some (P', nabla', s')"
  shows "fst P' = []"
  using assms
  proof(induct "(P, nabla, s)" arbitrary: P nabla s P' nabla' s' rule: sred_fun.induct)
    case (1 ys nabla s)
    then show ?case by auto
  next
    case (2 t1 t2 xs ys nabla s)
    note IHs = this
    then show ?case 
    proof (cases t1)
      case Unit
      note h1 = this
      then show ?thesis using IHs by (cases t2, auto split: if_splits)
    next
      case (Abst a t1')
      note h1 = this
      then show ?thesis using IHs by (cases t2, auto split: if_splits)
    next
      case (Susp pi X)
      note h1 = this
      then show ?thesis using IHs by (cases t2, auto split: if_splits)
    next
      case (Atom a)
      note h1 = this
      then show ?thesis using IHs by (cases t2, auto split: if_splits)
    next
      case (Paar t11 t12)
      note h1 = this
      then show ?thesis using IHs by (cases t2, auto split: if_splits)
    next
      case (Func F t1')
      note h1 = this
      then show ?thesis using IHs by (cases t2, auto split: if_splits)
    qed
  qed

text\<open>Whenever cred_fun succeeds, the snd (freshness) list of the resulting problem is empty:
all freshness problems have been solved.\<close>

lemma cred_fun_some_snd_empty:
  assumes "cred_fun (P, nabla, s) = Some (P', nabla', s')"
  shows "snd P' = []"
  using assms by (induct "(P, nabla, s)" arbitrary: P nabla s P' nabla' s' rule: cred_fun.induct, auto split: if_splits)


section \<open>Soundness of the computable algorithm\<close>

text\<open>sred_fun is simulated by the reflexive-transitive closure of the equational reductions.\<close>

lemma sred_rtc_prepend:
  assumes "P1 \<turnstile> s1 \<leadsto> P2" and "P2 \<turnstile> s2 \<leadsto>\<^sup>* P'" and "s' = s2 \<bullet> (s1 \<bullet> s)"
  shows "\<exists>s3. P1 \<turnstile> s3 \<leadsto>\<^sup>* P' \<and> s' = s3 \<bullet> s"
proof-
  have "P1 \<turnstile> (s2 \<bullet> s1) \<leadsto>\<^sup>* P'" "s' = (s2 \<bullet> s1) \<bullet> s"
    using assms comp_assoc by auto
  thus ?thesis by blast
qed

text\<open>One unfolding of sred_fun on a non-empty equation list corresponds to one s_red step.\<close>

lemma ex_sred_stepI:
  assumes "P \<turnstile> \<sigma> \<leadsto> Q" and "sred_fun (Q, nabla, \<sigma> \<bullet> s) = Some r"
  shows "\<exists>\<sigma> Q. P \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = Some r"
  using assms by blast

lemma sred_fun_unfold_step:
  assumes "sred_fun (((t1 \<approx>? t2) # xs, ys), nabla, s) = Some r"
  shows "\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = Some r"
  using assms
  apply (subst (asm) sred_fun.simps(2))
  apply (cases t1; cases t2; auto simp del: sred_fun.simps split_paired_Ex split: if_splits)
  apply ((rule ex_sred_stepI, rule s_red.intros, auto simp del: sred_fun.simps)[1])+
  done

lemma sred_fun_sred_rtc:
  assumes "sred_fun (P, nabla, s) = Some (P', nabla', s')"
  shows "nabla' = nabla \<and> (\<exists>s1. P \<turnstile> s1 \<leadsto>\<^sup>* P' \<and> s' = s1 \<bullet> s)"
  using assms
proof(induct P arbitrary: s rule: wf_induct[OF wf_rank_r])
  case (1 P)
  obtain eqs ys where P_def: "P = (eqs, ys)" by (cases P)
  show ?case
  proof(cases eqs)
    case Nil
    then show ?thesis using 1(2) P_def by force
  next
    case (Cons e xs)
    obtain t1 t2 where e_def: "e = (t1 \<approx>? t2)" by (cases e)
    obtain \<sigma> Q where step: "P \<turnstile> \<sigma> \<leadsto> Q" and rec: "sred_fun (Q, nabla, \<sigma> \<bullet> s) = Some (P', nabla', s')"
      using sred_fun_unfold_step 1(2) unfolding P_def Cons e_def by blast
    have "(Q, P) \<in> rank_r"
      using rank_r_sred[OF step] .
    hence "nabla' = nabla \<and> (\<exists>s1. Q \<turnstile> s1 \<leadsto>\<^sup>* P' \<and> s' = s1 \<bullet> (\<sigma> \<bullet> s))"
      using 1(1) rec by blast
    then show ?thesis
      using sred_rtc_prepend[OF step] by blast
  qed
qed

text\<open>cred_fun is simulated by the reflexive-transitive closure of the freshness reductions.\<close>

lemma cred_rtc_prepend:
  assumes "P1 \<turnstile> n1 \<rightarrow> P2" and "P2 \<turnstile> n2 \<rightarrow>\<^sup>* P'" and "nabla' = n2 \<union> (n1 \<union> nabla)"
  shows "\<exists>n3. P1 \<turnstile> n3 \<rightarrow>\<^sup>* P' \<and> nabla' = n3 \<union> nabla"
proof-
  have "P1 \<turnstile> (n2 \<union> n1) \<rightarrow>\<^sup>* P'" "nabla' = (n2 \<union> n1) \<union> nabla"
    using assms by auto
  thus ?thesis by blast
qed

lemma cred_fun_cred_rtc:
  assumes "cred_fun ((xs, ys), nabla, s) = Some (P', nabla', s')" and "xs = []"
  shows "s' = s \<and> (\<exists>n1. ([], ys) \<turnstile> n1 \<rightarrow>\<^sup>* P' \<and> nabla' = n1 \<union> nabla)"
  using assms
proof(induct "((xs, ys), nabla, s)" arbitrary: xs ys nabla s rule: cred_fun.induct)
  case (1 xs a ys nabla s)
  then show ?case using cred_rtc_prepend[OF unit_cred] by auto
next
  case (2 xs a t1 t2 ys nabla s)
  then show ?case using cred_rtc_prepend[OF paar_cred] by auto
next
  case (3 xs a F t ys nabla s)
  then show ?case using cred_rtc_prepend[OF func_cred] by auto
next
  case (4 xs a b t ys nabla s)
  then show ?case 
    using cred_rtc_prepend[OF abst_aa_cred] cred_rtc_prepend[OF abst_ab_cred]
    by (cases "a = b") auto
next
  case (5 xs a b ys nabla s)
  then show ?case using cred_rtc_prepend[OF atom_cred] by (auto split: if_splits)
next
  case (6 xs a pi X ys nabla s)
  then show ?case using cred_rtc_prepend[OF susp_cred] by auto
next
  case (7 xs nabla s)
  then show ?case by force
qed

lemma cred_fun_some_fst:
  assumes "cred_fun ((xs, ys), nabla, s) = Some (P', nabla', s')"
  shows "fst P' = xs"
  using assms 
  by (induct "((xs, ys), nabla, s)" arbitrary: xs ys nabla s rule: cred_fun.induct, auto split: if_splits)

text\<open>Gluing the closures of the equational and freshness reductions into red_plus.\<close>

lemma sred_rtc_red_plus_append:
  assumes "P1 \<turnstile> s \<leadsto>\<^sup>* P2" and "P2 \<Turnstile> (nabla, []) \<Rightarrow> P3"
  shows "P1 \<Turnstile> (nabla, s) \<Rightarrow> P3"
  using assms by (induct rule: sred_rtc.induct) auto

lemma cred_rtc_red_plus:
  assumes "P1 \<turnstile> nabla \<rightarrow>\<^sup>* P2"
  shows "(P1 = P2 \<and> nabla = {}) \<or> P1 \<Turnstile> (nabla, []) \<Rightarrow> P2"
  using assms
proof(induct rule: cred_rtc.induct)
  case (cred_refl P1)
  then show ?case by simp
next
  case (cred_rtc_step P1 nabla1 P2 nabla2 P3)
  show ?case
  proof(cases "P2 = P3 \<and> nabla2 = {}")
    case True
    then show ?thesis using cred_single[OF cred_rtc_step(1)] by simp
  next
    case False
    hence "P2 \<Turnstile> (nabla2, []) \<Rightarrow> P3" 
      using cred_rtc_step(3) False by auto
    then show ?thesis using cred_step[OF cred_rtc_step(1)] by simp
  qed
qed

text\<open>A successful run of the algorithm corresponds to a sequence of equational reductions 
followed by a sequence of freshness reductions ending in the empty problem.\<close>

lemma nomu_unify_some_rtc:
  assumes "nomu_unify P = Some (nabla, s)"
  shows "\<exists>P3. P \<turnstile> s \<leadsto>\<^sup>* P3 \<and> P3 \<turnstile> nabla \<rightarrow>\<^sup>* ([],[])"
proof-
  obtain R where R: "red_plus_fun (P, {}, []) = Some R"
    using assms by (cases "red_plus_fun (P, {}, [])") auto
  obtain xs ys nabla0 s0 where S: "sred_fun (P, {}, []) = Some ((xs, ys), nabla0, s0)"
    using R by (cases "sred_fun (P, {}, [])") auto
  have "xs = []"
    using sred_fun_some_fst_empty[OF S] by simp
  obtain P1 nabla1 s1 where C: "cred_fun (([], ys), nabla0, s0) = Some (P1, nabla1, s1)"
    using R S \<open>xs = []\<close> by (cases R) auto
  have "P1 = ([],[])"
    using cred_fun_some_fst[OF C] cred_fun_some_snd_empty[OF C] by (cases P1) auto
  hence "nabla1 = nabla" "s1 = s"
    using assms R S C \<open>xs = []\<close> by auto
  obtain s2 where "nabla0 = {}" "P \<turnstile> s2 \<leadsto>\<^sup>* ([], ys)" "s0 = s2"
    using sred_fun_sred_rtc[OF S] \<open>xs = []\<close> by auto
  moreover obtain n where "s1 = s0" "([], ys) \<turnstile> n \<rightarrow>\<^sup>* P1" "nabla1 = n \<union> nabla0"
    using cred_fun_cred_rtc[OF C] by auto
  ultimately show ?thesis
    using \<open>P1 = ([],[])\<close> \<open>nabla1 = nabla\<close> \<open>s1 = s\<close> by auto
qed

text\<open>For a non-trivial problem, a successful run of the algorithm corresponds to a red_plus 
derivation to the empty problem.\<close>

lemma nomu_unify_some_red_plus:
  assumes "nomu_unify P = Some (nabla, s)" and "P \<noteq> ([],[])"
  shows "P \<Turnstile> (nabla, s) \<Rightarrow> ([],[])"
proof-
  obtain P3 where sred: "P \<turnstile> s \<leadsto>\<^sup>* P3" and cred: "P3 \<turnstile> nabla \<rightarrow>\<^sup>* ([],[])"
    using nomu_unify_some_rtc[OF assms(1)] by blast
  show ?thesis
  proof(cases "P3 = ([],[]) \<and> nabla = {}")
    case True
    then show ?thesis 
      using sred_rtc_to_redplus[of P "([],[])" s] sred assms(2) by simp
  next
    case False
    then have "P3 \<Turnstile> (nabla, []) \<Rightarrow> ([],[])" 
      using cred_rtc_red_plus[OF cred] by metis
    then show ?thesis 
      by (rule sred_rtc_red_plus_append[OF sred])
  qed
qed

text\<open>Soundness: whenever the algorithm returns a result, it is an idempotent most general 
unifier of the input problem.\<close>

theorem nomu_unify_sound:
  assumes "nomu_unify P = Some (nabla, s)"
  shows "(nabla, s) \<in> U P \<and> mgu P (nabla, s) \<and> idem (nabla, s)"
proof-
  obtain P3 where sred: "P \<turnstile> s \<leadsto>\<^sup>* P3" and cred: "P3 \<turnstile> nabla \<rightarrow>\<^sup>* ([],[])"
    using nomu_unify_some_rtc[OF assms] by blast
  show ?thesis
  proof(cases "P = ([],[])")
    case True
    have "P3 = P \<and> s = []"
      using sred True by (cases rule: sred_rtc.cases) (auto dest: sred_eqs_not_empty)
    moreover have "nabla = {}"
      using cred True calculation by (cases rule: cred_rtc.cases) (auto elim: c_red.cases)
    ultimately show ?thesis 
      using True subst_equ_refl
      unfolding all_solutions_def mgu_def idem_def ext_subst_def by auto
  next
    case False
    have red: "P \<Turnstile> (nabla, s) \<Rightarrow> ([],[])"
      using nomu_unify_some_red_plus[OF assms False] .
    have "({}, []) \<in> U ([],[])" 
      unfolding all_solutions_def by simp
    hence "({} \<union> nabla, [] \<bullet> s) \<in> U P"
      using P1_from_P2_red_plus[OF red _ ext_subst_id] by blast
    then show ?thesis 
      using mgu[OF red] by simp
  qed
qed

section \<open>Completeness of the computable algorithm\<close>

text\<open>One unfolding of a failing sred_fun either hits a failure pattern or performs an s_red step
after which sred_fun still fails.\<close>

lemma ex_sred_stepI_gen:
  assumes "P \<turnstile> \<sigma> \<leadsto> Q" and "sred_fun (Q, nabla, \<sigma> \<bullet> s) = r"
  shows "\<exists>\<sigma> Q. P \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = r"
  using assms by blast

lemma sred_fun_unfold_none:
  assumes "sred_fun (((t1 \<approx>? t2) # xs, ys), nabla, s) = None"
  shows "fail ((t1 \<approx>? t2) # xs, ys) \<or> 
         (\<exists>\<sigma> Q. ((t1 \<approx>? t2) # xs, ys) \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None)"
  using assms
  apply (subst (asm) sred_fun.simps(2))
  apply (cases t1; cases t2; simp del: sred_fun.simps split_paired_Ex split: if_splits)
  apply (((rule disjI1, ((rule fail.intros(1-16)); blast)) 
        | (rule disjI1, rule fail_sym, ((rule fail.intros(1-16)); blast)) 
        | (rule disjI2, rule ex_sred_stepI_gen, rule s_red.intros, 
           force simp del: sred_fun.simps, force simp del: sred_fun.simps)
        | (rule disjI2, rule ex_sred_stepI_gen, rule s_red.intros, 
           force simp del: sred_fun.simps))[1])+
  done

text\<open>If sred_fun fails, the problem has no solution.\<close>

lemma sred_fun_none_empty:
  assumes "sred_fun (P, nabla, s) = None"
  shows "U P = {}"
  using assms
proof(induct P arbitrary: s rule: wf_induct[OF wf_rank_r])
  case (1 P)
  obtain eqs ys where P_def: "P = (eqs, ys)" by (cases P)
  show ?case
  proof(cases eqs)
    case Nil
    then show ?thesis using 1(2) P_def by simp
  next
    case (Cons e xs)
    obtain t1 t2 where e_def: "e = (t1 \<approx>? t2)" by (cases e)
    have H: "sred_fun (((t1 \<approx>? t2) # xs, ys), nabla, s) = None"
      using 1(2) unfolding P_def Cons e_def .
    have "fail P \<or> (\<exists>\<sigma> Q. P \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None)"
      unfolding P_def Cons e_def by (rule sred_fun_unfold_none[OF H])
    then show ?thesis
    proof
      assume "fail P"
      then show ?thesis using fail_then_empty by simp
    next
      assume "\<exists>\<sigma> Q. P \<turnstile> \<sigma> \<leadsto> Q \<and> sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
      then obtain \<sigma> Q where step: "P \<turnstile> \<sigma> \<leadsto> Q" and rec: "sred_fun (Q, nabla, \<sigma> \<bullet> s) = None"
        by blast
      have "(Q, P) \<in> rank_r"
        using rank_r_sred[OF step] .
      hence "U Q = {}"
        using 1(1) rec by blast
      then show ?thesis 
        using u_empty_sred[OF step] by simp
    qed
  qed
qed

text\<open>If cred_fun fails, the (freshness) problem has no solution.\<close>

lemma cred_fun_none_empty:
  assumes "cred_fun ((xs, ys), nabla, s) = None" and "xs = []"
  shows "U ([], ys) = {}"
  using assms
proof(induct "((xs, ys), nabla, s)" arbitrary: xs ys nabla s rule: cred_fun.induct)
  case (1 xs a ys nabla s)
  then show ?case using u_empty_cred[OF unit_cred] by auto
next
  case (2 xs a t1 t2 ys nabla s)
  then show ?case using u_empty_cred[OF paar_cred] by auto
next
  case (3 xs a F t ys nabla s)
  then show ?case using u_empty_cred[OF func_cred] by auto
next
  case (4 xs a b t ys nabla s)
  then show ?case 
    using u_empty_cred[OF abst_aa_cred] u_empty_cred[OF abst_ab_cred]
    by (cases "a = b") auto
next
  case (5 xs a b ys nabla s)
  then show ?case 
    using u_empty_cred[OF atom_cred] fail_then_empty[OF fail_fresh_atom]
    by (cases "a = b") auto
next
  case (6 xs a pi X ys nabla s)
  then show ?case using u_empty_cred[OF susp_cred] by auto
next
  case (7 xs nabla s)
  then show ?case by simp
qed

lemma u_empty_sred_rtc:
  assumes "P1 \<turnstile> s \<leadsto>\<^sup>* P2" and "U P2 = {}"
  shows "U P1 = {}"
  using assms
proof(induct rule: sred_rtc.induct)
  case (sred_refl P1)
  then show ?case by simp
next
  case (sred_rtc_step P1 s1 P2 s2 P3)
  then have "U P2 = {}" by simp
  then show ?case using u_empty_sred[OF sred_rtc_step(1)] by simp
qed

text\<open>Completeness: whenever the algorithm fails, the problem has no solution.\<close>

theorem nomu_unify_none:
  assumes "nomu_unify P = None"
  shows "U P = {}"
proof(cases "sred_fun (P, {}, [])")
  case None
  then show ?thesis using sred_fun_none_empty by blast
next
  case (Some R)
  then obtain xs ys nabla0 s0 where S: "sred_fun (P, {}, []) = Some ((xs, ys), nabla0, s0)"
    by (cases R) auto
  have "xs = []"
    using sred_fun_some_fst_empty[OF S] by simp
  obtain s1 where rtc: "P \<turnstile> s1 \<leadsto>\<^sup>* ([], ys)"
    using sred_fun_sred_rtc[OF S] \<open>xs = []\<close> by auto
  show ?thesis
  proof(cases "cred_fun (([], ys), nabla0, s0)")
    case None
    then have "U ([], ys) = {}" 
      using cred_fun_none_empty by blast
    then show ?thesis 
      using u_empty_sred_rtc[OF rtc] by simp
  next
    case (Some C)
    then obtain P1 nabla1 s1' where C: "cred_fun (([], ys), nabla0, s0) = Some (P1, nabla1, s1')"
      by (cases C) auto
    have "P1 = ([],[])"
      using cred_fun_some_fst[OF C] cred_fun_some_snd_empty[OF C] by (cases P1) auto
    hence "nomu_unify P = Some (nabla1, s1')"
      using S C \<open>xs = []\<close> by simp
    then show ?thesis using assms by simp
  qed
qed

text\<open>Together with soundness: the algorithm fails exactly on the problems without solutions.\<close>

corollary nomu_unify_none_iff:
  shows "nomu_unify P = None \<longleftrightarrow> U P = {}"
proof
  assume "nomu_unify P = None"
  then show "U P = {}" using nomu_unify_none by simp
next
  assume "U P = {}"
  show "nomu_unify P = None"
  proof(rule ccontr)
    assume "nomu_unify P \<noteq> None"
    then obtain nabla s where "nomu_unify P = Some (nabla, s)" by auto
    then have "(nabla, s) \<in> U P" using nomu_unify_sound by simp
    then show False using \<open>U P = {}\<close> by simp
  qed
qed

text\<open>Completeness in the style of @{thm [source] completeness}: whenever a (non-trivial) 
problem has a solution, the algorithm returns a result that is reached by red_plus and is
a most general unifier.\<close>

theorem nomu_unify_complete:
  assumes "P \<noteq> ([],[])" "U P \<noteq> {}"
  shows "\<exists>nabla s. nomu_unify P = Some (nabla, s) \<and> mgu P (nabla, s) \<and> idem (nabla, s)"
proof-
  obtain nabla s where res: "nomu_unify P = Some (nabla, s)"
    using assms(2) nomu_unify_none_iff by (cases "nomu_unify P") auto
  moreover have "mgu P (nabla, s)" "idem (nabla, s)"
    using nomu_unify_sound[OF res] by simp+
  ultimately show ?thesis using res by blast
qed


(*<*)
end
(*>*)
