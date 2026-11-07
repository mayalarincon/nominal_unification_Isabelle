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

text\<open>Whenever cred_fun succeeds, the snd (freshness) list of the resulting problem is empty:
all freshness problems have been solved.\<close>

lemma cred_fun_some_snd_empty:
  assumes "cred_fun (P, nabla, s) = Some (P', nabla', s')"
  shows "snd P' = []"
  using assms by (induct "(P, nabla, s)" arbitrary: P nabla s P' nabla' s' rule: cred_fun.induct, auto split: if_splits)


(*<*)
end
(*>*)
