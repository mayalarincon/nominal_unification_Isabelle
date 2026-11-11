(*<*)
theory NU_Examples
  imports NU_Computable_Completeness
begin
(*>*)

section \<open>Executable examples\<close>

subsection \<open>Equations\<close>

text \<open>\<open>a \<approx>? a\<close>: solvable with the empty substitution: \<open>Some ({}, [])\<close>.\<close>
value "nomu_unify ([Atom ''a'' \<approx>? Atom ''a''], [])"

text \<open>\<open>a \<approx>? b\<close>: different atoms, no solution: \<open>None\<close>.\<close>
value "nomu_unify ([Atom ''a'' \<approx>? Atom ''b''], [])"

text \<open>\<open>X \<approx>? a\<close>: solution \<open>X \<mapsto> a\<close>.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Atom ''a''], [])"

text \<open>\<open>(a b)\<cdot>X \<approx>? a\<close>: solution \<open>X \<mapsto> (a b)\<cdot>a = b\<close>.\<close>
value "nomu_unify ([Susp [(''a'', ''b'')] ''X'' \<approx>? Atom ''a''], [])"

text \<open>\<open>\<langle>X, a\<rangle> \<approx>? \<langle>b, Y\<rangle>\<close>: solution \<open>X \<mapsto> b, Y \<mapsto> a\<close>.\<close>
value "nomu_unify ([Paar (Susp [] ''X'') (Atom ''a'') \<approx>? Paar (Atom ''b'') (Susp [] ''Y'')], [])"

text \<open>\<open>f X \<approx>? g a\<close>: different function symbols, no solution: \<open>None\<close>.\<close>
value "nomu_unify ([Func ''f'' (Susp [] ''X'') \<approx>? Func ''g'' (Atom ''a'')], [])"

text \<open>\<open>X \<approx>? f X\<close>: occurs check fails, no solution: \<open>None\<close>.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Func ''f'' (Susp [] ''X'')], [])"

subsection \<open>Abstractions\<close>

text \<open>\<open>[a]a \<approx>? [b]b\<close>: \<open>\<alpha>\<close>-equivalent, empty substitution: \<open>Some ({}, [])\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Atom ''a'') \<approx>? Abst ''b'' (Atom ''b'')], [])"

text \<open>\<open>[a]b \<approx>? [b]a\<close>: not \<open>\<alpha>\<close>-equivalent, no solution: \<open>None\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Atom ''b'') \<approx>? Abst ''b'' (Atom ''a'')], [])"

text \<open>\<open>[a]X \<approx>? [b]b\<close>: solution \<open>X \<mapsto> a\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Susp [] ''X'') \<approx>? Abst ''b'' (Atom ''b'')], [])"

text \<open>\<open>[a]X \<approx>? [b]X\<close>: empty substitution under the freshness context \<open>a # X, b # X\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Susp [] ''X'') \<approx>? Abst ''b'' (Susp [] ''X'')], [])"

text \<open>\<open>[a][b]\<langle>X, b\<rangle> \<approx>? [b][a]\<langle>a, X\<rangle>\<close>: reduces to \<open>X \<approx>? b\<close> and \<open>b \<approx>? a\<close>, no solution: \<open>None\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Abst ''b'' (Paar (Susp [] ''X'') (Atom ''b''))) \<approx>?
                    Abst ''b'' (Abst ''a'' (Paar (Atom ''a'') (Susp [] ''X'')))], [])"

subsection \<open>Freshness problems\<close>

text \<open>\<open>a #? [a]X\<close>: \<open>a\<close> is bound, solvable: \<open>Some ({}, [])\<close>.\<close>
value "nomu_unify ([], [''a'' \<sharp>? Abst ''a'' (Susp [] ''X'')])"

text \<open>\<open>a #? f b\<close>: solvable: \<open>Some ({}, [])\<close>.\<close>
value "nomu_unify ([], [''a'' \<sharp>? Func ''f'' (Atom ''b'')])"

text \<open>\<open>a #? \<langle>a, b\<rangle>\<close>: reduces to \<open>a #? a\<close>, no solution: \<open>None\<close>.\<close>
value "nomu_unify ([], [''a'' \<sharp>? Paar (Atom ''a'') (Atom ''b'')])"

text \<open>\<open>a #? (a b)\<cdot>X\<close>: solvable under the freshness context \<open>b # X\<close>.\<close>
value "nomu_unify ([], [''a'' \<sharp>? Susp [(''a'', ''b'')] ''X''])"

subsection \<open>Mixed problems\<close>

text \<open>\<open>X \<approx>? [a]Y,  a #? X\<close>: solution \<open>X \<mapsto> [a]Y\<close>; the constraint \<open>a #? [a]Y\<close> holds.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Abst ''a'' (Susp [] ''Y'')], [''a'' \<sharp>? Susp [] ''X''])"

text \<open>\<open>X \<approx>? a,  a #? X\<close>: after \<open>X \<mapsto> a\<close> the constraint becomes \<open>a #? a\<close>, no solution: \<open>None\<close>.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Atom ''a''], [''a'' \<sharp>? Susp [] ''X''])"

(*<*)
end
(*>*)
