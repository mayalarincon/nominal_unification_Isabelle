(*<*)
theory NU_Examples
  imports NU_Computable_Completeness
begin
(*>*)

section \<open>Executable examples\<close>

subsection \<open>Equations\<close>

text \<open>\<open>([a \<approx>? a], []) \<leadsto> ([], [])\<close>. Result: \<open>Some ({}, [])\<close>.\<close>
value "nomu_unify ([Atom ''a'' \<approx>? Atom ''a''], [])"

text \<open>
  \<open>([a \<approx>? b], []) \<leadsto> \<bottom>\<close>

  No rule applies to \<open>a \<approx>? b\<close>, since \<open>a \<noteq> b\<close>.

  Result: \<open>None\<close>.
\<close>
value "nomu_unify ([Atom ''a'' \<approx>? Atom ''b''], [])"

text \<open>\<open>([X \<approx>? a], []) \<turnstile>[X \<mapsto> a] \<leadsto> ([], [])\<close>. Result: \<open>Some ({}, [X \<mapsto> a])\<close>.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Atom ''a''], [])"

text \<open>
  \<open>([(a b)\<cdot>X \<approx>? a], []) \<turnstile>[X \<mapsto> b] \<leadsto> ([], [])\<close>

  Here \<open>(a b)\<^sup>-\<^sup>1\<cdot>a = b\<close>.

  Result: \<open>Some ({}, [X \<mapsto> b])\<close>.
\<close>
value "nomu_unify ([Susp [(''a'', ''b'')] ''X'' \<approx>? Atom ''a''], [])"

text \<open>\<open>([\<langle>X, a\<rangle> \<approx>? \<langle>b, Y\<rangle>], []) \<leadsto> ([X \<approx>? b, a \<approx>? Y], []) \<turnstile>[X \<mapsto> b] \<leadsto> ([a \<approx>? Y], []) \<turnstile>[Y \<mapsto> a] \<leadsto> ([], [])\<close>. Result: \<open>Some ({}, [X \<mapsto> b, Y \<mapsto> a])\<close>.\<close>
value "nomu_unify ([Paar (Susp [] ''X'') (Atom ''a'') \<approx>? Paar (Atom ''b'') (Susp [] ''Y'')], [])"

text \<open>\<open>([f X \<approx>? g a], []) \<leadsto> \<bottom>\<close>. Result: None.\<close>
value "nomu_unify ([Func ''f'' (Susp [] ''X'') \<approx>? Func ''g'' (Atom ''a'')], [])"

text \<open>\<open>([X \<approx>? f X], []) \<leadsto> \<bottom>\<close>. Occurs check: \<open>X\<close> occurs in \<open>f X\<close>.  Result: \<open>None\<close>.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Func ''f'' (Susp [] ''X'')], [])"

subsection \<open>Abstractions\<close>

text \<open>\<open>([[a]a \<approx>? [b]b], []) \<leadsto> ([a \<approx>? (a b)\<cdot>b], [a #? b]) = ([a \<approx>? a], [a #? b]) \<leadsto> ([], [a #? b]) \<rightarrow> ([], [])\<close>. Result: \<open>Some ({}, [])\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Atom ''a'') \<approx>? Abst ''b'' (Atom ''b'')], [])"

text \<open>\<open>([[a]b \<approx>? [b]a], []) \<leadsto> ([b \<approx>? (a b)\<cdot>a], [a #? a]) = ([b \<approx>? b], [a #? a]) \<leadsto> ([], [a #? a]) \<rightarrow> \<bottom>\<close>. Result: \<open>None\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Atom ''b'') \<approx>? Abst ''b'' (Atom ''a'')], [])"

text \<open>\<open>([[a]X \<approx>? [b]b], []) \<leadsto> ([X \<approx>? (a b)\<cdot>b], [a #? b]) = ([X \<approx>? a], [a #? b]) \<turnstile>[X \<mapsto> a] \<leadsto> ([], [a #? b]) \<rightarrow> ([], [])\<close>. Result: \<open>Some ({}, [X \<mapsto> a])\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Susp [] ''X'') \<approx>? Abst ''b'' (Atom ''b'')], [])"

text \<open>\<open>([[a]X \<approx>? [b]X], []) \<leadsto> ([X \<approx>? (a b)\<cdot>X], [a #? X]) \<leadsto> ([], [a #? X, b #? X, a #? X]) \<turnstile>{a # X} \<rightarrow> ([], [b #? X, a #? X]) \<turnstile>{b # X} \<rightarrow> ([], [a #? X]) \<turnstile>{a # X} \<rightarrow> ([], [])\<close>

  Here \<open>ds(id, (a b)) = [a, b]\<close>.

  Result: \<open>Some ({a # X, b # X}, [])\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Susp [] ''X'') \<approx>? Abst ''b'' (Susp [] ''X'')], [])"

text \<open>\<open>([[a][b]\<langle>X, b\<rangle> \<approx>? [b][a]\<langle>a, X\<rangle>], []) \<leadsto> ([[b]\<langle>X, b\<rangle> \<approx>? [b]\<langle>b, (a b)\<cdot>X\<rangle>], [a #? [a]\<langle>a, X\<rangle>]) \<leadsto> ([\<langle>X, b\<rangle> \<approx>? \<langle>b, (a b)\<cdot>X\<rangle>], [a #? [a]\<langle>a, X\<rangle>]) \<leadsto> ([X \<approx>? b, b \<approx>? (a b)\<cdot>X], [a #? [a]\<langle>a, X\<rangle>]) \<turnstile>[X \<mapsto> b] \<leadsto> ([b \<approx>? (a b)\<cdot>b], [a #? [a]\<langle>a, b\<rangle>]) = ([b \<approx>? a], [a #? [a]\<langle>a, b\<rangle>]) \<leadsto> \<bottom>\<close>. Result: \<open>None\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Abst ''b'' (Paar (Susp [] ''X'') (Atom ''b''))) \<approx>?
                    Abst ''b'' (Abst ''a'' (Paar (Atom ''a'') (Susp [] ''X'')))], [])"

subsection \<open>Freshness problems\<close>

text \<open>\<open>([], [a #? [a]X]) \<rightarrow> ([], [])\<close>. Result: \<open>Some ({}, [])\<close>.\<close>
value "nomu_unify ([], [''a'' \<sharp>? Abst ''a'' (Susp [] ''X'')])"

text \<open>\<open>([], [a #? f b]) \<rightarrow> ([], [a #? b]) \<rightarrow> ([], [])\<close>. Result: \<open>Some ({}, [])\<close>.\<close>
value "nomu_unify ([], [''a'' \<sharp>? Func ''f'' (Atom ''b'')])"

text \<open>\<open>([], [a #? \<langle>a, b\<rangle>]) \<rightarrow> ([], [a #? a, a #? b]) \<rightarrow> \<bottom>\<close>. Result: \<open>None\<close>.\<close>
value "nomu_unify ([], [''a'' \<sharp>? Paar (Atom ''a'') (Atom ''b'')])"

text \<open>\<open>([], [a #? (a b)\<cdot>X]) \<turnstile>{b # X} \<rightarrow> ([], [])\<close>
  Here \<open>(a b)\<^sup>-\<^sup>1\<cdot>a = b\<close>.
  Result: \<open>Some ({b # X}, [])\<close>.\<close>
value "nomu_unify ([], [''a'' \<sharp>? Susp [(''a'', ''b'')] ''X''])"

subsection \<open>Mixed problems\<close>

text \<open>\<open>([X \<approx>? [a]Y], [a #? X]) \<turnstile>[X \<mapsto> [a]Y] \<leadsto> ([], [a #? [a]Y]) \<rightarrow> ([], [])\<close>. Result: \<open>Some ({}, [X \<mapsto> [a]Y])\<close>.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Abst ''a'' (Susp [] ''Y'')], [''a'' \<sharp>? Susp [] ''X''])"

text \<open>\<open>([X \<approx>? a], [a #? X]) \<turnstile>[X \<mapsto> a] \<leadsto> ([], [a #? a]) \<rightarrow> \<bottom>\<close>. Result: \<open>None\<close>.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Atom ''a''], [''a'' \<sharp>? Susp [] ''X''])"

subsection \<open>Repeated meta-variables\<close>

text \<open>\<open>([\<langle>X, X\<rangle> \<approx>? \<langle>a, a\<rangle>], []) \<leadsto> ([X \<approx>? a, X \<approx>? a], []) \<turnstile>[X \<mapsto> a] \<leadsto> ([a \<approx>? a], []) \<leadsto> ([], [])\<close>. Result: \<open>Some ({}, [X \<mapsto> a])\<close>.\<close>
value "nomu_unify ([Paar (Susp [] ''X'') (Susp [] ''X'') \<approx>? Paar (Atom ''a'') (Atom ''a'')], [])"

text \<open>\<open>([\<langle>X, X\<rangle> \<approx>? \<langle>a, b\<rangle>], []) \<leadsto> ([X \<approx>? a, X \<approx>? b], []) \<turnstile>[X \<mapsto> a] \<leadsto> ([a \<approx>? b], []) \<leadsto> \<bottom>\<close>. Result: \<open>None\<close>.\<close>
value "nomu_unify ([Paar (Susp [] ''X'') (Susp [] ''X'') \<approx>? Paar (Atom ''a'') (Atom ''b'')], [])"

text \<open>\<open>([(a b)\<cdot>X \<approx>? X], []) \<leadsto> ([], [a #? X, b #? X]) \<turnstile>{a # X} \<rightarrow> ([], [b #? X]) \<turnstile>{b # X} \<rightarrow> ([], [])\<close>
  Here \<open>ds((a b), id) = [a, b]\<close>.
  Result: \<open>Some ({a # X, b # X}, [])\<close>.\<close>
value "nomu_unify ([Susp [(''a'', ''b'')] ''X'' \<approx>? Susp [] ''X''], [])"

text \<open>\<open>([(a b)\<cdot>X \<approx>? (b c)\<cdot>X], []) \<leadsto> ([], [a #? X, b #? X, c #? X]) \<turnstile>{a # X} \<rightarrow> ([], [b #? X, c #? X]) \<turnstile>{b # X} \<rightarrow> ([], [c #? X]) \<turnstile>{c # X} \<rightarrow> ([], [])\<close>
  Here \<open>ds((a b), (b c)) = [a, b, c]\<close>.
  Result: \<open>Some ({a # X, b # X, c # X}, [])\<close>.\<close>
value "nomu_unify ([Susp [(''a'', ''b'')] ''X'' \<approx>? Susp [(''b'', ''c'')] ''X''], [])"

text \<open>\<open>([\<langle>X, (a b)\<cdot>X\<rangle> \<approx>? \<langle>a, b\<rangle>], []) \<leadsto> ([X \<approx>? a, (a b)\<cdot>X \<approx>? b], []) \<turnstile>[X \<mapsto> a] \<leadsto> ([(a b)\<cdot>a \<approx>? b], []) = ([b \<approx>? b], []) \<leadsto> ([], [])\<close>. Result: \<open>Some ({}, [X \<mapsto> a])\<close>.\<close>
value "nomu_unify ([Paar (Susp [] ''X'') (Susp [(''a'', ''b'')] ''X'') \<approx>? Paar (Atom ''a'') (Atom ''b'')], [])"

text \<open>\<open>([\<langle>X, (a b)\<cdot>X\<rangle> \<approx>? \<langle>a, a\<rangle>], []) \<leadsto> ([X \<approx>? a, (a b)\<cdot>X \<approx>? a], []) \<turnstile>[X \<mapsto> a] \<leadsto> ([(a b)\<cdot>a \<approx>? a], []) = ([b \<approx>? a], []) \<leadsto> \<bottom>\<close>. Result: \<open>None\<close>.\<close>
value "nomu_unify ([Paar (Susp [] ''X'') (Susp [(''a'', ''b'')] ''X'') \<approx>? Paar (Atom ''a'') (Atom ''a'')], [])"

text \<open>\<open>([\<langle>X, Y\<rangle> \<approx>? \<langle>(a b)\<cdot>Y, a\<rangle>], []) \<leadsto> ([X \<approx>? (a b)\<cdot>Y, Y \<approx>? a], []) \<turnstile>[X \<mapsto> (a b)\<cdot>Y] \<leadsto> ([Y \<approx>? a], []) \<turnstile>[Y \<mapsto> a] \<leadsto> ([], [])\<close>
  Composing the substitutions, \<open>X \<mapsto> (a b)\<cdot>a = b\<close>.
  Result: \<open>Some ({}, [X \<mapsto> b, Y \<mapsto> a])\<close>.\<close>
value "nomu_unify ([Paar (Susp [] ''X'') (Susp [] ''Y'') \<approx>? Paar (Susp [(''a'', ''b'')] ''Y'') (Atom ''a'')], [])"

text \<open>\<open>([\<langle>X, Y\<rangle> \<approx>? \<langle>f Y, f X\<rangle>], []) \<leadsto> ([X \<approx>? f Y, Y \<approx>? f X], []) \<turnstile>[X \<mapsto> f Y] \<leadsto> ([Y \<approx>? f (f Y)], []) \<leadsto> \<bottom>\<close>
  Occurs check: \<open>Y\<close> occurs in \<open>f (f Y)\<close>.
  Result: \<open>None\<close>.\<close>
value "nomu_unify ([Paar (Susp [] ''X'') (Susp [] ''Y'') \<approx>? Paar (Func ''f'' (Susp [] ''Y'')) (Func ''f'' (Susp [] ''X''))], [])"

text \<open>\<open>([[a]X \<approx>? [b](a b)\<cdot>X], []) \<leadsto> ([X \<approx>? (a b)(a b)\<cdot>X], [a #? (a b)\<cdot>X]) \<leadsto> ([], [a #? (a b)\<cdot>X]) \<turnstile>{b # X} \<rightarrow> ([], [])\<close>
  Here \<open>ds(id, (a b)(a b)) = {}\<close> and \<open>(a b)\<^sup>-\<^sup>1\<cdot>a = b\<close>.
  Result: \<open>Some ({b # X}, [])\<close>.\<close>
value "nomu_unify ([Abst ''a'' (Susp [] ''X'') \<approx>? Abst ''b'' (Susp [(''a'', ''b'')] ''X'')], [])"

text \<open>\<open>([X \<approx>? Y, Y \<approx>? [a]b], [b #? X]) \<turnstile>[X \<mapsto> Y] \<leadsto> ([Y \<approx>? [a]b], [b #? Y]) \<turnstile>[Y \<mapsto> [a]b] \<leadsto> ([], [b #? [a]b]) \<rightarrow> ([], [b #? b]) \<rightarrow> \<bottom>\<close>. Result: \<open>None\<close>.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Susp [] ''Y'', Susp [] ''Y'' \<approx>? Abst ''a'' (Atom ''b'')], [''b'' \<sharp>? Susp [] ''X''])"

text \<open>\<open>([X \<approx>? Y, Y \<approx>? [a]a], [a #? X]) \<turnstile>[X \<mapsto> Y] \<leadsto> ([Y \<approx>? [a]a], [a #? Y]) \<turnstile>[Y \<mapsto> [a]a] \<leadsto> ([], [a #? [a]a]) \<rightarrow> ([], [])\<close>. Result: \<open>Some ({}, [X \<mapsto> [a]a, Y \<mapsto> [a]a])\<close>.\<close>
value "nomu_unify ([Susp [] ''X'' \<approx>? Susp [] ''Y'', Susp [] ''Y'' \<approx>? Abst ''a'' (Atom ''a'')], [''a'' \<sharp>? Susp [] ''X''])"

(*<*)
end
(*>*)
