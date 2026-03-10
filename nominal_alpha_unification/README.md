# Nominal Alpha Unification 
### Authors
Guilherme Borges Brandão<sup>(\*)</sup>, Thomas Ammer<sup>(+)</sup>\
Daniele Nantes Sobrinho<sup>(\*)</sup>, Mauricio Ayala-Rincón<sup>(\*)</sup>,\
Christian Urban<sup>(+)</sup>,  Maribel Fernández<sup>(+)</sup>, Mohammad Abdulaziz<sup>(+)</sup>

<sup>**(\*)**</sup> Universidade de Brasília, Brasília D.F., Brazil\
<sup>**(+)**</sup> King College London, London, U.K.

## Contents

This theory verifies a non-deterministic procedure for **nominal syntactic unification**, i.e., **nominal $\alpha$-unification**. The procedure is presented as a set of inductive rules, following Christian Urban's seminal Isabelle formalisation.  

The formalisation is updated according to the PVS Ana Cristina Rocha Oliveira et al. approach by *separately* proving the properties of symmetry, transitivity, and equivariance of the $alpha$-equivalence relation. This treatment of $alpha$-equivalence properties was also followed by Washington Luís de Carvalho et al. in the Coq formalisation of nominal $\alpha$-unification and nominal C-unification. In the PVS formalisation, nominal $alpha$-unification is presented as a functional recursive algorithm, proved sound and complete, from which executable code in Lisp can be extracted. In the Coq formalisation, a non-deterministic rule-based procedure was presented, following Urban's seminal approach, which is proved sound and complete; further, a recursive definition of nominal $alpha$-unification was presented, which is proved equivalent to the inductive procedure, and from which executable code was extracted.

### References

* Christian Urban, Andrew M. Pitts, Murdoch Gabbay:
Nominal unification. *Theor. Comput. Sci.* 323(1-3): 473-497 (2004)
https://doi.org/10.1016/j.tcs.2004.06.016

* Christian Urban:
Nominal Unification Revisited. In Proc. UNIF 2010, EPTCS 42:1-11 (2010)
https://doi.org/10.4204/EPTCS.42.1

* Mauricio Ayala-Rincón, Maribel Fernández, Ana Cristina Rocha Oliveira:
Completeness in PVS of a Nominal Unification Algorithm. In Proc. LSFA 2015, ENTCS 323:57-74 (2016)
https://doi.org/10.1016/j.entcs.2016.06.005

* Ana Cristina Rocha Oliveira: 
Unification, Confluence, and Intersection Types for Nominal Rewriting Systems. PhD thesis, Graduate Program in Informatics, University of Brasília, 2016. in English.
http://repositorio.unb.br/handle/10482/22387

* Mauricio Ayala-Rincón, Washington Luís de Carvalho Segundo, Maribel Fernández, Daniele Nantes Sobrinho, Ana Cristina Rocha Oliveira:
A formalisation of nominal α-equivalence with A, C, and AC function symbols. *Theor. Comput. Sci.* 781: 3-23 (2019)
https://doi.org/10.1016/j.tcs.2019.02.020

* Washington Luís Ribeiro de Carvalho Segundo:
Nominal Equational Problems Modulo Associativity, Commutativity and Associativity-Commutativity. PhD thesis, Graduate Program in Informatics, University of Brasília, 2019. in English.
http://repositorio.unb.br/handle/10482/35474

