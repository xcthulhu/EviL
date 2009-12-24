header{* An Intuitionistic Logic Axiom Class *}

theory IntAxClass
imports Main MinAxClass
begin

text
{* We follow Dirk van Dalen from his entry on Intuitionistic Logic
   in the Oxford Handbook of Philosophical Logic, Vol. 5\ldots
   However, we have admittedly opted to include 
   \emph{Hilbert's Explosion}, rather than the rules for
   for \emph{negation introduction} and \emph{negation elimination}, 
   as they are both consequences of this stronger result.  *}

class IntAx = MinAx +
  fixes bot :: "'a"     ("\<bottom>")
  fixes conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<cdot>" 35)
  fixes disj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "v" 30)
  assumes conjI: "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> (\<phi> \<cdot> \<psi>)"
  assumes conjE1: "\<turnstile> (\<phi> \<cdot> \<psi>) \<rightarrow> \<phi>"
  assumes conjE2: "\<turnstile> (\<phi> \<cdot> \<psi>) \<rightarrow> \<psi>"
  assumes disjI1: "\<turnstile> \<phi> \<rightarrow> (\<phi> v \<psi>)"
  assumes disjI2: "\<turnstile> \<psi> \<rightarrow> (\<phi> v \<psi>)"
  assumes disjE: "\<turnstile> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> v \<psi>) \<rightarrow> \<chi>"
  assumes expl: "\<turnstile> \<bottom> \<rightarrow> \<phi>"

text
{* Next we prove distribution over disjunction\ldots *}

(*lemma (in IntAx) imp_disj_dist:
"\<turnstile> (\<phi> \<rightarrow> (\<psi> v \<chi>)) \<rightarrow> 
*)
end
