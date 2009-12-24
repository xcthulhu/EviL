header{* A Classical Logic Axiom Class *}

theory ClassAxClass
imports MinAxClass
begin

class ClassAx = MinAx +
  fixes bot :: "'a"     ("\<bottom>")
  assumes ax3: "\<turnstile> ((\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<psi> \<rightarrow> \<bottom>)) \<rightarrow> \<psi> \<rightarrow> \<phi>"

instantiation bool :: ClassAx
begin
definition bot_bool_def[iff]: "\<bottom> = False"

instance proof
qed (fastsimp+)
end

no_notation
Not  ("\<not> _" [40] 40)

abbreviation (in ClassAx) 
neg :: "'a \<Rightarrow> 'a" ("\<not> _" [40] 40) where
"\<not> \<phi> \<equiv> (\<phi> \<rightarrow> \<bottom>)"

text
{* The following rule is sometimes called \emph{negation elimination}
   in natural deduction\ldots this is a good name, so we'll name this lemma
   after that rule. *}

lemma (in ClassAx) neg_elim: "\<turnstile> \<not> \<phi> \<rightarrow> \<phi> \<rightarrow> \<psi>"
proof -
  from ax1 have "\<turnstile> \<not> \<phi> \<rightarrow> \<not> \<psi> \<rightarrow> \<not> \<phi>" .
  moreover from ax3 have "\<turnstile> (\<not> \<psi> \<rightarrow> \<not> \<phi>) \<rightarrow> \<phi> \<rightarrow> \<psi>" .
  ultimately show ?thesis by (blast intro: hs)
qed

text
{* We next turn to proving two forms of double negation; 
   the latter is evidently intuitionistically valid while 
   the former is a favorite of classical logicians. *}

lemma (in ClassAx) dblneg1: "\<turnstile> \<not> \<not> \<phi> \<rightarrow> \<phi>"
proof -
  from neg_elim have "\<turnstile> \<not> \<not> \<phi> \<rightarrow> \<not> \<phi> \<rightarrow> \<not> \<not> \<not> \<phi>" .
  moreover from ax3 have "\<turnstile> (\<not> \<phi> \<rightarrow> \<not> \<not> \<not> \<phi>) \<rightarrow> \<not> \<not> \<phi> \<rightarrow> \<phi>" .
  ultimately have "\<turnstile> \<not> \<not> \<phi> \<rightarrow> \<not> \<not> \<phi> \<rightarrow> \<phi>" by (blast intro: hs)
  thus ?thesis by (blast intro: imp_remove mp)
qed

lemma (in ClassAx) dblneg2: "\<turnstile> \<phi> \<rightarrow> \<not> \<not> \<phi>"
proof -
  from dblneg1 have "\<turnstile> \<not> \<not> \<not> \<phi> \<rightarrow> \<not> \<phi>" .
  moreover from ax3 have "\<turnstile> (\<not> \<not> \<not> \<phi> \<rightarrow> \<not> \<phi>) \<rightarrow> \<phi> \<rightarrow> \<not> \<not> \<phi>" .
  ultimately show ?thesis by (blast intro: mp)
qed

text
{* Finally, we prove a form of Hilbert's explosion principle,
   also known as \emph{ex falso quodlibet} *}

lemma (in ClassAx) expls: "\<turnstile> \<bottom> \<rightarrow> \<phi>"
proof -
  from refl have "\<turnstile> \<bottom> \<rightarrow> \<bottom>" .
  with weaken have "\<turnstile> (\<phi> \<rightarrow> \<bottom>) \<rightarrow> (\<bottom> \<rightarrow> \<bottom>)" .
  with mp ax3 [where \<phi>="\<phi>" and \<psi>="\<bottom>"]
       show ?thesis by blast
qed

text
{* We now turn to introducing the shorthand for disjunction 
   and conjunction: *} 

no_notation
"op |"  (infixr "\<or>" 30)

abbreviation (in ClassAx) 
disj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<or>" 30) where
"\<phi> \<or> \<psi> \<equiv> \<not> \<phi> \<rightarrow> \<psi>"

text
{* For the time being, we don't care really about conjunction or
   bi-implication.
   We already have effectively proven @{term "\<not> \<phi> \<or> \<phi>"}; we
   now turn to proving commutativity. 

   For our own sense of clarity, within the proof we shall use the
   unabbreviated notation. *}

lemma (in ClassAx) disj_comm: "\<turnstile> \<phi> \<or> \<psi> \<rightarrow> \<psi> \<or> \<phi>"
proof -
   from refl have "[\<not> \<phi> \<rightarrow> \<psi>] :\<turnstile> \<not> \<phi> \<rightarrow> \<psi>" by auto
   moreover from dblneg2 lift 
            have "[\<not> \<phi> \<rightarrow> \<psi>] :\<turnstile> \<psi> \<rightarrow> \<not> \<not> \<psi>" by blast
   moreover note lift_hs
   ultimately have "[\<not> \<phi> \<rightarrow> \<psi>] :\<turnstile> \<not> \<phi> \<rightarrow> \<not> \<not> \<psi>" by blast
   moreover from ax3 lift 
     have "[\<not> \<phi> \<rightarrow> \<psi>] :\<turnstile> (\<not> \<phi> \<rightarrow> \<not> \<not> \<psi>) \<rightarrow> \<not> \<psi> \<rightarrow> \<phi>"
       by blast
   moreover note lift_mp
   ultimately have "[\<not> \<phi> \<rightarrow> \<psi>] :\<turnstile> \<not> \<psi> \<rightarrow> \<phi>" by blast
   thus ?thesis by auto
qed

text
{* We get to perhaps the most important result of this file now,
   \emph{disjunction elimination}, which is sometimes known as the
   \emph{constructive dilemma}.  *}

lemma (in ClassAx) disjE: 
 "\<turnstile> \<phi> \<or> \<psi> \<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<chi>) \<rightarrow> \<chi>"
proof -
  let ?\<Gamma> = "[\<phi> \<or> \<psi>, \<phi> \<rightarrow> \<chi>, \<psi> \<rightarrow> \<chi>]"
  have "?\<Gamma> :\<turnstile> \<phi> \<or> \<chi>"
  proof -
    have "(\<phi> \<or> \<psi>) \<in> set ?\<Gamma>" by simp
    with lift_elm have "?\<Gamma> :\<turnstile> \<phi> \<or> \<psi>" .
    moreover have "(\<psi> \<rightarrow> \<chi>) \<in> set ?\<Gamma>" by simp
    with lift_elm have "?\<Gamma> :\<turnstile> \<psi> \<rightarrow> \<chi>" .
    moreover note lift_hs
    ultimately show ?thesis by blast
  qed
  with lift disj_comm lift_mp
    have "?\<Gamma> :\<turnstile> \<chi> \<or> \<phi>" by blast
  with lift lift_hs dblneg2
    have "?\<Gamma> :\<turnstile> \<chi> \<or> \<not> \<not> \<phi>" by blast
  with lift ax2 lift_mp
    have "?\<Gamma> :\<turnstile> (\<not> \<chi> \<rightarrow> \<not> \<phi>) \<rightarrow> \<not> \<not> \<chi>"
      by blast
  moreover have "?\<Gamma> :\<turnstile> \<not> \<chi> \<rightarrow> \<not> \<phi>"
    proof -
      have "(\<phi> \<rightarrow> \<chi>) \<in> set ?\<Gamma>" by simp
      with lift_elm have "?\<Gamma> :\<turnstile> \<phi> \<rightarrow> \<chi>" .
      with lift dblneg1 lift_hs
        have "?\<Gamma> :\<turnstile> \<not> \<not> \<phi> \<rightarrow> \<chi>" by blast
      with lift disj_comm lift_mp
        show ?thesis by blast
    qed
  moreover
  note lift_mp
  ultimately have "?\<Gamma> :\<turnstile> \<not> \<not> \<chi>" by best
  with lift lift_mp dblneg1 [where \<phi>="\<chi>"]
  have "?\<Gamma> :\<turnstile> \<chi>" by blast
  thus ?thesis by auto
qed
      
lemma (in ClassAx) cdil:
  assumes a: "\<Gamma> :\<turnstile> \<phi> \<or> \<psi>"
      and b: "\<Gamma> :\<turnstile> \<phi> \<rightarrow> \<chi>"
      and c: "\<Gamma> :\<turnstile> \<psi> \<rightarrow> \<chi>"
    shows "\<Gamma> :\<turnstile> \<chi>"
using a b c
proof -
  let ?\<alpha>="\<phi> \<or> \<psi> \<rightarrow> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<chi>) \<rightarrow> \<chi>"
  from disjE [where \<phi>="\<phi>" and \<psi>="\<psi>" and \<chi>="\<chi>"]
       lift [where \<Gamma>="\<Gamma>" and \<phi>="?\<alpha>"]
  have "\<Gamma> :\<turnstile> ?\<alpha>" by auto
  with a lift_mp [where \<Gamma>="\<Gamma>" and \<phi>="\<phi> \<or> \<psi>"]
  have "\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<chi>) \<rightarrow> \<chi>" by blast 
  with b lift_mp [where \<Gamma>="\<Gamma>" and \<phi>="\<phi> \<rightarrow> \<chi>"]
  have "\<Gamma> :\<turnstile> (\<psi> \<rightarrow> \<chi>) \<rightarrow> \<chi>" by blast
  with c lift_mp [where \<Gamma>="\<Gamma>" and \<phi>="\<psi> \<rightarrow> \<chi>"]
  show ?thesis by blast
qed

end