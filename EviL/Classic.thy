header{* Classic Results in Classical Logic *}

theory Classic
imports ClassAxClass Little_Lindy
begin

text
{* We first give the grammar for Classical Logic, which is just a simple BNF:
  \[ \phi ::= p\ |\ \bot\ |\ \phi \rightarrow \psi \]
Here is the same grammar in Isabelle/HOL; note that its basically the same
as the logician's shorthand. 

Since we are constantly abusing our notation, we shall first turn off some old
notation we had adopted in ClassAxClass, so we can reuse it here. *}

no_notation
  bot ("\<bottom>") and
  imp (infixr "\<rightarrow>" 25)  and
  vdash ("\<turnstile> _" [20] 20) and
  lift_vdash (infix ":\<turnstile>" 10) and
  Not  ("\<not> _" [40] 40) and
  neg ("\<not> _" [40] 40) and
  pneg ("\<sim> _" [40] 40) 

datatype 'a cl_form = 
    CL_P "'a"                       ("P#")
  | CL_Bot                          ("\<bottom>")
  | CL_Imp "'a cl_form" "'a cl_form"  (infixr "\<rightarrow>" 25)

text
{* We next go over the semantics of Classical Logic, which follow
   a textbook recursive definition. *}

fun cl_eval :: "'a set \<Rightarrow> 'a cl_form \<Rightarrow> bool" (infix "\<Turnstile>" 20) where
   "(S \<Turnstile> P# p) = (p \<in> S)"
 | "(_ \<Turnstile> \<bottom>) = False"
 | "(S \<Turnstile> \<phi> \<rightarrow> \<psi>) = ((S \<Turnstile> \<phi>) \<longrightarrow> (S \<Turnstile> \<psi>))"

abbreviation
cl_neg :: "'a cl_form \<Rightarrow> 'a cl_form" ("\<not> _" [40] 40) where
"\<not> \<phi> \<equiv> (\<phi> \<rightarrow> \<bottom>)"

text
{* With semantics defined, we turn to defining the syntax of CL, 
   our classical logic, which is the smallest set containing 
   the three axioms of classical logic laid out in ClassAx, 
   and closed under \emph{modus ponens} *}

inductive_set CL :: "'a cl_form set" where 
  cl_ax1: "(\<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>) \<in> CL" |
  cl_ax2: "((\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>)) \<in> CL" |
  cl_ax3: "(((\<phi> \<rightarrow> \<bottom>) \<rightarrow> \<psi> \<rightarrow> \<bottom>) \<rightarrow> \<psi> \<rightarrow> \<phi>) \<in> CL" |
  cl_mp: "\<lbrakk> (\<phi> \<rightarrow> \<psi>) \<in> CL; \<phi> \<in> CL \<rbrakk> \<Longrightarrow> \<psi> \<in> CL"

abbreviation cl_vdash :: "'a cl_form \<Rightarrow> bool" ("\<turnstile> _" [20] 20) where
"(\<turnstile> \<phi>) \<equiv> \<phi> \<in> CL"

text
{* As per tradition, soundness is trivial: *}

lemma cl_soundness: "\<turnstile> \<phi> \<Longrightarrow> S \<Turnstile> \<phi>"
  by (induct set: CL, auto)

text
{* Furthermore, This trivially implies that that CL is consistent: *}
lemma cl_const: "~ (\<turnstile> \<bottom>)"
using cl_soundness
  by fastsimp

text
{* The remainder of the current discussion shall be devoted to showing
   completeness.  We first show that our logic is an instance
   of ClassAx: *} 

interpretation cl_ClassAx: ClassAx "op \<rightarrow>" "cl_vdash" "\<bottom>"
proof qed (fastsimp intro: CL.intros)+

text
{* Next, we define the \emph{Fischer-Ladner} subformula operation, 
   and prove some key lemmas regarding it. *}

primrec FL :: "'a cl_form \<Rightarrow> 'a cl_form set" where
   "FL (P# p) = {P# p, \<not> (P# p), \<bottom>, \<not> \<bottom>}"
 | "FL \<bottom> = {\<bottom>, \<not> \<bottom>}"
 | "FL (\<phi> \<rightarrow> \<psi>) = { \<phi> \<rightarrow> \<psi>, \<not> (\<phi> \<rightarrow> \<psi>), 
                    \<phi>, \<not> \<phi>, \<psi>, \<not> \<psi> , \<bottom>, \<not> \<bottom>} 
                  \<union> FL \<phi> \<union> FL \<psi>"

lemma finite_FL: "finite (FL \<phi>)"
  by (induct \<phi>) simp_all

lemma imp_closed_FL: "(\<psi> \<rightarrow> \<chi>) \<in> FL \<phi> 
                       \<Longrightarrow> \<psi> \<in> FL \<phi> \<and> \<chi> \<in> FL \<phi>"
proof -
  assume \<heartsuit>: "(\<psi> \<rightarrow> \<chi>) \<in> FL \<phi>"
  hence "\<psi> \<in> FL \<phi>"
    by (induct \<phi>, fastsimp+)
  moreover from \<heartsuit> have "\<chi> \<in> FL \<phi>"
    by (induct \<phi>, fastsimp+)
  ultimately show ?thesis by auto
qed 

text
{* We note define \emph{pseudo-negation} for our classical
   logic system.  Note that we have previously defined 
   @{term "pneg"} in developing our classical logic class.
   Indeed, what we shall define is demonstrated to be the same 
   operation. However, the advantage of our presentation is that
   it is in fact constructive, which means that it is better
   for automated reasoning.  The advantage of the previous
   definition is that it is abstract, and so can be used for
   very general reasoning.  But it relies on choice and so
   apparently does not automate terribly well\ldots *} 

fun dest_neg :: "'a cl_form \<Rightarrow> 'a cl_form"
  where "dest_neg (\<not> \<phi>) = \<phi>"

abbreviation cl_pneg :: "'a cl_form \<Rightarrow> 'a cl_form" ("\<sim>' _" [40] 40)
  where 
  "\<sim>' \<phi> \<equiv> (if (\<exists> \<psi>. (\<not> \<psi>) = \<phi>) 
             then (dest_neg \<phi>) 
             else \<not> \<phi>)"

notation
Classic.cl_ClassAx.pneg ("\<sim> _" [40] 40)

lemmas pneg_def = Classic.cl_ClassAx.pneg_def

lemma cl_pneg_eq: "(\<sim>' \<phi>) = (\<sim> \<phi>)"
proof cases
   assume a: "\<exists> \<psi>. (\<not> \<psi>) = \<phi>"
   hence "\<exists>! \<psi>. (\<not> \<psi>) = \<phi>" by fastsimp
   moreover 
   then have "(\<not> \<sim>' \<phi>) = \<phi>" by fastsimp
   moreover from a 
                 pneg_def [where \<phi>="\<phi>"]
   have "(\<sim> \<phi>) = (SOME \<psi> . (\<not> \<psi>) = \<phi>)" by fastsimp
   moreover note
   --{*@{thm [source] some1_equality} states @{thm some1_equality}*}
     some1_equality [where P="% \<psi> . (\<not> \<psi>) = \<phi>"
                       and a="\<sim>' \<phi>"]
   ultimately show ?thesis by auto
  next
   assume b: "~ (\<exists> \<psi>. (\<not> \<psi>) = \<phi>)"
   with pneg_def [where \<phi>="\<phi>"]
   show ?thesis by fastsimp
qed

lemma neg_pneg_sem_eq: "(~ (S \<Turnstile> \<phi>)) = (S \<Turnstile> \<sim> \<phi>)"
proof cases
   assume a: "\<exists> \<psi>. (\<not> \<psi>) = \<phi>"
   hence "(\<not> \<sim>' \<phi>) = \<phi>" by fastsimp
   hence "(\<not> \<sim> \<phi>) = \<phi>" by (simp add: cl_pneg_eq)
   moreover
   have "(~ (S \<Turnstile> \<not> \<sim> \<phi>)) = (S \<Turnstile> \<sim> \<phi>)" 
     by simp
   ultimately show ?thesis by simp
 next
   assume b: "~ (\<exists> \<psi>. (\<not> \<psi>) = \<phi>)"
   hence "(\<sim>' \<phi>) = (\<not> \<phi>)" by simp
   hence "(\<sim> \<phi>) = (\<not> \<phi>)" by (simp add: cl_pneg_eq)
   moreover
   have "(~ (S \<Turnstile> \<phi>)) = (S \<Turnstile> \<not> \<phi>)" by simp
   ultimately show ?thesis by simp
qed

lemma pneg_FL: "\<forall>\<psi> \<in> FL(\<phi>). (\<sim> \<psi>) \<in> FL(\<phi>)"
proof -
  have "\<forall> \<psi> \<in> FL(\<phi>) . (\<sim>' \<psi>) \<in> FL(\<phi>)"
    by (induct \<phi>, (auto|fastsimp)+)
  thus ?thesis by (simp add: cl_pneg_eq) 
qed

text
{* We now turn to showing how Atoms of @{term "FL(\<Phi>)"} can
   be translated into models.  We then show the \emph{Henkin Truth 
   Lemma} for holds for this translation. We will need to set up
   some more boilerplate to accomplish this (local abbreviations,
   local names for class theorems, and so on). *}

notation
Classic.cl_ClassAx.Atoms ("At") and
Classic.cl_ClassAx.lift_imp (infix ":\<rightarrow>" 24)

abbreviation cl_lift_vdash :: "'a cl_form list \<Rightarrow> 'a cl_form \<Rightarrow> bool" (infix ":\<turnstile>" 10) where
  "(\<Gamma> :\<turnstile> \<phi>) \<equiv> (\<turnstile> \<Gamma> :\<rightarrow> \<phi>)"

abbreviation cl_mod :: "'a cl_form set \<Rightarrow> 'a set" ("\<dagger>_") where
  "\<dagger>\<Gamma> \<equiv> {p. (P# p) \<in> \<Gamma>}"

lemmas
Atoms_def = Classic.cl_ClassAx.Atoms_def and
coincidence = Classic.cl_ClassAx.coincidence and
lift = Classic.cl_ClassAx.lift and
lift_mp = Classic.cl_ClassAx.lift_mp and
lift_weaken = Classic.cl_ClassAx.lift_weaken and
pneg_negimpII = Classic.cl_ClassAx.pneg_negimpII and
neg_elim = Classic.cl_ClassAx.neg_elim

lemma henkin_truth:
assumes A: "\<Gamma> \<in> At (FL \<psi>)"
    and B: "\<phi> \<in> FL(\<psi>)"
shows "(\<dagger>\<Gamma> \<Turnstile> \<phi>) = (list \<Gamma> :\<turnstile> \<phi>)"
  and "(\<dagger>\<Gamma> \<Turnstile> \<sim> \<phi>) = (list \<Gamma> :\<turnstile> \<sim> \<phi>)"
using A B
proof(induct \<phi>)
  --"Propositional case:"
  fix a :: "'a"
  assume "P# a \<in> FL \<psi>"
  with A finite_FL neg_pneg_sem_eq
       coincidence [where P="% \<phi>. \<dagger>\<Gamma> \<Turnstile> \<phi>"]
  have "(P# a \<in> \<Gamma>) = (list \<Gamma> :\<turnstile> P# a)"
   and \<heartsuit>: "(\<dagger>\<Gamma> \<Turnstile> P# a) = (list \<Gamma> :\<turnstile> P# a) 
             \<Longrightarrow> (\<dagger>\<Gamma> \<Turnstile> \<sim> P# a) = (list \<Gamma> :\<turnstile> \<sim> P# a)"
   by blast+
  thus "(\<dagger>\<Gamma> \<Turnstile> P# a) = (list \<Gamma> :\<turnstile> P# a)" 
    by fastsimp
  with \<heartsuit> show "(\<dagger>\<Gamma> \<Turnstile> \<sim> P# a) = (list \<Gamma> :\<turnstile> \<sim> P# a)"
    by fastsimp

  next
  --"Bottom case -- similar to the propositional case:"
  assume "\<bottom> \<in> FL \<psi>"
  with A finite_FL neg_pneg_sem_eq
       coincidence [where P="% \<phi>. \<dagger>\<Gamma> \<Turnstile> \<phi>"]
  have "(\<bottom> \<in> \<Gamma>) = (list \<Gamma> :\<turnstile> \<bottom>)"
   and \<clubsuit>: "(\<dagger>\<Gamma> \<Turnstile> \<bottom>) = (list \<Gamma> :\<turnstile> \<bottom>) 
             \<Longrightarrow> (\<dagger>\<Gamma> \<Turnstile> \<sim> \<bottom>) = (list \<Gamma> :\<turnstile> \<sim> \<bottom>)"
   by blast+
  with A Atoms_def [where \<Phi>="FL \<psi>"] 
  show "(\<dagger>\<Gamma> \<Turnstile> \<bottom>) = (list \<Gamma> :\<turnstile> \<bottom>)"
    by (simp add: mem_def)
  with \<clubsuit> show "(\<dagger>\<Gamma> \<Turnstile> \<sim> \<bottom>) = (list \<Gamma> :\<turnstile> \<sim> \<bottom>)"
    by fastsimp

  next
  --"Last case: implication is the most challenging"
  fix \<phi> \<chi> :: "'a cl_form"
  assume \<star>: "(\<phi> \<rightarrow> \<chi>) \<in> FL \<psi>"
     and "\<lbrakk> \<Gamma> \<in> At (FL \<psi>); \<phi> \<in> FL \<psi> \<rbrakk> 
             \<Longrightarrow> (\<dagger>\<Gamma> \<Turnstile> \<phi>) = (list \<Gamma> :\<turnstile> \<phi>)"
     and "\<lbrakk> \<Gamma> \<in> At (FL \<psi>); \<phi> \<in> FL \<psi> \<rbrakk> 
             \<Longrightarrow> (\<dagger>\<Gamma> \<Turnstile> \<sim> \<phi>) = (list \<Gamma> :\<turnstile> \<sim> \<phi>)"
     and "\<lbrakk> \<Gamma> \<in> At (FL \<psi>); \<chi> \<in> FL \<psi> \<rbrakk> 
             \<Longrightarrow> (\<dagger>\<Gamma> \<Turnstile> \<chi>) = (list \<Gamma> :\<turnstile> \<chi>)"
   with A 
        imp_closed_FL[where \<phi>="\<psi>" 
                        and \<psi>="\<phi>"
                        and \<chi>="\<chi>"]
   have
         c1: "(\<dagger>\<Gamma> \<Turnstile> \<phi>) = (list \<Gamma> :\<turnstile> \<phi>)"
     and c2: "(\<dagger>\<Gamma> \<Turnstile> \<sim> \<phi>) = (list \<Gamma> :\<turnstile> \<sim> \<phi>)"
     and c3: "(\<dagger>\<Gamma> \<Turnstile> \<chi>) = (list \<Gamma> :\<turnstile> \<chi>)" 
       by fastsimp+

   --"We will show that in three cases, which exhaust"
   --"all possibility, the conclusion follows."
   show "(\<dagger>\<Gamma> \<Turnstile> \<phi> \<rightarrow> \<chi>) = (list \<Gamma> :\<turnstile> \<phi> \<rightarrow> \<chi>)"
   proof -
    { assume "\<dagger>\<Gamma> \<Turnstile> \<chi>"
       with c3 lift_weaken [where \<Gamma>="list \<Gamma>"] 
       have "list \<Gamma> :\<turnstile> \<phi> \<rightarrow> \<chi>"
        and "\<dagger>\<Gamma> \<Turnstile> \<phi> \<rightarrow> \<chi>" by simp+
       hence ?thesis by simp }
    moreover
    { assume "~ (\<dagger>\<Gamma> \<Turnstile> \<phi>)"
      moreover
      with c2 neg_pneg_sem_eq 
      have "list \<Gamma> :\<turnstile> \<sim> \<phi>" by fastsimp
      with pneg_negimpII
           lift [where \<Gamma>="list \<Gamma>"]
           lift_mp [where \<Gamma>="list \<Gamma>"]
       have "list \<Gamma> :\<turnstile> \<not> \<phi>" 
         by blast
       with neg_elim
            lift [where \<Gamma>="list \<Gamma>"]
            lift_mp [where \<Gamma>="list \<Gamma>"]
       have "list \<Gamma> :\<turnstile> \<phi> \<rightarrow> \<chi>" 
         by blast
       ultimately have ?thesis by fastsimp }
    moreover
    { assume a: "\<dagger>\<Gamma> \<Turnstile> \<phi>"
         and b: "~ (\<dagger>\<Gamma> \<Turnstile> \<chi>)"
      --"We proceed by reductio ad absurdem"
      { assume "list \<Gamma> :\<turnstile> \<phi> \<rightarrow> \<chi>"
        with a c1 lift_mp [where \<Gamma>="list \<Gamma>"]
        have "list \<Gamma> :\<turnstile> \<chi>" by blast
        with c3 b have "False" by simp } 
      with a b have ?thesis by fastsimp }
    ultimately show ?thesis by fast
   qed
 
   with \<star> A finite_FL neg_pneg_sem_eq
       coincidence [where P="% \<phi>. \<dagger>\<Gamma> \<Turnstile> \<phi>"]
   show "(\<dagger>\<Gamma> \<Turnstile> \<sim> (\<phi> \<rightarrow> \<chi>)) = (list \<Gamma> :\<turnstile> \<sim> (\<phi> \<rightarrow> \<chi>))"
     by blast
qed

text
{* We now turn to our completeness theorem for classical logic *}

lemmas 
little_lindy = Classic.cl_ClassAx.little_lindy

lemma cl_completeness:
  assumes dnp: "~ (\<turnstile> \<psi>)"
    shows "\<exists> S. ~ (S \<Turnstile> \<psi>)"
using dnp
proof -
  from dnp have "~ ([] :\<turnstile> \<psi>)" 
    by simp
  hence "~ (list {} :\<turnstile> \<psi>)" 
    by (simp add: empty_set_list)
  with little_lindy [where \<Phi>="FL \<psi>"
                       and \<Gamma>="{}"]
       finite_FL [where \<phi>="\<psi>"]
       pneg_FL [where \<phi>="\<psi>"]
  have "\<exists>\<Gamma>. At (FL \<psi>) \<Gamma> \<and> ~ (list \<Gamma> :\<turnstile> \<psi>)"
    by fastsimp
  from this obtain \<Gamma> where "At (FL \<psi>) \<Gamma> \<and> ~ (list \<Gamma> :\<turnstile> \<psi>)"
    by fast
  moreover have "\<psi> \<in> FL \<psi>"
    by (induct \<psi>) simp_all
  moreover note henkin_truth [where \<psi>="\<psi>" and \<phi>="\<psi>"]
                mem_def [where x="\<Gamma>" and S="At (FL \<psi>)"]
  ultimately show ?thesis by fastsimp
qed

lemma cl_equiv: "(\<turnstile> \<psi>) = (\<forall>S. S \<Turnstile> \<psi>)"
using cl_soundness cl_completeness
  by blast

text
{* As an added bonus, since the semantics for classical
   logic are already essentially automated, we can use
   them to lazily prove hard things in the proof theory
   of classical logic automatically\ldots as the following 
   demonstrates *}

lemma cl_proof [intro!]: "\<forall>S. S \<Turnstile> \<psi> \<Longrightarrow> \<turnstile> \<psi>"
using cl_equiv
   by blast

lemma "\<turnstile> ((\<psi> \<rightarrow> \<phi>) \<rightarrow> \<psi>) \<rightarrow> \<psi>"
  by fastsimp

text
{* We'll next turn to setting up a system for importing
   our theorems from classical logic into the ClassAx
   class.  This will prove extremely useful for our
   future exploits in formalizing modal logic (since
   this will mean we will have any classical tautology
   we can think of at our disposal in proofs).

   As a technical note, we are generally agnostic over
   what proposition letters are in our treatment of
   classical logic - but here we make a definite 
   interpretation, which is that they are propositions
   in whatever classical logic we are looking at.

   Before we proceed much further, we'll clean up our
   notation a bit and undo some of our previous abuse
   (so that we may presumably resume abusing notation in
    future theories). *}

no_notation
  cl_vdash ("\<turnstile> _" [20] 20) and
  Classic.cl_ClassAx.Atoms ("At") and
  Classic.cl_ClassAx.lift_imp (infix ":\<rightarrow>" 24) and
  cl_lift_vdash (infix ":\<turnstile>" 10) and
  Classic.cl_ClassAx.pneg ("\<sim> _" [40] 40) and
  cl_pneg ("\<sim>' _" [40] 40) and
  cl_mod ("\<dagger>_")

notation
  bot ("\<bottom>") and
  imp (infixr "\<rightarrow>" 25) and
  vdash ("\<turnstile> _" [20] 20) and
  cl_vdash ("\<turnstile>\<^bsub>CL\<^esub> _" [20] 20) and
  lift_vdash (infix ":\<turnstile>" 10) and
  neg ("\<not> _" [40] 40) and
  pneg ("\<sim> _" [40] 40)

primrec (in ClassAx) cltr :: "'a cl_form \<Rightarrow> 'a" where
     "cltr (P# a) = a"
   | "cltr \<bottom>  = \<bottom>"
   | "cltr (\<phi> \<rightarrow> \<psi>) = ((cltr \<phi>) \<rightarrow> (cltr \<psi>))"

lemma (in ClassAx) cl_translate: "\<phi> \<in> CL \<Longrightarrow> \<turnstile> cltr \<phi>"
by (induct set: CL, 
    (fastsimp intro: ax1 ax2 ax3 mp)+)

end
