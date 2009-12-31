header{* A Minimal Logic Axiom Class *}

theory MinAxClass
imports Main
begin

text
{* This file introduces some proof theory for \emph{minimal logic},
   the implicational fragment of \emph{intuitionistic logic}. 
   The most important results of this file involve development of 
   some elementary results in the sequent calculus, namely various 
   forms of \emph{deduction theorem}, \emph{monotonicity} and 
   finally \emph{cut}. Presumably one could consider 
   \emph{minimal logic} an axiomatic extension of certain 
   \emph{substructural logics}, but this is admittedly beyond
   the scope of our project. *}

text
{* As an aside, this file represents a first real attempt to prove
   anything nontrivial employing \emph{classes} and more advanced Isar 
   proof patterns in Isabelle/HOL. It doesn't run particularly fast, the 
   style is pretty inconsistent, many proofs could probably be simplified, 
   and it is overall not very elegant in our opinion. *}

class MinAx =
  fixes imp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixr "\<rightarrow>" 25)
  fixes vdash :: "'a \<Rightarrow> bool"      ("\<turnstile> _" [20] 20)
  assumes ax1: "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>"
  assumes ax2: "\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>)"
  assumes mp: "\<turnstile> \<phi> \<rightarrow> \<psi>  \<Longrightarrow> \<turnstile> \<phi> \<Longrightarrow> \<turnstile> \<psi>" 

text
{* Note that @{term "mp"} stands for \emph{modus ponens} *}

text
{* We first show, very briefly, that this set of axioms is 
   consistent, by giving an instance in which they are satisfied
   (in this case, we just use the basic logic of Isabelle/HOL) *}

instantiation bool :: MinAx
begin
definition imp_bool_def[iff]: "imp = (\<lambda> \<phi> \<psi>. \<phi> \<longrightarrow> \<psi>)"
definition vdash_bool_def[iff]: "(\<turnstile> \<phi>) = \<phi>"

instance proof
qed (fastsimp+)
end

text
{* This result may seem trivial, but it is really is fundamental 
   to all minimal logic; we shall use it over and over again. *}

lemma (in MinAx) refl: "\<turnstile> \<phi> \<rightarrow> \<phi>"
proof -
   from ax1 [where \<phi>="\<phi>" and \<psi>="\<phi> \<rightarrow> \<phi>"] 
        ax2 [where \<phi>="\<phi>" and \<psi>="\<phi> \<rightarrow> \<phi>" and \<chi>="\<phi>"]
        ax1 [where \<phi>="\<phi>" and \<psi>="\<phi>"] 
        show ?thesis by (blast intro: mp)
qed

text
{* We next turn to providing some other basic results in minimal logic. 
   Note that @{term"hs"} stands for \emph{hypothetical syllogism}. *}

lemma (in MinAx) weaken: "\<turnstile> \<phi> \<Longrightarrow> \<turnstile> \<psi> \<rightarrow> \<phi>"
by (blast intro: mp ax1)

lemma (in MinAx) hs: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> \<psi> \<rightarrow> \<chi> \<Longrightarrow> \<turnstile> \<phi> \<rightarrow> \<chi>"
proof -
   assume "\<turnstile> \<phi> \<rightarrow> \<psi>" "\<turnstile> \<psi> \<rightarrow> \<chi>"
   moreover 
     from this
          weaken [where \<psi>="\<phi>" and \<phi>="\<psi> \<rightarrow> \<chi>"]
        have "\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>" by simp
   moreover
     from ax2 [where \<phi>="\<phi>" and \<psi>="\<psi>" and \<chi>="\<chi>"]
       have "\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>)" .
   ultimately show ?thesis by (blast intro: mp)
qed

text
{* That concludes our discussion of basic minimal logic. 
   We now turn to developing a rudimentary sequent calculus; the basis of
   our analysis will be a higher order operation, which translates lists 
   into chains of implication. *}

primrec (in MinAx) lift_imp :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" (infix ":\<rightarrow>" 24) where
    "([] :\<rightarrow> \<phi>) = \<phi>"
  | "((\<psi> # \<psi>s) :\<rightarrow> \<phi>) = (\<psi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>))"

text 
{* As you can see, we use a primitive recursive function in the above definition of
   @{term "% \<psi>s \<phi>. \<psi>s :\<rightarrow> \<phi>"}; we can write this particular lambda abstraction with
   the shorthand @{term "op :\<rightarrow>"}. Moreover, we can conceptually we think of this as 
   @{term "foldr (% \<psi> \<phi>. \<psi> \<rightarrow> \<phi>) \<psi>s \<phi>"}, in fact this follows from a rather trivial
   induction: *}

lemma (in MinAx) "(\<psi>s :\<rightarrow> \<phi>) = foldr (% \<psi> \<phi>. \<psi> \<rightarrow> \<phi>) \<psi>s \<phi>"
by (induct \<psi>s) simp_all

text
{* With @{term "op :\<rightarrow>"}, we now turn to developing some elementary results in the
   sequent calculus. The first results we find simply correspond to the minimal logic 
   metarules previously established, and also the axioms we have been given.  Note that 
   while results in the sequent calculus follow, we first prove stronger theorems in 
   the object language, as this practice typically makes inductive results easier. *}

abbreviation (in MinAx) lift_vdash :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" (infix ":\<turnstile>" 10) where
  "(\<Gamma> :\<turnstile> \<phi>) \<equiv> (\<turnstile> \<Gamma> :\<rightarrow> \<phi>)"

lemma (in MinAx) lift: "\<turnstile> \<phi> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi>"
  by (induct \<Gamma>, auto, simp add: weaken)

lemma (in MinAx) lift_ax2: "\<turnstile> (\<phi>s :\<rightarrow> (\<psi> \<rightarrow> \<chi>)) \<rightarrow> (\<phi>s :\<rightarrow> \<psi>) \<rightarrow> (\<phi>s :\<rightarrow> \<chi>)"
  proof (induct \<phi>s, simp add: refl)
    -- "We can solve the base case automatically."
    -- "It suffices to prove the inductive step."
  fix \<phi>s :: "'a list"
  fix a \<psi> \<chi> :: "'a"
  assume "\<turnstile> (\<phi>s :\<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi>s :\<rightarrow> \<psi>) \<rightarrow> (\<phi>s :\<rightarrow> \<chi>)"
  moreover from this weaken 
     have "\<turnstile> a \<rightarrow> ((\<phi>s :\<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi>s :\<rightarrow> \<psi>) \<rightarrow> (\<phi>s :\<rightarrow> \<chi>))"
      by fast
  from this ax2 
      show "\<turnstile> (a # \<phi>s :\<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (a # \<phi>s :\<rightarrow> \<psi>) \<rightarrow> (a # \<phi>s :\<rightarrow> \<chi>)"
      by(auto, blast intro: mp hs)
qed

lemma (in MinAx) lift_mp: "\<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi>  \<Longrightarrow> \<Gamma> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> :\<turnstile> \<psi>"
by (blast intro: mp lift_ax2)

lemma (in MinAx) lift_weaken: "\<Gamma> :\<turnstile> \<phi> \<Longrightarrow> \<Gamma> :\<turnstile> \<psi> \<rightarrow> \<phi>"
by (blast intro: ax1 lift lift_mp)

lemma (in MinAx) lift_ax1: "\<turnstile> \<phi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)"
proof (induct \<psi>s, simp add: refl)
  -- "Once again, base case is trivial so we only do inductive case"
  fix \<psi>s :: "'a list"
  fix a :: "'a"
  assume "\<turnstile> \<phi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)"
  hence "[\<phi>] :\<turnstile> \<psi>s :\<rightarrow> \<phi>" by simp
  hence "[\<phi>] :\<turnstile> a \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)" by (blast intro: lift_weaken)
  thus "\<turnstile> \<phi> \<rightarrow> (a # \<psi>s :\<rightarrow> \<phi>)" by simp
qed

lemma (in MinAx) lift_hs: "\<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<Gamma> :\<turnstile> \<psi> \<rightarrow> \<chi> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi> \<rightarrow> \<chi>"
proof -
  -- "We just follow the proof of the unlifted hypothetical syllogism" 
  assume "\<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi>" "\<Gamma> :\<turnstile> \<psi> \<rightarrow> \<chi>"
  moreover 
     from this
          lift_weaken [where \<Gamma>="\<Gamma>" and \<psi>="\<phi>" and \<phi>="\<psi> \<rightarrow> \<chi>"]
        have "\<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>" by simp
  moreover
     from ax2 [where \<phi>="\<phi>" and \<psi>="\<psi>" and \<chi>="\<chi>"]
          lift
       have "\<Gamma> :\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>)" by simp
  ultimately show ?thesis by (blast intro: lift_mp)
qed

text
{* This theorem is in basic minimal logic, but it is hard
   to prove without dipping shallowly into the sequent calculus.
   It will be a gateway to much more general theorems. *}

lemma (in MinAx) flip: "\<turnstile> (\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<psi> \<rightarrow> \<phi> \<rightarrow> \<chi>)"
proof -
  let ?\<alpha> = "\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>"
  from refl [where \<phi>="\<psi>"]
       weaken
       lift_weaken [where \<Gamma>="[?\<alpha>, \<psi>]"
                      and \<phi>="\<psi>"
                      and \<psi>="\<phi>"]
       have "[?\<alpha> ,\<psi>, \<phi>] :\<turnstile> \<psi>" by auto
  moreover 
  from refl [where \<phi>="?\<alpha>"]
       lift_weaken [where \<Gamma>="[?\<alpha>]" 
                        and \<psi>="\<psi>"
                        and \<phi>="?\<alpha>"]
       lift_weaken [where \<Gamma>="[?\<alpha>,\<psi>]" 
                        and \<psi>="\<phi>"
                        and \<phi>="?\<alpha>"]
       have "[?\<alpha> ,\<psi>, \<phi>] :\<turnstile> ?\<alpha>" by auto
  moreover
  from refl [where \<phi>="\<phi>"]
       lift [where \<Gamma>="[?\<alpha>,\<psi>]" 
                   and \<phi>="\<phi> \<rightarrow> \<phi>"]
       have "[?\<alpha> ,\<psi>, \<phi>] :\<turnstile> \<phi>" by auto
  ultimately have "[?\<alpha>,\<psi>,\<phi>] :\<turnstile> \<chi>" by (blast intro: lift_mp)
  thus ?thesis by auto
qed

text
{* We next establish two analogues in using sequents *}

lemma (in MinAx) lift_flip1: 
   "\<turnstile> (\<psi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)) \<rightarrow> (\<psi>s :\<rightarrow> (\<psi> \<rightarrow> \<phi>))"
proof (induct \<psi>s, auto simp add: refl)
  fix \<psi>s :: "'a list"; fix a :: "'a"
  assume "\<turnstile> (\<psi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)) \<rightarrow> (\<psi>s :\<rightarrow> \<psi> \<rightarrow> \<phi>)"
  hence "\<turnstile> (a \<rightarrow> \<psi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)) \<rightarrow> a \<rightarrow> (\<psi>s :\<rightarrow> \<psi> \<rightarrow> \<phi>)"
      by (blast intro: weaken ax2 mp)
  thus "\<turnstile> (\<psi> \<rightarrow> a \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)) \<rightarrow> a \<rightarrow> (\<psi>s :\<rightarrow> \<psi> \<rightarrow> \<phi>)"
       by (blast intro: flip hs)
qed

lemma (in MinAx) lift_flip2: 
   "\<turnstile> (\<psi>s :\<rightarrow> (\<psi> \<rightarrow> \<phi>)) \<rightarrow> (\<psi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>))"
proof (induct \<psi>s, auto simp add: refl)
  fix \<psi>s :: "'a list"; fix a :: "'a"
  assume "\<turnstile> (\<psi>s :\<rightarrow> \<psi> \<rightarrow> \<phi>) \<rightarrow> \<psi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)"
  hence "\<turnstile> (a \<rightarrow> (\<psi>s :\<rightarrow> \<psi> \<rightarrow> \<phi>)) \<rightarrow> a \<rightarrow> \<psi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)"
      by (blast intro: weaken ax2 mp)
  thus "\<turnstile> (a \<rightarrow> (\<psi>s :\<rightarrow> \<psi> \<rightarrow> \<phi>)) \<rightarrow> \<psi> \<rightarrow> a \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)"
       by (blast intro: flip hs)
qed

text
{* Next, we give another result in basic minimal logic;
   we again use some results in sequent calculus to ease
   proving this result *}

lemma (in MinAx) imp_remove: "\<turnstile> (\<chi> \<rightarrow> \<chi> \<rightarrow> \<phi>) \<rightarrow> \<chi> \<rightarrow> \<phi>"
proof -
  from ax2 have "[\<chi> \<rightarrow> \<chi> \<rightarrow> \<phi>] :\<turnstile> (\<chi> \<rightarrow> \<chi>) \<rightarrow> (\<chi> \<rightarrow> \<phi>)" 
          by auto
  hence "[\<chi> \<rightarrow> \<chi> \<rightarrow> \<phi>] :\<turnstile> \<chi> \<rightarrow> \<phi>" 
          by (blast intro: refl lift lift_mp)
  thus ?thesis by auto
qed

text
{* Our first major theorem in the sequent calculus in minimal
   logic.  As we will see, this is the basis for just about
   all of the major results *}

lemma (in MinAx) lift_removeAll[iff]:
"\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> ((removeAll \<chi> \<psi>s) :\<rightarrow> (\<chi> \<rightarrow> \<phi>))"
proof(induct \<psi>s, auto simp add: ax1)
  -- "Evidently there are two things to prove"
  -- "The first is a trivial consequence of ax2"
  fix \<psi>s :: "'a list"; fix a :: "'a"
  assume "\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> (removeAll \<chi> \<psi>s :\<rightarrow> \<chi> \<rightarrow> \<phi>)"
  thus "\<turnstile> (a \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)) \<rightarrow> a \<rightarrow> (removeAll \<chi> \<psi>s :\<rightarrow> \<chi> \<rightarrow> \<phi>)"
    by (blast intro: weaken ax2 mp)
  next
  -- "So we turn to the more involved part of the proof;"
  -- "This really is the meat of the induction"
  fix \<psi>s :: "'a list"
  assume A: "\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> (removeAll \<chi> \<psi>s :\<rightarrow> \<chi> \<rightarrow> \<phi>)"
  thus "\<turnstile> (\<chi> \<rightarrow> (\<psi>s :\<rightarrow> \<phi>)) \<rightarrow> (removeAll \<chi> \<psi>s :\<rightarrow> \<chi> \<rightarrow> \<phi>)"
  proof -
     let ?\<alpha> = "\<psi>s :\<rightarrow> \<phi>"
     let ?\<beta> = "removeAll \<chi> \<psi>s :\<rightarrow> \<chi> \<rightarrow> \<phi>"
     from A have "\<turnstile> (\<chi> \<rightarrow> ?\<alpha>) \<rightarrow> \<chi> \<rightarrow> ?\<beta>" by (blast intro: ax2 weaken mp)
     moreover 
     from lift_flip1 have "\<turnstile> (\<chi> \<rightarrow> ?\<beta>) \<rightarrow> (removeAll \<chi> \<psi>s :\<rightarrow> \<chi> \<rightarrow> \<chi> \<rightarrow> \<phi>)" .
     moreover
     have 
       "\<turnstile> (removeAll \<chi> \<psi>s :\<rightarrow> (\<chi> \<rightarrow> \<chi> \<rightarrow> \<phi>)) \<rightarrow> ?\<beta>"
       by (blast intro: imp_remove lift lift_ax2 mp)
     ultimately show ?thesis by (blast intro: hs)
  qed
qed

text
{* We can now prove two expressions of the deduction theorem,
   and we'll also prove the cut rule: *}

lemma (in MinAx) disch: "\<Gamma> :\<turnstile> \<phi> \<Longrightarrow> removeAll \<psi> \<Gamma> :\<turnstile> \<psi> \<rightarrow> \<phi>"
using lift_removeAll [where \<psi>s="\<Gamma>" and \<phi>="\<phi>" and \<chi>="\<psi>"] 
by (auto, blast intro: mp)

lemma (in MinAx) undisch [iff]: "(\<Gamma> :\<turnstile> \<psi> \<rightarrow> \<phi>) = (\<psi> # \<Gamma> :\<turnstile> \<phi>)"
proof - 
  have "(\<Gamma> @ [\<psi>] :\<rightarrow> \<phi>) = (\<Gamma> :\<rightarrow> (\<psi> \<rightarrow> \<phi>))"
  proof (induct \<Gamma>, simp)
    fix \<Gamma> :: "'a list"; fix a :: "'a"
    assume "(\<Gamma> @ [\<psi>] :\<rightarrow> \<phi>) = (\<Gamma> :\<rightarrow> \<psi> \<rightarrow> \<phi>)"
    moreover have "(a # \<Gamma>) @ [\<psi>] = a # (\<Gamma> @ [\<psi>])" 
      by (induct \<Gamma>) simp_all
    ultimately show "((a # \<Gamma>) @ [\<psi>] :\<rightarrow> \<phi>) = (a # \<Gamma> :\<rightarrow> \<psi> \<rightarrow> \<phi>)" by simp
  qed
  note \<spadesuit> = this
  moreover 
  hence "(\<psi> # \<Gamma> :\<turnstile> \<phi>) = (\<Gamma> @ [\<psi>] :\<turnstile> \<phi>)"
    by (auto simp add: \<spadesuit>,
         (blast intro: mp lift_flip1 lift_flip2)+)
  ultimately show ?thesis by fastsimp
qed

lemma (in MinAx) cut:
  assumes a: "\<psi> # \<Gamma> :\<turnstile> \<phi>"
      and b: "\<Gamma> :\<turnstile> \<psi>"
       shows "\<Gamma> :\<turnstile> \<phi>"
using a b
proof -
  from a undisch have "\<Gamma> :\<turnstile> \<psi> \<rightarrow> \<phi>" by fastsimp
  with b lift_mp show ?thesis by blast
qed


text
{* The following theorem, as we shall see, gives rise to \emph{monotonicity},
   arguably the fundamental theorem of minimal logic.  We universally
   quantify everything to ease the inductive proof, which is somewhat
   technically challenging even when this trick is employed *}

lemma (in MinAx) imp_mono:
  "\<forall> \<psi>s \<phi>. set \<psi>s \<subseteq> set \<chi>s \<longrightarrow> (\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> (\<chi>s :\<rightarrow> \<phi>))"
proof (induct \<chi>s)
  { fix \<psi>s :: "'a list"; fix \<phi> :: "'a"
    assume "set \<psi>s \<subseteq> set []"
    hence "\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> ([] :\<rightarrow> \<phi>)" by (auto, simp add: refl) }
    thus "\<forall>\<psi>s \<phi>. set \<psi>s \<subseteq> set [] \<longrightarrow> (\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> ([] :\<rightarrow> \<phi>))" by auto
  next
    fix a :: "'a"; fix \<chi>s :: "'a list"
    assume \<clubsuit>: "\<forall>\<psi>s \<phi>. set \<psi>s \<subseteq> set \<chi>s \<longrightarrow> (\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> (\<chi>s :\<rightarrow> \<phi>))"
    thus "\<forall>\<psi>s \<phi>. set \<psi>s \<subseteq> set (a # \<chi>s) \<longrightarrow> (\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> (a # \<chi>s :\<rightarrow> \<phi>))"
    proof -
    -- "To prove the above we first prove something more general"
    { fix \<chi>s \<psi>s :: "'a list"; fix a \<phi> :: "'a"
      assume a1: "\<forall>\<psi>s \<phi>. set \<psi>s \<subseteq> set \<chi>s \<longrightarrow> (\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> (\<chi>s :\<rightarrow> \<phi>))"
      assume a2: "set \<psi>s \<subseteq> set (a # \<chi>s)"
      from a1 a2 have "\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> (a # \<chi>s :\<rightarrow> \<phi>)"
      proof -
        have "set \<psi>s \<subseteq> set \<chi>s \<or> ~ (set \<psi>s \<subseteq> set \<chi>s)" by fast
        -- "Thus, we have two cases to prove for"
        moreover  
        { assume "set \<psi>s \<subseteq> set \<chi>s"
          with a1 have "[\<psi>s :\<rightarrow> \<phi>] :\<turnstile> (\<chi>s :\<rightarrow> \<phi>)" by fastsimp
          moreover with ax1 have "[\<chi>s :\<rightarrow> \<phi>] :\<turnstile> (a # \<chi>s :\<rightarrow> \<phi>)" by fastsimp
          ultimately have "\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> (a # \<chi>s :\<rightarrow> \<phi>)" 
          by (fastsimp intro: hs)
        } 
        moreover 
        { let ?ls = "removeAll a \<psi>s"
          assume "~ (set \<psi>s \<subseteq> set \<chi>s)"
          with a2 have "set ?ls \<subseteq> set \<chi>s" by fastsimp
          with a1 have "\<turnstile> (?ls :\<rightarrow> a \<rightarrow> \<phi>) \<rightarrow> (\<chi>s :\<rightarrow> a \<rightarrow> \<phi>)"
            by fastsimp
          hence "\<turnstile> (?ls :\<rightarrow> a \<rightarrow> \<phi>) \<rightarrow> (a # \<chi>s :\<rightarrow> \<phi>)" 
            by (auto, blast intro: lift_flip2 hs)
          hence "\<turnstile> (\<psi>s :\<rightarrow> \<phi>) \<rightarrow> (a # \<chi>s :\<rightarrow> \<phi>)"
            by (blast intro: lift_removeAll hs)
        }
        ultimately show ?thesis by fast
      qed
    }
    -- "This evidently suffices to prove the theorem"
    with \<clubsuit> show ?thesis by fastsimp
  qed
qed

text
{* Finally, we can state \emph{monotonicity}\ldots *}
  
lemma (in MinAx) lift_mono: "set \<Gamma> \<subseteq> set \<Psi> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi> \<Longrightarrow> \<Psi> :\<turnstile> \<phi>"
using imp_mono mp by blast

lemma (in MinAx) lift_eq: "set \<Gamma> = set \<Psi> \<Longrightarrow> (\<Gamma> :\<turnstile> \<phi>) = (\<Psi> :\<turnstile> \<phi>)"
using lift_mono 
      equalityD1 [where A="set \<Gamma>" and B="set \<Psi>"]
      equalityD2 [where A="set \<Gamma>" and B="set \<Psi>"]
by blast


text
{* This is now a trivial consequence of our
   \emph{monotonicity} theorem. *}

lemma (in MinAx) lift_elm:
  "\<phi> \<in> set \<Gamma> \<Longrightarrow> \<Gamma> :\<turnstile> \<phi>"
proof -
  have "[\<phi>] :\<turnstile> \<phi>" by (auto, simp add: refl)
  moreover assume "\<phi> \<in> set \<Gamma>"
  hence "set [\<phi>] \<subseteq> set \<Gamma>" by simp
  ultimately show ?thesis 
    by (blast intro: lift_mono)
qed

text
{* A less trivial consequence is the general cut
   rule\ldots *}

lemma (in MinAx) super_cut:
    assumes "\<forall> \<phi> \<in> set \<Delta>. \<Gamma> :\<turnstile> \<phi>"
        and "\<Delta> @ \<Gamma> :\<turnstile> \<psi>"
       shows "\<Gamma> :\<turnstile> \<psi>"
using assms
proof(induct \<Delta>, simp)
  fix a :: "'a"; fix \<Delta> :: "'a list"
  assume a: "\<lbrakk>\<forall>\<phi>\<in>set \<Delta>. \<Gamma> :\<turnstile> \<phi>; \<Delta> @ \<Gamma> :\<turnstile> \<psi>\<rbrakk> \<Longrightarrow> \<Gamma> :\<turnstile> \<psi>"
     and b: "\<forall>\<phi>\<in>set (a # \<Delta>). \<Gamma> :\<turnstile> \<phi>"
     and c: "(a # \<Delta>) @ \<Gamma> :\<turnstile> \<psi>"
  hence d: "\<Gamma> :\<turnstile> a" by fastsimp
  have "set \<Gamma> \<subseteq> set (\<Delta> @ \<Gamma>)"
    by (induct \<Delta>) fastsimp+
  with d lift_mono [where \<Psi>="\<Delta> @ \<Gamma>" and \<Gamma>="\<Gamma>"]
  have e: "\<Delta> @ \<Gamma> :\<turnstile> a"
    by simp
  have "(a # \<Delta>) @ \<Gamma> = a # \<Delta> @ \<Gamma>"
    by (induct \<Delta>) simp_all
  with c e cut have f: "\<Delta> @ \<Gamma> :\<turnstile> \<psi>" by fastsimp
  from b have "\<forall> \<phi> \<in> set \<Delta>. \<Gamma> :\<turnstile> \<phi>" by fastsimp
  with a f show ?thesis by auto 
qed

end
