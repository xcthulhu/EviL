header{* A Uni-Modal Logic Axiom Class *}

theory ModalAxClass
imports Main Classic
begin

text
{* I here present a disclaimer - Isabelle's underlying logic
   cannot deal with multi-parametric type classes, which means
   that while a \emph{multi-Modal} axiom class would be ideal
   for our purposes, it is sadly impossible in this framework.  
   Hence, our class will present a uni-modal framework.  In 
   application, the modality we shall employ will be a function 
   which takes an argument and outputs one of the real modalities
   in whatever syntax we have under discussion. *}

class ModalAx = ClassAx +
  fixes box :: "'a \<Rightarrow> 'a" ("\<box> _" [40] 40)
  assumes axK: "\<turnstile> \<box> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<box> \<phi> \<rightarrow> \<box> \<psi>"
      and nec: "\<turnstile> \<phi> \<Longrightarrow> \<turnstile> \<box> \<phi>"

lemma (in ModalAx) lift_axK:
  "\<turnstile> \<box> (\<phi>s :\<rightarrow> \<psi> ) \<rightarrow> (map (%\<phi>.\<box> \<phi>) \<phi>s :\<rightarrow> \<box> \<psi>)"
proof(induct \<phi>s, simp add: refl)
  fix \<phi> :: "'a"; fix \<phi>s :: "'a list"
  let ?\<Gamma> = "[\<box>(\<phi> # \<phi>s :\<rightarrow> \<psi>), \<box> \<phi>]"
  assume \<heartsuit>: "\<turnstile> \<box> (\<phi>s :\<rightarrow> \<psi>) \<rightarrow> (map (%\<phi>.\<box> \<phi>) \<phi>s :\<rightarrow> \<box> \<psi>)"
  have "(\<phi> # \<phi>s :\<rightarrow> \<psi>) = (\<phi> \<rightarrow> (\<phi>s :\<rightarrow> \<psi>))" by simp
  with axK [where \<phi>="\<phi>" and \<psi>="\<phi>s :\<rightarrow> \<psi>"]
  have "\<turnstile> \<box> (\<phi> # \<phi>s :\<rightarrow> \<psi>) \<rightarrow> \<box> \<phi> \<rightarrow> \<box> (\<phi>s :\<rightarrow> \<psi>)"
    by simp
  hence "?\<Gamma> :\<turnstile> \<box> (\<phi>s :\<rightarrow> \<psi>)" by simp
  moreover from \<heartsuit> lift [where \<Gamma>="?\<Gamma>"]
  have "?\<Gamma> :\<turnstile> \<box> (\<phi>s :\<rightarrow> \<psi>) \<rightarrow> (map (%\<phi>.\<box> \<phi>) \<phi>s :\<rightarrow> \<box> \<psi>)"
    by simp
  moreover note lift_mp [where \<Gamma>="?\<Gamma>"]
  ultimately 
  have "?\<Gamma> :\<turnstile> map (%\<phi>.\<box> \<phi>) \<phi>s :\<rightarrow> \<box> \<psi>"
    by blast
  thus
    "\<turnstile> \<box> (\<phi> # \<phi>s :\<rightarrow> \<psi>) \<rightarrow> (map (%\<phi>.\<box> \<phi>) (\<phi> # \<phi>s) :\<rightarrow> \<box> \<psi>)"
    by simp
qed

lemma (in ModalAx) lift_nec:
  "\<Gamma> :\<turnstile> \<phi> \<Longrightarrow> (map (%\<phi>.\<box> \<phi>) \<Gamma>) :\<turnstile> \<box> \<phi>"
proof -
  assume "\<Gamma> :\<turnstile> \<phi>"
  with nec have "\<turnstile> \<box>(\<Gamma> :\<rightarrow> \<phi>)" by simp
  with lift_axK mp show ?thesis by blast
qed

abbreviation (in ModalAx) 
pos :: "'a \<Rightarrow> 'a" ("\<diamond> _" [40] 40) where
  "(\<diamond> \<phi>) \<equiv> (\<not> \<box> \<not> \<phi>)"

lemma (in ModalAx) pos_nec_imp:
  "\<turnstile> \<diamond> \<phi> \<rightarrow> \<box> (\<phi> \<rightarrow> \<psi>) \<rightarrow> \<diamond> \<psi>"
proof -
  let ?\<Gamma> = "[\<diamond> \<phi>, \<box> (\<phi> \<rightarrow> \<psi>), \<box> \<not> \<psi>]"
  have "((P# \<phi> \<rightarrow> P# \<psi>) \<rightarrow> \<not> P# \<psi> \<rightarrow> \<not> P# \<phi>) \<in> CL"
    by fastsimp
  with cl_translate have
    "\<turnstile> cltr ((P# \<phi> \<rightarrow> P# \<psi>) \<rightarrow> \<not> P# \<psi> \<rightarrow> \<not> P# \<phi>)" .
  hence "[(\<phi> \<rightarrow> \<psi>), \<not> \<psi>] :\<turnstile> \<not> \<phi>" by simp
  with lift_nec have
    "map (%\<phi>.\<box> \<phi>) [(\<phi> \<rightarrow> \<psi>), \<not> \<psi>] :\<turnstile> \<box> \<not> \<phi>" .
  moreover have 
    "set (map (%\<phi>.\<box> \<phi>) [(\<phi> \<rightarrow> \<psi>), \<not> \<psi>]) \<subseteq> set ?\<Gamma>" by simp
  moreover note lift_mono
  ultimately have "?\<Gamma> :\<turnstile> \<box> \<not> \<phi>" by blast
  moreover have "((\<box> \<not> \<phi>) \<rightarrow> \<bottom>) \<in> set ?\<Gamma>" by simp
  with lift_elm have "?\<Gamma> :\<turnstile> (\<box> \<not> \<phi>) \<rightarrow> \<bottom>" by blast
  moreover note lift_mp
  ultimately have "?\<Gamma> :\<turnstile> \<bottom>" by blast
  thus ?thesis by simp
qed

end