header{* The EviL Truth (Lemma) *}

theory EviL_Truth
imports EviL_Logic
begin

text{* In our previous treatment, we introduced the semantics, proof theory, soundness and completeness
 for classical logic in one file; addressing the issues related to the canonical model construction for
 classical logic along with everything else.  Since the logic we are developing here is much richer, we 
 have opted to devote this file to the truth lemma for the subformula
 model we have constructed. *}

no_notation
  bot ("\<bottom>") and
  imp (infixr "\<rightarrow>" 25)  and
  vdash ("\<turnstile> _" [20] 20) and
  lift_vdash (infix ":\<turnstile>" 10) and
  Not  ("\<not> _" [40] 40) and
  neg ("\<not> _" [40] 40) and
  Classic.cl_neg ("\<not> _" [40] 40) and
  pneg ("\<sim> _" [40] 40) and
  cl_pneg ("\<sim>' _" [40] 40) and
  CL_P ("P#") and
  CL_Bot ("\<bottom>") and
  CL_Imp (infixr "\<rightarrow>" 25)

text{* We first introduce \emph{pseudo} operators.  Namely, we'll follow our 
  previous treatment of pseudo-negation (that is, @{term "\<lambda> \<phi> . ~ \<phi>"}) that we did in
  \texttt{Classic.thy}, but we shall also introduce new psuedo-operations
  corresponding to @{term "[-]"} and @{term "[+]"}.
  To do this, we first prove some basic logical equivilances, which are consequences
  of the above.
 *}

lemma evil_BBI_eq: "\<turnstile> [+] X ([+] X \<phi>) \<leftrightarrow> [+] X \<phi>"
--"Further further beliefs are the same as further beliefs"
using evil_ax5 [where X="X"] 
      evil_ax4 [where X="X" and \<phi>="[+] X \<phi>"]
      evil_eq_intro
  by blast

lemma evil_BB_eq: "\<turnstile> [-] X ([-] X \<phi>) \<leftrightarrow> [-] X \<phi>"
--"To discard beliefs and then discard beliefs again"
--"is the same as discarding beliefs only once"
using evil_BBax5 [where X="X"] 
      evil_BBax4 [where X="X" and \<phi>="[-] X \<phi>"]
      evil_eq_intro
  by blast

lemma evil_eq_neg: "\<turnstile>  \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<not> \<phi> \<leftrightarrow> \<not> \<psi>"
proof -
  assume "\<turnstile>  \<phi> \<leftrightarrow> \<psi>"
  moreover
    let ?\<theta> = "((P#\<^bsub>CL\<^esub> \<phi>) \<leftrightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> \<psi>) \<rightarrow>\<^bsub>CL\<^esub> (\<not>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<phi>) \<leftrightarrow>\<^bsub>CL\<^esub> \<not>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<psi>))" 
    have "?\<theta> \<in> CL" by fastsimp
  moreover note evil_ClassAx.cl_translate [where \<phi>="?\<theta>"]
                evil_mp
  ultimately show ?thesis by fastsimp
qed

lemma evil_DD_eq: "\<turnstile> \<langle>-\<rangle> X (\<langle>-\<rangle> X \<phi>) \<leftrightarrow> \<langle>-\<rangle> X \<phi>"
proof -
  have "\<bottom> \<in> \<Down> (\<not> \<not> [-] X (\<not> \<phi>))" by simp
  moreover from evil_dneg_eq
    have "\<turnstile> \<not> \<not> [-] X (\<not> \<phi>) \<leftrightarrow> [-] X (\<not> \<phi>)" 
      by fast
  moreover note evil_sub [where \<chi>="\<langle>-\<rangle> X (\<langle>-\<rangle> X \<phi>)"
                            and \<phi>="\<not> \<not> [-] X (\<not> \<phi>)"
                            and \<psi>="[-] X (\<not> \<phi>)"]
  ultimately have "\<turnstile> \<langle>-\<rangle> X (\<langle>-\<rangle> X \<phi>) \<leftrightarrow> \<not> [-] X ([-] X (\<not> \<phi>))" by fastsimp
  moreover 
  from evil_BB_eq have "\<turnstile> [-] X ([-] X (\<not> \<phi>)) \<leftrightarrow> [-] X (\<not> \<phi>)"  .
  with evil_eq_neg have "\<turnstile> \<not> [-] X ([-] X (\<not> \<phi>)) \<leftrightarrow> \<langle>-\<rangle> X \<phi>" .
  moreover note evil_eq_trans
  ultimately show ?thesis by blast
qed
  
lemma evil_DDI_eq: "\<turnstile> \<langle>+\<rangle> X (\<langle>+\<rangle> X \<phi>) \<leftrightarrow> \<langle>+\<rangle> X \<phi>"
proof -
  have "\<bottom> \<in> \<Down> (\<not> \<not> [+] X (\<not> \<phi>))" by simp
  moreover from evil_dneg_eq
    have "\<turnstile> \<not> \<not> [+] X (\<not> \<phi>) \<leftrightarrow> [+] X (\<not> \<phi>)" 
      by fast
  moreover note evil_sub [where \<chi>="\<langle>+\<rangle> X (\<langle>+\<rangle> X \<phi>)"
                            and \<phi>="\<not> \<not> [+] X (\<not> \<phi>)"
                            and \<psi>="[+] X (\<not> \<phi>)"]
  ultimately have "\<turnstile> \<langle>+\<rangle> X (\<langle>+\<rangle> X \<phi>) \<leftrightarrow> \<not> [+] X ([+] X (\<not> \<phi>))" by fastsimp
  moreover 
  from evil_BBI_eq have "\<turnstile> [+] X ([+] X (\<not> \<phi>)) \<leftrightarrow> [+] X (\<not> \<phi>)"  .
  with evil_eq_neg have "\<turnstile> \<not> [+] X ([+] X (\<not> \<phi>)) \<leftrightarrow> \<langle>+\<rangle> X \<phi>" .
  moreover note evil_eq_trans
  ultimately show ?thesis by blast
qed

text{* Here are our psuedo box operators; the lemmas we shall prove reflect the
       lemmas associated with pseudo-negation. *}

definition evil_pBB :: "'b \<Rightarrow> ('a,'b) evil_form 
                           \<Rightarrow> ('a,'b) evil_form" ("[-]'")
  where
  "[-]' X \<phi> \<equiv> (if (\<exists> \<psi>. ([-] X \<psi>) = \<phi>)
                then \<phi>
                else [-] X \<phi>)"

definition evil_pBBI :: "'b \<Rightarrow> ('a,'b) evil_form 
                            \<Rightarrow> ('a,'b) evil_form" ("[+]'")
  where
  "[+]' X \<phi> \<equiv> (if (\<exists> \<psi>. ([+] X \<psi>) = \<phi>)
                then \<phi>
                else [+] X \<phi>)"

abbreviation evil_pDD :: "'b \<Rightarrow> ('a,'b) evil_form 
                           \<Rightarrow> ('a,'b) evil_form" ("\<langle>-\<rangle>'")
  where
  "\<langle>-\<rangle>' X \<phi> \<equiv> \<not> ([-]' X (\<not> \<phi>))"

abbreviation evil_pDDI :: "'b \<Rightarrow> ('a,'b) evil_form 
                            \<Rightarrow> ('a,'b) evil_form" ("\<langle>+\<rangle>'")
  where
  "\<langle>+\<rangle>' X \<phi> \<equiv> \<not> ([+]' X (\<not> \<phi>))"

declare evil_pBB_def [simp] 
    and evil_pBBI_def [simp]

text {* To start, we shall prove some basic syntactic theorems
        regarding our new operators. *}

lemma pBB_eq [simp]: "[-]' X ([-]' X \<phi>) = [-]' X \<phi>" by fastsimp
lemma pBBI_eq [simp]: "[+]' X ([+]' X \<phi>) = [+]' X \<phi>" by fastsimp

lemma pBB_BB_subform_sub: "\<Down> ([-]' X \<phi>) \<subseteq> \<Down> ([-] X \<phi>)" 
proof cases 
    assume "\<exists> \<psi>. ([-] X \<psi>) = \<phi>" thus ?thesis by fastsimp
    next assume "~ (\<exists> \<psi>. ([-] X \<psi>) = \<phi>)" 
           thus ?thesis by fastsimp
qed

lemma pBBI_BBI_subform_sub: "\<Down> ([+]' X \<phi>) \<subseteq> \<Down> ([+] X \<phi>)" 
proof cases 
    assume "\<exists> \<psi>. ([+] X \<psi>) = \<phi>" thus ?thesis by fastsimp
    next assume "~ (\<exists> \<psi>. ([+] X \<psi>) = \<phi>)" 
           thus ?thesis by fastsimp
qed    

text {* We have here now two utterly analogous proofs, illustrating
        our psuedo-operations are algebraically indistinguishable to
        the logic of EviL. *}

lemma evil_BB_pBB_eq: "\<turnstile> [-]' X \<phi> \<leftrightarrow> [-] X \<phi>"
proof cases
   assume "\<exists> \<psi>. ([-] X \<psi>) = \<phi>"
   with this obtain \<psi> where "[-] X \<psi> = \<phi>" by auto
   hence "[-] X \<psi> = [-]' X \<phi>" 
     and "[-] X ([-] X \<psi>) = [-] X \<phi>" by fastsimp+
   moreover from evil_eq_symm evil_BB_eq have
     "\<turnstile> [-] X \<psi> \<leftrightarrow> [-] X ([-] X \<psi>)" by fast
   ultimately show ?thesis by simp
 next
   assume "~ (\<exists> \<psi>. ([-] X \<psi>) = \<phi>)"
   hence "[-]' X \<phi> = [-] X \<phi>" by simp
   with evil_eq_refl show ?thesis by simp
qed

lemma evil_BBI_pBBI_eq: "\<turnstile> [+]' X \<phi> \<leftrightarrow> [+] X \<phi>"
proof cases
   assume "\<exists> \<psi>. ([+] X \<psi>) = \<phi>"
   with this obtain \<psi> where "[+] X \<psi> = \<phi>" by auto
   hence "[+] X \<psi> = [+]' X \<phi>" 
     and "[+] X ([+] X \<psi>) = [+] X \<phi>" by fastsimp+
   moreover from evil_eq_symm evil_BBI_eq have
     "\<turnstile> [+] X \<psi> \<leftrightarrow> [+] X ([+] X \<psi>)" by fast
   ultimately show ?thesis by simp
 next
   assume "~ (\<exists> \<psi>. ([+] X \<psi>) = \<phi>)"
   hence "[+]' X \<phi> = [+] X \<phi>" by simp
   with evil_eq_refl show ?thesis by simp
qed

lemma evil_eq_contrapose:
   "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<not> \<phi> \<leftrightarrow> \<not> \<psi>"
using evil_eq_weaken
      evil_eq_symm
      evil_contrapose
      evil_eq_intro [where \<phi>="\<not> \<phi>" and \<psi>="\<not> \<psi>"]
by fast

lemma evil_DD_pDD_eq: "\<turnstile> \<langle>-\<rangle>' X \<phi> \<leftrightarrow> \<langle>-\<rangle> X \<phi>"
using evil_BB_pBB_eq [where X="X" and \<phi>="\<not> \<phi>"]
      evil_eq_contrapose
by fast

lemma evil_DDI_pDDI_eq: "\<turnstile> \<langle>+\<rangle>' X \<phi> \<leftrightarrow> \<langle>+\<rangle> X \<phi>"
using evil_BBI_pBBI_eq [where X="X" and \<phi>="\<not> \<phi>"]
      evil_eq_contrapose
by fast

text {* Some consequences of the above are that every
        axiom involving @{term "[-]"} and @{term "[+]"}
        has a variation involving the pseudo-boxes.
        
        This constitutes a metalemma of sorts. *} 

lemma evil_pax4: "\<turnstile> [+]' X \<phi> \<rightarrow> \<phi>"
using evil_eq_weaken
      evil_BBI_pBBI_eq [where X="X" and \<phi>="\<phi>"]
      evil_ax4 [where X="X" and \<phi>="\<phi>"]
      evil_ClassAx.hs
by blast

lemma evil_pBBax4: "\<turnstile> [-]' X \<phi> \<rightarrow> \<phi>"
using evil_eq_weaken
      evil_BB_pBB_eq [where X="X" and \<phi>="\<phi>"]
      evil_BBax4 [where X="X" and \<phi>="\<phi>"]
      evil_ClassAx.hs
by blast

lemma evil_pax5: "\<turnstile> [+]' X \<phi> \<rightarrow> [+]' X ([+]' X \<phi>)" 
proof -
  from evil_eq_weaken
       evil_BBI_pBBI_eq [where X="X" and \<phi>="\<phi>"]
       evil_eq_symm
       evil_BBI_map [where X="X"
                       and \<phi>="[+] X \<phi>" 
                       and \<psi>="[+]' X \<phi>"]
  have "\<turnstile> [+] X ([+] X \<phi>) \<rightarrow> [+] X ([+]' X \<phi>)" by blast
  with evil_ax5 [where X="X" and \<phi>="\<phi>"]
       evil_ClassAx.hs
  have "\<turnstile> [+] X \<phi> \<rightarrow> [+] X ([+]' X \<phi>)" by blast
  with evil_eq_weaken
       evil_BBI_pBBI_eq [where X="X" and \<phi>="\<phi>"]
       evil_ClassAx.hs
  have "\<turnstile> [+]' X \<phi> \<rightarrow> [+] X ([+]' X \<phi>)" by blast
  with evil_BBI_pBBI_eq [where X="X" and \<phi>="[+]' X \<phi>"]
       evil_eq_symm
       evil_eq_weaken
       evil_ClassAx.hs
  show ?thesis by blast
qed
     
lemma evil_pBBax5: "\<turnstile> [-]' X \<phi> \<rightarrow> [-]' X ([-]' X \<phi>)" 
proof -
  from evil_eq_weaken
       evil_BB_pBB_eq [where X="X" and \<phi>="\<phi>"]
       evil_eq_symm
       evil_BB_map [where X="X"
                       and \<phi>="[-] X \<phi>" 
                       and \<psi>="[-]' X \<phi>"]
  have "\<turnstile> [-] X ([-] X \<phi>) \<rightarrow> [-] X ([-]' X \<phi>)" by blast
  with evil_BBax5 [where X="X" and \<phi>="\<phi>"]
       evil_ClassAx.hs
  have "\<turnstile> [-] X \<phi> \<rightarrow> [-] X ([-]' X \<phi>)" by blast
  with evil_eq_weaken
       evil_BB_pBB_eq [where X="X" and \<phi>="\<phi>"]
       evil_ClassAx.hs
  have "\<turnstile> [-]' X \<phi> \<rightarrow> [-] X ([-]' X \<phi>)" by blast
  with evil_BB_pBB_eq [where X="X" and \<phi>="[-]' X \<phi>"]
       evil_eq_symm
       evil_eq_weaken
       evil_ClassAx.hs
  show ?thesis by blast
qed

lemma evil_pax6: "\<turnstile> P# p \<rightarrow> [+]' X (P# p)"
using evil_ax6 [where X="X" and p="p"]
by simp

lemma evil_pax7: "\<turnstile> P# p \<rightarrow> [-]' X (P# p)"
using evil_ax7 [where X="X" and p="p"]
by simp

lemma evil_pax8: "\<turnstile> \<diamond> X \<phi> \<rightarrow> [-]' X (\<diamond> X \<phi>)"
using evil_ax8 [where X="X" and \<phi>="\<phi>"]
by simp

lemma evil_pBBIax8: "\<turnstile> \<box> X \<phi> \<rightarrow> [+]' X (\<box> X \<phi>)"
using evil_BBIax8 [where X="X" and \<phi>="\<phi>"]
by simp

lemma evil_pax9: "\<turnstile> \<box> X \<phi> \<rightarrow> \<box> X ([+]' Y \<phi>)"
using evil_eq_symm
      evil_eq_weaken
      evil_B_map [where X="X"]
      evil_BBI_pBBI_eq [where X="Y" and \<phi>="\<phi>"]
      evil_ax9 [where X="X" and Y="Y" and \<phi>="\<phi>"]
      evil_ClassAx.hs
by blast

lemma evil_pax10: "\<turnstile> \<box> X \<phi> \<rightarrow> \<box> X ([-]' Y \<phi>)"
using evil_eq_symm
      evil_eq_weaken
      evil_B_map [where X="X"]
      evil_BB_pBB_eq [where X="Y" and \<phi>="\<phi>"]
      evil_ax10 [where X="X" and Y="Y" and \<phi>="\<phi>"]
      evil_ClassAx.hs
by blast

--"Skipping axiom 11"

lemma evil_pax12: "\<turnstile> \<odot> X \<rightarrow> [-]' X (\<odot> X)"
using evil_ax12 [where X="X"]
by simp

lemma evil_pax13: "\<turnstile> \<phi> \<rightarrow> [+]' X (\<langle>-\<rangle>' X \<phi>)"
using evil_ax13 [where X="X" and \<phi>="\<phi>"]
by simp

lemma evil_pax14: "\<turnstile> \<phi> \<rightarrow> [-]' X (\<langle>+\<rangle>' X \<phi>)"
using evil_ax14 [where X="X" and \<phi>="\<phi>"]
by simp

--"Skipping axiom 15"

lemma evil_pax16: "\<turnstile> [-]' X (\<phi> \<rightarrow> \<psi>) \<rightarrow> [-]' X \<phi> \<rightarrow> [-]' X \<psi>"
proof -
   let ?A = "[-] X (\<phi> \<rightarrow> \<psi>)"
   and ?A' = "[-]' X (\<phi> \<rightarrow> \<psi>)"
   and ?B = "[-] X \<phi>"
   and ?B' = "[-]' X \<phi>"
   and ?C = "[-] X \<psi>"
   and ?C' = "[-]' X \<psi>"
   from evil_BB_pBB_eq [where X="X"]
        evil_eq_symm
        evil_eq_weaken
   have a: "\<turnstile> ?A' \<rightarrow> ?A"
    and b: "\<turnstile> ?B' \<rightarrow> ?B"
    and c: "\<turnstile> ?C \<rightarrow> ?C'" by blast+
   moreover from evil_ax16 have "\<turnstile> ?A \<rightarrow> ?B \<rightarrow> ?C" .
   with a evil_ClassAx.hs have "\<turnstile> ?A' \<rightarrow> ?B \<rightarrow> ?C" by blast
   hence "[?A'] :\<turnstile> ?B \<rightarrow> ?C" by simp 
   moreover from evil_ClassAx.lift [where \<Gamma>="[?A']"]
                 b c
   have "[?A'] :\<turnstile> ?B' \<rightarrow> ?B" and "[?A'] :\<turnstile> ?C \<rightarrow> ?C'" by blast+
   moreover note evil_ClassAx.lift_hs [where \<Gamma>="[?A']"]
   ultimately have "[?A'] :\<turnstile> ?B' \<rightarrow> ?C'" by blast
   thus ?thesis by simp
qed

lemma evil_pax17: "\<turnstile> [+]' X (\<phi> \<rightarrow> \<psi>) \<rightarrow> [+]' X \<phi> \<rightarrow> [+]' X \<psi>"
proof -
   let ?A = "[+] X (\<phi> \<rightarrow> \<psi>)"
   and ?A' = "[+]' X (\<phi> \<rightarrow> \<psi>)"
   and ?B = "[+] X \<phi>"
   and ?B' = "[+]' X \<phi>"
   and ?C = "[+] X \<psi>"
   and ?C' = "[+]' X \<psi>"
   from evil_BBI_pBBI_eq [where X="X"]
        evil_eq_symm
        evil_eq_weaken
   have a: "\<turnstile> ?A' \<rightarrow> ?A"
    and b: "\<turnstile> ?B' \<rightarrow> ?B"
    and c: "\<turnstile> ?C \<rightarrow> ?C'" by blast+
   moreover from evil_ax17 have "\<turnstile> ?A \<rightarrow> ?B \<rightarrow> ?C" .
   with a evil_ClassAx.hs have "\<turnstile> ?A' \<rightarrow> ?B \<rightarrow> ?C" by blast
   hence "[?A'] :\<turnstile> ?B \<rightarrow> ?C" by simp 
   moreover from evil_ClassAx.lift [where \<Gamma>="[?A']"]
                 b c
   have "[?A'] :\<turnstile> ?B' \<rightarrow> ?B" and "[?A'] :\<turnstile> ?C \<rightarrow> ?C'" by blast+
   moreover note evil_ClassAx.lift_hs [where \<Gamma>="[?A']"]
   ultimately have "[?A'] :\<turnstile> ?B' \<rightarrow> ?C'" by blast
   thus ?thesis by simp
qed

lemma evil_pBB_nec:
      assumes prv: "\<turnstile> \<phi>"
        shows "\<turnstile> [-]' X \<phi>"
using prv
proof -
   from prv evil_BB_nec have "\<turnstile> [-] X \<phi>" by fast
   with evil_BB_pBB_eq [where X="X"]
        evil_eq_symm evil_eq_mp
   show ?thesis by blast
qed

lemma evil_pBBI_nec:
      assumes prv: "\<turnstile> \<phi>"
        shows "\<turnstile> [+]' X \<phi>"
using prv
proof -
   from prv evil_BBI_nec have "\<turnstile> [+] X \<phi>" by fast
   with evil_BBI_pBBI_eq [where X="X"]
        evil_eq_symm evil_eq_mp
   show ?thesis by blast
qed

lemma evil_lift_pax16: 
   assumes notnil: "\<phi>s \<noteq> []"
     shows "\<turnstile> [-]' X (\<phi>s :\<rightarrow> \<psi>) 
              \<rightarrow> ((map ([-]' X) \<phi>s) :\<rightarrow> [-]' X \<psi>)"
using notnil
proof (induct \<phi>s)
 case Nil thus ?case by fast
 next case (Cons \<phi> \<phi>s)
  note ind_hyp = this
  show ?case
  proof cases
    assume "\<phi>s = []"
      with evil_pax16 [where X="X"]
        show ?case by fastsimp
    next 
    let ?A = "[-]' X ((\<phi> # \<phi>s) :\<rightarrow> \<psi>)"
    and ?B = "[-]' X \<phi>"
    and ?C = "[-]' X (\<phi>s :\<rightarrow> \<psi>)"
    and ?D = "((map ([-]' X) \<phi>s) :\<rightarrow> [-]' X \<psi>)"
    assume notnil: "\<phi>s \<noteq> []"
      with ind_hyp
           evil_ClassAx.lift [where \<Gamma>="[?A]"]
        have map: "[?A] :\<turnstile> ?C \<rightarrow> ?D" by fast
      from evil_pax16 [where X="X"
                         and \<phi>="\<phi>"
                         and \<psi>="\<phi>s :\<rightarrow> \<psi>"]
        have "[?A] :\<turnstile> ?B \<rightarrow> ?C" by simp
      with map
           evil_ClassAx.lift_hs [where \<Gamma>="[?A]"
                                   and \<phi>="?B"
                                   and \<psi>="?C"
                                   and \<chi>="?D"]
        show ?case by (simp del: evil_pBB_def)
  qed
qed

lemma evil_pBB_lift_map:
 assumes seq: "\<phi>s :\<turnstile> \<psi>"
   shows "(map ([-]' X) \<phi>s) :\<turnstile> [-]' X \<psi>"
using seq
proof (induct \<phi>s)
  case Nil with evil_pBB_nec [where X="X"]
    show ?case by fastsimp
  next case (Cons \<phi> \<phi>s)
    with evil_pBB_nec [where X="X" and \<phi>="(\<phi> # \<phi>s) :\<rightarrow> \<psi>"]
         evil_mp
         evil_lift_pax16 [where X="X"
                           and \<phi>s="\<phi> # \<phi>s"
                           and \<psi>="\<psi>"]
    show ?case by (simp del: evil_pBB_def)
qed

lemma evil_lift_pax17: 
   assumes notnil: "\<phi>s \<noteq> []"
     shows "\<turnstile> [+]' X (\<phi>s :\<rightarrow> \<psi>) 
              \<rightarrow> ((map ([+]' X) \<phi>s) :\<rightarrow> [+]' X \<psi>)"
using notnil
proof (induct \<phi>s)
 case Nil thus ?case by fast
 next case (Cons \<phi> \<phi>s)
  note ind_hyp = this
  show ?case
  proof cases
    assume "\<phi>s = []"
      with evil_pax17 [where X="X"]
        show ?case by fastsimp
    next 
    let ?A = "[+]' X ((\<phi> # \<phi>s) :\<rightarrow> \<psi>)"
    and ?B = "[+]' X \<phi>"
    and ?C = "[+]' X (\<phi>s :\<rightarrow> \<psi>)"
    and ?D = "((map ([+]' X) \<phi>s) :\<rightarrow> [+]' X \<psi>)"
    assume notnil: "\<phi>s \<noteq> []"
      with ind_hyp
           evil_ClassAx.lift [where \<Gamma>="[?A]"]
        have map: "[?A] :\<turnstile> ?C \<rightarrow> ?D" by fast
      from evil_pax17 [where X="X"
                         and \<phi>="\<phi>"
                         and \<psi>="\<phi>s :\<rightarrow> \<psi>"]
        have "[?A] :\<turnstile> ?B \<rightarrow> ?C" by simp
      with map
           evil_ClassAx.lift_hs [where \<Gamma>="[?A]"
                                   and \<phi>="?B"
                                   and \<psi>="?C"
                                   and \<chi>="?D"]
        show ?case by (simp del: evil_pBBI_def)
  qed
qed

lemma evil_pBBI_lift_map:
 assumes seq: "\<phi>s :\<turnstile> \<psi>"
   shows "(map ([+]' X) \<phi>s) :\<turnstile> [+]' X \<psi>"
using seq
proof (induct \<phi>s)
  case Nil with evil_pBBI_nec [where X="X"]
    show ?case by fastsimp
  next case (Cons \<phi> \<phi>s)
    with evil_pBBI_nec [where X="X" and \<phi>="(\<phi> # \<phi>s) :\<rightarrow> \<psi>"]
         evil_mp
         evil_lift_pax17 [where X="X"
                           and \<phi>s="\<phi> # \<phi>s"
                           and \<psi>="\<psi>"]
    show ?case by (simp del: evil_pBBI_def)
qed

text{* What follows is mostly repeat code from \texttt{Classic.thy}; 
       however, we also show logical results 
       which are analogous to the above.

       One change is that our destructor is total now;
       we shall find a crazy occasion to reuse it in a lemma. *}

primrec evil_dest:: "('a,'b) evil_form 
    \<Rightarrow> ('a,'b) evil_form" ("\<surd>")
  where  " \<surd> (P# p) = P# p"
       | "\<surd> \<bottom> = \<bottom>"
       | "\<surd> (\<odot> X) = \<odot> X"
       | "\<surd> (\<phi> \<rightarrow> \<psi>) = \<phi>"
       | "\<surd> (\<box> X \<phi>) = \<phi>"
       | "\<surd> ([-] X \<phi>) = \<phi>"
       | "\<surd> ([+] X \<phi>) = \<phi>"

abbreviation evil_pneg :: "('a,'b) evil_form 
         \<Rightarrow> ('a,'b) evil_form" ("\<sim>' _" [40] 40)
  where 
  "\<sim>' \<phi> \<equiv> (if (\<exists> \<psi>. (\<not> \<psi>) = \<phi>) 
             then (\<surd> \<phi>) 
             else \<not> \<phi>)"

notation
evil_ClassAx.pneg ("\<sim> _" [40] 40)

lemmas pneg_def = evil_ClassAx.pneg_def

--"The new pseudo-negation is constructive(?) so always simplify to it" 
lemma pneg_eq [simp]: "(\<sim> \<phi>) = (\<sim>' \<phi>)"
proof cases
   assume a: "\<exists> \<psi>. (\<not> \<psi>) = \<phi>"
   hence "\<exists>! \<psi>. (\<not> \<psi>) = \<phi>" by fastsimp
   moreover 
   then have "(\<not> \<sim>' \<phi>) = \<phi>" by fastsimp
   moreover from a 
                 pneg_def [where \<phi>="\<phi>"]
   have "(\<sim> \<phi>) = (SOME \<psi> . (\<not> \<psi>) = \<phi>)" by fastsimp
   moreover note
     some1_equality [where P="% \<psi> . (\<not> \<psi>) = \<phi>"
                       and a="\<sim>' \<phi>"]
   ultimately show ?thesis by auto
  next
   assume b: "~ (\<exists> \<psi>. (\<not> \<psi>) = \<phi>)"
   with pneg_def [where \<phi>="\<phi>"]
   show ?thesis by fastsimp
qed

--"These silly lemmas show how pseudo-negation plays"
--"with boxes and pseudo-boxes"
lemma evil_pBB_pneg_eq [simp]: "(\<sim> [-]' X \<phi>) = (\<not> [-]' X \<phi>)"
   by fastsimp

lemma evil_pBBI_pneg_eq [simp]: "(\<sim> [+]' X \<phi>) = (\<not> [+]' X \<phi>)"
   by fastsimp

lemma evil_B_pneg_eq [simp]: "(\<sim> \<box> X \<phi>) = (\<not> \<box> X \<phi>)"
   by fastsimp

lemma evil_pBB_pneg_eq2 [simp]: "(\<sim> \<not> [-]' X \<phi>) = ([-]' X \<phi>)"
   by fastsimp

lemma evil_pBBI_pneg_eq2 [simp]: "(\<sim> \<not> [+]' X \<phi>) = ([+]' X \<phi>)"
   by fastsimp

lemma evil_B_pneg_eq2 [simp]: "(\<sim> \<not> \<box> X \<phi>) = (\<box> X \<phi>)"
   by fastsimp

lemma evil_Bot_pneg_eq [simp]: "(\<sim> \<bottom>) = (\<not> \<bottom>)" by fastsimp

lemma evil_Bot_pneg_eq2 [simp]: "(\<sim> (\<not> \<bottom>)) = \<bottom>" by fastsimp

--"As we can see pseudo-negation is logically the same"
--"as negation"
lemma evil_pneg_eq: "\<turnstile> \<sim> \<phi> \<leftrightarrow> \<not> \<phi>"
proof cases
   assume "\<exists> \<psi>. (\<not> \<psi>) = \<phi>"
   with this obtain \<psi> where "(\<not> \<psi>) = \<phi>" by auto
   moreover hence "(\<sim> \<phi>) = \<psi>" by fastsimp
   moreover note evil_dneg_eq evil_eq_symm
   ultimately show ?thesis by fastsimp
 next
   assume "~ (\<exists> \<psi>. (\<not> \<psi>) = \<phi>)"
   with evil_eq_refl show ?thesis by fastsimp
qed

lemma evil_pdneg_eq: "\<turnstile> \<not> \<sim> \<phi> \<leftrightarrow> \<phi>"
proof cases
   assume "\<exists> \<psi>. (\<not> \<psi>) = \<phi>"
   with someI_ex [where P="% \<psi> . (\<not> \<psi>) = \<phi>"] 
       evil_ClassAx.pneg_def [where \<phi>="\<phi>"]
     have "(\<not> \<sim> \<phi>) = \<phi>" by fastsimp
   with evil_eq_refl show ?thesis by fastsimp
 next
   assume "~ (\<exists> \<psi>. (\<not> \<psi>) = \<phi>)"
   with evil_eq_refl evil_dneg_eq 
   show ?thesis by fastsimp
qed

lemma neg_pneg_sem_eq [simp]: "(M,w |\<turnstile> \<sim> \<phi>) = (~ (M,w |\<turnstile> \<phi>))"
proof cases
   assume "\<exists> \<psi> . (\<not> \<psi>) = \<phi>"
   hence "(\<not> \<sim> \<phi>) = \<phi>" by fastsimp
   moreover
   have "(~ (M,w |\<turnstile> \<not> \<sim> \<phi>)) = (M,w |\<turnstile> \<sim> \<phi>)" 
     by simp
   ultimately show ?thesis by fastsimp
 next
   assume "~ (\<exists> \<psi>. (\<not> \<psi>) = \<phi>)"
   hence "(\<sim> \<phi>) = (\<not> \<phi>)" by fastsimp
   moreover
   have "(~ (M,w |\<turnstile> \<phi>)) = (M,w |\<turnstile> \<not> \<phi>)" by simp
   ultimately show ?thesis by fastsimp
qed

text{* With these preliminaries out of the way we turn to tackling
       issues related to the Fisher-Ladner closure.  Observe that our
       semantics specify an unknown number of agents; this could
       potentially be an issue.  However, we
       know for a given formula it can only mention a finite number
       of agents; hence the Fisher-Ladner subformula construction
       need only mention these agents.

       To accomplish this, we first introduce an operation: *}

primrec dudes
   :: "('a,'b) evil_form \<Rightarrow> 'b set" ("\<delta>")
where
    "\<delta> (P# p) = {}"
  | "\<delta> \<bottom> = {}"
  | "\<delta> (\<odot> X) = {X}"
  | "\<delta> (\<phi> \<rightarrow> \<psi>) = (\<delta> \<phi>) \<union> (\<delta> \<psi>)"
  | "\<delta> (\<box> X \<phi>) = {X} \<union>  (\<delta> \<phi>)"
  | "\<delta> ([-] X \<phi>) = {X} \<union>  (\<delta> \<phi>)"
  | "\<delta> ([+] X \<phi>) = {X} \<union>  (\<delta> \<phi>)"

lemma finite_dudes: "finite (\<delta> \<phi>)"
  by (induct \<phi>) simp_all

text{* The function @{term "dudes"}, gathers a list of the people mentioned by the formula it takes as an 
       argument. We shall use it as follows: our Fisher-Ladner closure will be programmed to
       carry around a little state which correspond to the @{term "dudes"} mentioned 
       by the top level formula. These people are the only people we care about in our universe. 
       
       We now turn to giving the subformula set; as is evident, it's very large. Moreover, unlike the
       Fisher-Ladner closure, it's not a \emph{closure}, but this is irrelevant for our purposes anyway.*}

primrec evil_FL :: "'b set
                 \<Rightarrow> ('a,'b) evil_form 
                 \<Rightarrow> ('a,'b) evil_form set" ("\<Sigma>") where
  evil_FL_P: 
    "\<Sigma> \<Delta> (P# p) =   {P# p, \<not> (P# p), \<bottom>, \<not> \<bottom>} 
                  \<union> {[-]' X (P# p) | X. X \<in> \<Delta>}
                  \<union> {[+]' X (P# p) | X. X \<in> \<Delta>}
                  \<union> {\<not> [-]' X (P# p) | X. X \<in> \<Delta>}
                  \<union> {\<not> [+]' X (P# p) | X. X \<in> \<Delta>}"
 | evil_FL_PP: 
    "\<Sigma> \<Delta> (\<odot> X) = {\<odot> X, \<not> (\<odot> X), \<bottom>, \<not> \<bottom>, 
                  [-]' X (\<odot> X), \<not> [-]' X (\<odot> X)}"
 | evil_FL_Bot: 
    "\<Sigma> \<Delta> \<bottom> = {\<bottom>, \<not> \<bottom>}"
 | evil_FL_Imp: 
    "\<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>) = { \<phi> \<rightarrow> \<psi>, \<not> (\<phi> \<rightarrow> \<psi>), 
                      \<phi>, \<psi>, \<not> \<phi>, \<not> \<psi>, \<bottom>, \<not> \<bottom>} 
                   \<union> (\<Sigma> \<Delta> \<phi>) \<union> (\<Sigma> \<Delta> \<psi>)"
| evil_FL_B: 
     "\<Sigma> \<Delta> (\<box> X \<phi>) = { \<box> X \<phi>, \<not> \<box> X \<phi>, 
                      [+]' X (\<box> X \<phi>), \<not> [+]' X (\<box> X \<phi>),
                       \<phi>, \<bottom>, \<not> \<bottom>}
                    \<union> {\<box> X ([-]' Y \<phi>) | Y. Y \<in> \<Delta>}
                    \<union> {\<not> \<box> X ([-]' Y \<phi>) | Y. Y \<in> \<Delta>}
                    \<union> {\<box> X ([+]' Y \<phi>) | Y. Y \<in> \<Delta>}
                    \<union> {\<not> \<box> X ([+]' Y \<phi>) | Y. Y \<in> \<Delta>}
                    \<union> {[-]' Y \<phi> | Y. Y \<in> \<Delta>}
                    \<union> {\<not> [-]' Y \<phi> | Y. Y \<in> \<Delta>}
                    \<union> {[+]' Y \<phi> | Y. Y \<in> \<Delta>}
                    \<union> {\<not> [+]' Y \<phi> | Y. Y \<in> \<Delta>}
                    \<union> (\<Sigma> \<Delta> \<phi>)"
 | evil_FL_BB: 
     "\<Sigma> \<Delta> ([+] X \<phi>) = { [+] X \<phi>, \<not> [+] X \<phi>, 
                        \<phi>, \<not> \<phi>, \<bottom>, \<not> \<bottom>}
                      \<union> (\<Sigma> \<Delta> \<phi>)"
 | evil_FL_BBI: 
     "\<Sigma> \<Delta> ([-] X \<phi>) = { [-] X \<phi>, \<not> [-] X \<phi>, 
                        \<phi>, \<not> \<phi>, \<bottom>, \<not> \<bottom>}
                      \<union> (\<Sigma> \<Delta> \<phi>)"

lemma finite_evil_FL:
      assumes fin_dudes: "finite \<Delta>"
        shows "finite (\<Sigma> \<Delta> \<phi>)"  
           --"like the letters of a"
           --"fraternity of EviL..."
using fin_dudes
by (induct \<phi>) simp_all

lemma evil_FL_refl: "\<phi> \<in> \<Sigma> \<Delta> \<phi>"
  by (induct \<phi>, simp_all) 

lemma pneg_evil_FL: "\<forall>\<psi> \<in> (\<Sigma> \<Delta> \<phi>). (\<sim> \<psi>) \<in> (\<Sigma> \<Delta> \<phi>)"
proof (induct \<phi>)
       case E_P thus ?case by fastsimp
  next case E_Bot thus ?case by fastsimp
  next case E_PP thus ?case by fastsimp
  next case E_B thus ?case by (unfold evil_FL_B,
                               blast intro: evil_FL_refl
                                            evil_B_pneg_eq
                                            evil_B_pneg_eq2
                                            evil_pBB_pneg_eq
                                            evil_pBB_pneg_eq2
                                            evil_pBBI_pneg_eq
                                            evil_pBBI_pneg_eq2
                                            evil_Bot_pneg_eq
                                            evil_Bot_pneg_eq2)
  next case E_Imp thus ?case by (simp,auto)
  next case E_BB thus ?case by fastsimp
  next case E_BBI thus ?case by fastsimp
qed

lemma evil_FL_subform_refl: "\<Down> \<phi> \<subseteq> \<Sigma> \<Delta> \<phi>"
proof (induct \<phi>)
       case E_P thus ?case by simp
  next case E_Bot thus ?case by simp
  next case E_PP thus ?case by simp
  next case (E_Imp \<phi> \<psi>)
       note ih = this 
       from ih have "\<Down> \<phi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" by fastsimp
       moreover
       have "\<Sigma> \<Delta> \<psi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" by fastsimp
         with ih have "\<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" by fast
       ultimately show ?case by simp
  next case (E_B X \<phi>) 
       moreover have "\<Sigma> \<Delta> \<phi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)" by fastsimp
       ultimately show ?case by simp
  next case (E_BB X \<phi>)
       moreover have "\<Sigma> \<Delta> \<phi> \<subseteq> \<Sigma> \<Delta> ([-] X \<phi>)" by fastsimp
       ultimately show ?case by simp
  next case (E_BBI X \<phi>)
       moreover have "\<Sigma> \<Delta> \<phi> \<subseteq> \<Sigma> \<Delta> ([+] X \<phi>)" by fastsimp
       ultimately show ?case by simp
qed

lemma evil_FL_subforms: "\<forall> \<psi> \<in> \<Sigma> \<Delta> \<phi>. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> \<phi>"
proof (induct \<phi>)
       case E_P thus ?case by fastsimp
  next case E_Bot thus ?case by fastsimp
  next case E_PP thus ?case by fastsimp
  next case (E_Imp \<phi> \<psi>)
       hence ih1: "\<forall>\<chi>\<in>\<Sigma> \<Delta> \<phi>. \<Down> \<chi> \<subseteq> \<Sigma> \<Delta> \<phi>"
         and ih2: "\<forall>\<chi>\<in>\<Sigma> \<Delta> \<psi>. \<Down> \<chi> \<subseteq> \<Sigma> \<Delta> \<psi>" by fast+
       have "\<Sigma> \<Delta> \<phi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" by fastsimp
       with ih1 have 
            "\<forall> \<chi> \<in> \<Sigma> \<Delta> \<phi>. \<Down> \<chi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" by fast
       moreover
       have "\<Sigma> \<Delta> \<psi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" by fastsimp
       with ih2 have 
            "\<forall> \<chi> \<in> \<Sigma> \<Delta> \<psi>. \<Down> \<chi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" by fast
       ultimately have 
        "\<forall>\<chi> \<in> (\<Sigma> \<Delta> \<phi>) \<union> (\<Sigma> \<Delta> \<psi>). \<Down>\<chi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)"
           by fastsimp
       moreover
       from evil_FL_subform_refl [where \<phi>="\<phi> \<rightarrow> \<psi>"]
       have "{\<phi>,\<psi>} \<union> (\<Down> \<phi>) \<union> (\<Down> \<psi>) \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" 
            by simp
       hence "\<Down> \<phi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" 
         and "\<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<phi> \<rightarrow> \<psi>)" by fast+
       ultimately show ?case by simp
  next case (E_B X \<phi>)
       note ih = this
       --"I'm really pretty sad about this,"
       --"but I must resort to using this very stupid lemma :("
       { fix A B C D; 
           assume "A = B \<or> A = C" and "B \<subseteq> D" and "C \<subseteq> D"
           hence "A \<subseteq> D" by fastsimp }
       note sublem = this
       have sub: "\<Sigma> \<Delta> \<phi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)" by fastsimp
       with ih have "\<forall>\<psi>\<in>\<Sigma> \<Delta> \<phi>. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)" by fast
       moreover from sub evil_FL_subform_refl
       have reflI: "\<Down> \<phi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)" by fast  
       moreover
       let ?A = "{\<box> X ([-]' Y \<phi>) |Y. Y \<in> \<Delta>}" 
       and ?B = "{\<not> \<box> X ([-]' Y \<phi>) |Y. Y \<in> \<Delta>}"
       and ?C = "{\<box> X ([+]' Y \<phi>) |Y. Y \<in> \<Delta>}"                         
       and ?D = "{\<not> \<box> X ([+]' Y \<phi>) |Y. Y \<in> \<Delta>}"
       and ?E = "{[-]' Y \<phi> |Y. Y \<in> \<Delta>}"
       and ?F = "{\<not> [-]' Y \<phi> |Y. Y \<in> \<Delta>}"
       and ?G = "{[+]' Y \<phi> |Y. Y \<in> \<Delta>}"
       and ?H = "{\<not> [+]' Y \<phi> |Y. Y \<in> \<Delta>}"

       from reflI have reflII:
            "{\<phi>} \<union> \<Down> \<phi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)" by simp
       { fix \<chi>; assume "\<Down> \<chi> = {\<phi>} \<union> \<Down> \<phi> \<or> \<Down> \<chi> = \<Down> \<phi>"      
         with sublem [where A2="\<Down> \<chi>"
                        and B2="{\<phi>} \<union> \<Down> \<phi>"
                        and C2="\<Down>\<phi>" 
                        and D2="\<Sigma> \<Delta> (\<box> X \<phi>)"]
              reflI reflII
         have "\<Down> \<chi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)" by fast }
       note EGintro = this
       have "\<forall>\<psi>\<in>?E. \<Down> \<psi> = {\<phi>} \<union> \<Down> \<phi> \<or> \<Down> \<psi> = \<Down> \<phi>"
            "\<forall>\<psi>\<in>?G. \<Down> \<psi> = {\<phi>} \<union> \<Down> \<phi> \<or> \<Down> \<psi> = \<Down> \<phi>"
               by fastsimp+
       with EGintro
       have "\<forall>\<psi>\<in>?E. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
        and "\<forall>\<psi>\<in>?G. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)" by blast+
       note EGsub = this

       moreover
       have "\<forall>\<psi>\<in>?A. \<surd>\<psi> \<in> ?E"
        and "\<forall>\<psi>\<in>?C. \<surd>\<psi> \<in> ?G"
        and "\<forall>\<psi>\<in>?F. \<surd>\<psi> \<in> ?E"
        and "\<forall>\<psi>\<in>?H. \<surd>\<psi> \<in> ?G"
            by (fastsimp simp del: evil_pBB_def
                                   evil_pBBI_def)+

       with EGsub have
            "\<forall>\<psi>\<in>?A. {\<surd>\<psi>} \<union> \<Down> (\<surd>\<psi>) \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
        and "\<forall>\<psi>\<in>?C. {\<surd>\<psi>} \<union> \<Down> (\<surd>\<psi>) \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
        and "\<forall>\<psi>\<in>?F. {\<surd>\<psi>, \<bottom>} \<union> \<Down> (\<surd>\<psi>) \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
        and "\<forall>\<psi>\<in>?H. {\<surd>\<psi>, \<bottom>} \<union> \<Down> (\<surd>\<psi>) \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
            by simp+
       note destsub = this

       have "\<forall>\<psi>\<in>?A. \<Down> \<psi> = {\<surd>\<psi>} \<union> \<Down> (\<surd>\<psi>)"
        and "\<forall>\<psi>\<in>?C. \<Down> \<psi> = {\<surd>\<psi>} \<union> \<Down> (\<surd>\<psi>)"
        and "\<forall>\<psi>\<in>?F. \<Down> \<psi> = {\<surd>\<psi>, \<bottom>} \<union> \<Down> (\<surd>\<psi>)"
        and "\<forall>\<psi>\<in>?H. \<Down> \<psi> = {\<surd>\<psi>, \<bottom>} \<union> \<Down> (\<surd>\<psi>)"
            by (fastsimp simp del: evil_pBB_def
                                   evil_pBBI_def)+

       with destsub 
       have "\<forall>\<psi>\<in>?A. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
        and "\<forall>\<psi>\<in>?C. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
        and "\<forall>\<psi>\<in>?F. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
        and "\<forall>\<psi>\<in>?H. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
            by simp+
       note ACFHsub = this

       moreover
       have "\<forall>\<psi>\<in>?B. \<surd>\<psi> \<in> ?A"
        and "\<forall>\<psi>\<in>?D. \<surd>\<psi> \<in> ?C"
            by (fastsimp simp del: evil_pBB_def
                                   evil_pBBI_def)+

       with ACFHsub have
            "\<forall>\<psi>\<in>?B. {\<surd>\<psi>, \<bottom>} \<union> \<Down> (\<surd>\<psi>) \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
        and "\<forall>\<psi>\<in>?D. {\<surd>\<psi>, \<bottom>} \<union> \<Down> (\<surd>\<psi>) \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
            by simp+
       note destsub = this

       have "\<forall>\<psi>\<in>?B. \<Down> \<psi> = {\<surd>\<psi>, \<bottom>} \<union> \<Down> (\<surd>\<psi>)"
        and "\<forall>\<psi>\<in>?D. \<Down> \<psi> = {\<surd>\<psi>, \<bottom>} \<union> \<Down> (\<surd>\<psi>)"
            by (fastsimp simp del: evil_pBB_def
                                   evil_pBBI_def)+

       with destsub 
       have "\<forall>\<psi>\<in>?B. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
        and "\<forall>\<psi>\<in>?D. \<Down> \<psi> \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
            by simp+

       moreover from reflI have
           "\<Down> ([+]' X (\<box> X \<phi>)) \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)"
       and "\<Down> (\<not> [+]' X (\<box> X \<phi>)) \<subseteq> \<Sigma> \<Delta> (\<box> X \<phi>)" 
           by simp+

       ultimately show ?case by (simp del: evil_pBB_def
                                           evil_pBBI_def
                                      add: Ball_def)
  next case (E_BB X \<phi>)
       with evil_FL_subform_refl
       show ?case by fastsimp
  next case (E_BBI X \<phi>)
       with evil_FL_subform_refl
       show ?case by fastsimp
qed

lemma evil_FL_BB_to_pBB: "\<forall> \<psi> X.  [-] X \<psi> \<in> \<Sigma> \<Delta> \<phi> 
                              \<longrightarrow>  [-]' X \<psi> \<in> \<Sigma> \<Delta> \<phi>"
proof(induct \<phi>)
       case E_P thus ?case by simp
  next case E_Bot thus ?case by simp
  next case E_PP thus ?case by simp
  next case E_Imp thus ?case by fastsimp
  next case (E_B Y \<phi>) 
    note ih = this
    { fix \<psi>; fix X; assume mem: "[-] X \<psi> \<in> \<Sigma> \<Delta> (\<box> Y \<phi>)"
       let ?A = "{\<box> X ([-]' Y \<phi>) |Y. Y \<in> \<Delta>}" 
       and ?B = "{\<not> \<box> X ([-]' Y \<phi>) |Y. Y \<in> \<Delta>}"
       and ?C = "{\<box> X ([+]' Y \<phi>) |Y. Y \<in> \<Delta>}"                         
       and ?D = "{\<not> \<box> X ([+]' Y \<phi>) |Y. Y \<in> \<Delta>}"
       and ?F = "{\<not> [-]' Y \<phi> |Y. Y \<in> \<Delta>}"
       and ?G = "{[+]' Y \<phi> |Y. Y \<in> \<Delta>}"
       and ?H = "{\<not> [+]' Y \<phi> |Y. Y \<in> \<Delta>}"
       have "[-] X \<psi> \<notin> ?A" 
        and "[-] X \<psi> \<notin> ?B"
        and "[-] X \<psi> \<notin> ?C"
        and "[-] X \<psi> \<notin> ?D"
        and "[-] X \<psi> \<notin> ?F"
        and "[-] X \<psi> \<notin> ?G"
        and "[-] X \<psi> \<notin> ?H"
        and "[-] X \<psi> \<noteq> (\<box> Y \<phi>)"
        and "[-] X \<psi> \<noteq> (\<not> \<box> Y \<phi>)" 
        and "[-] X \<psi> \<noteq> ([+]' Y (\<box> Y \<phi>))"
        and "[-] X \<psi> \<noteq> (\<not> [+]' Y (\<box> Y \<phi>))"
        and "[-] X \<psi> \<noteq> \<bottom>"
        and "[-] X \<psi> \<noteq> (\<not> \<bottom>)"
          by auto+
       with mem 
       have  tri1:
             "[-] X \<psi> = \<phi> \<or> 
              [-] X \<psi> \<in> {[-]' Z \<phi> | Z. Z \<in> \<Delta>} \<or>
              [-] X \<psi> \<in> \<Sigma> \<Delta> \<phi>" 
       by (fastsimp del: evil_pBB_def
                         evil_pBBI_def)
       have "[-] X \<psi> \<in> {[-]' Z \<phi> | Z. Z \<in> \<Delta>}
             \<Longrightarrow> [-] X \<psi> = \<phi> \<or> [-] X \<psi> = [-]' X \<psi>" 
         by fastsimp
       with tri1 have tri2:
           "[-] X \<psi> = \<phi> \<or> 
            [-] X \<psi> = [-]' X \<psi> \<or>
            [-] X \<psi> \<in> \<Sigma> \<Delta> \<phi>" by fastsimp
       from evil_FL_refl [where \<Delta>="\<Delta>" and \<phi>="\<phi>"]
       have "[-] X \<psi> = \<phi> \<Longrightarrow> [-] X \<psi> \<in> \<Sigma> \<Delta> \<phi>" 
         by fastsimp
       with tri2 have 
           "[-] X \<psi> = [-]' X \<psi> \<or>
            [-] X \<psi> \<in> \<Sigma> \<Delta> \<phi>" by fastsimp
       with ih
       have bi: "[-] X \<psi> = [-]' X \<psi> \<or> [-]' X \<psi> \<in> \<Sigma> \<Delta> (\<box> Y \<phi>)"
         by (fastsimp simp del: evil_pBB_def
                                evil_pBBI_def)
       from mem
       have "[-] X \<psi> = [-]' X \<psi> \<Longrightarrow> [-]' X \<psi> \<in> \<Sigma> \<Delta> (\<box> Y \<phi>)"
         by (fastsimp simp del: evil_pBB_def
                                evil_pBBI_def)
       with bi have "[-]' X \<psi> \<in> \<Sigma> \<Delta> (\<box> Y \<phi>)" by fastsimp }
    thus ?case by fast
  next case E_BB thus ?case by fastsimp
  next case E_BBI thus ?case by fastsimp
qed

lemma evil_FL_BBI_to_pBBI: "\<forall> \<psi> X.  [+] X \<psi> \<in> \<Sigma> \<Delta> \<phi> 
                              \<longrightarrow>  [+]' X \<psi> \<in> \<Sigma> \<Delta> \<phi>"
proof(induct \<phi>)
       case E_P thus ?case by simp
  next case E_Bot thus ?case by simp
  next case E_PP thus ?case by simp
  next case E_Imp thus ?case by fastsimp
  next case (E_B Y \<phi>) 
    note ih = this
    { fix \<psi>; fix X; assume mem: "[+] X \<psi> \<in> \<Sigma> \<Delta> (\<box> Y \<phi>)"
       let ?A = "{\<box> X ([-]' Y \<phi>) |Y. Y \<in> \<Delta>}" 
       and ?B = "{\<not> \<box> X ([-]' Y \<phi>) |Y. Y \<in> \<Delta>}"
       and ?C = "{\<box> X ([+]' Y \<phi>) |Y. Y \<in> \<Delta>}"                         
       and ?D = "{\<not> \<box> X ([+]' Y \<phi>) |Y. Y \<in> \<Delta>}"
       and ?E = "{[-]' Y \<phi> |Y. Y \<in> \<Delta>}"
       and ?F = "{\<not> [-]' Y \<phi> |Y. Y \<in> \<Delta>}"
       and ?H = "{\<not> [+]' Y \<phi> |Y. Y \<in> \<Delta>}"
       have "[+] X \<psi> \<notin> ?A" 
        and "[+] X \<psi> \<notin> ?B"
        and "[+] X \<psi> \<notin> ?C"
        and "[+] X \<psi> \<notin> ?D"
        and "[+] X \<psi> \<notin> ?E"
        and "[+] X \<psi> \<notin> ?F"
        and "[+] X \<psi> \<notin> ?H"
        and "[+] X \<psi> \<noteq> (\<box> Y \<phi>)"
        and "[+] X \<psi> \<noteq> (\<not> \<box> Y \<phi>)" 
        and "[-] X \<psi> \<noteq> (\<not> [+]' Y (\<box> Y \<phi>))"
        and "[-] X \<psi> \<noteq> \<bottom>"
        and "[-] X \<psi> \<noteq> (\<not> \<bottom>)"
          by auto+
       with mem 
       have quatro1:
             "[+] X \<psi> = \<phi> \<or>
              [+] X \<psi> = [+]' Y (\<box> Y \<phi>) \<or>
              [+] X \<psi> \<in> {[+]' Z \<phi> | Z. Z \<in> \<Delta>} \<or>
              [+] X \<psi> \<in> \<Sigma> \<Delta> \<phi>" 
       by (fastsimp del: evil_pBB_def
                         evil_pBBI_def)
       have "[+] X \<psi> = [+]' Y (\<box> Y \<phi>) 
             \<Longrightarrow> [+] X \<psi> = [+]' X \<psi>" by fastsimp
       with quatro1 have quatro2:
             "[+] X \<psi> = \<phi> \<or>
              [+] X \<psi> = [+]' X \<psi> \<or>
              [+] X \<psi> \<in> {[+]' Z \<phi> | Z. Z \<in> \<Delta>} \<or>
              [+] X \<psi> \<in> \<Sigma> \<Delta> \<phi>"  by fastsimp
       have "[+] X \<psi> \<in> {[+]' Z \<phi> | Z. Z \<in> \<Delta>}
             \<Longrightarrow> [+] X \<psi> = \<phi> \<or> [+] X \<psi> = [+]' X \<psi>" by fastsimp
       with quatro2 have tri:
             "[+] X \<psi> = \<phi> \<or>
              [+] X \<psi> = [+]' X \<psi> \<or>
              [+] X \<psi> \<in> \<Sigma> \<Delta> \<phi>"  by fastsimp 
       from evil_FL_refl [where \<Delta>="\<Delta>" and \<phi>="\<phi>"]
       have "[+] X \<psi> = \<phi> \<Longrightarrow> [+] X \<psi> \<in> \<Sigma> \<Delta> \<phi>" 
         by fastsimp
       with tri have 
           "[+] X \<psi> = [+]' X \<psi> \<or>
            [+] X \<psi> \<in> \<Sigma> \<Delta> \<phi>" by fastsimp
       with ih
       have bi: "[+] X \<psi> = [+]' X \<psi> \<or> [+]' X \<psi> \<in> \<Sigma> \<Delta> (\<box> Y \<phi>)"
         by (fastsimp simp del: evil_pBB_def
                                evil_pBBI_def)
       from mem
       have "[+] X \<psi> = [+]' X \<psi> \<Longrightarrow> [+]' X \<psi> \<in> \<Sigma> \<Delta> (\<box> Y \<phi>)"
         by (fastsimp simp del: evil_pBB_def
                                evil_pBBI_def)
       with bi have "[+]' X \<psi> \<in> \<Sigma> \<Delta> (\<box> Y \<phi>)" by fastsimp }
    thus ?case by fast
  next case E_BB thus ?case by fastsimp
  next case E_BBI thus ?case by fastsimp
qed

text {* With all of the above out of our way, we are ready to provide
        the subformula canonical model for a given formula @{term "\<phi>"}.
        However, note that this model will only be @{text "partly_evil"}.
        We shall help ourself to the @{text "\<angle>"} symbol for this construction;
        as far as we can tell from the literature, the meaning of @{text "\<angle>"} 
        appears to have been forgotten by logicians as it is never employed. *}

notation
evil_ClassAx.Atoms ("Atoms") and
evil_ClassAx.lift_imp (infix ":\<rightarrow>" 24)

abbreviation pevil_canonical_model ::
  "('a,'b) evil_form
   \<Rightarrow> (('a,'b) evil_form set,'a,'b) evil_kripke" ("\<angle>")
where
"\<angle> \<phi> \<equiv> 
  \<lparr> W = Atoms (\<Sigma> (\<delta> \<phi>) \<phi>),
    V = (\<lambda> w p. (P# p) \<in> w),
    PP = (\<lambda> X. {w.(\<odot> X) \<in> w}),
    RB = (\<lambda> X. 
           {(w,v). {w,v} \<subseteq> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>) \<and>
                   {\<psi>. (\<box> X \<psi>) \<in> w} \<subseteq> v}),

    RBB = (\<lambda> X. 
           {(w,v). {w,v} \<subseteq> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>) \<and>
                   {\<psi>. ([-]' X \<psi>) \<in> w} \<subseteq> v \<and>
                   {([-]' X \<psi>) | \<psi>. ([-]' X \<psi>) \<in> w} \<subseteq> v \<and>
                   {\<psi>. ([+]' X \<psi>) \<in> v} \<subseteq> w \<and>
                   {([+]' X \<psi>) | \<psi>. ([+]' X \<psi>) \<in> v} \<subseteq> w}),
    RBBI = (\<lambda> X. 
            {(w,v). {w,v} \<subseteq> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>) \<and>
                    {\<psi>. ([+]' X \<psi>) \<in> w} \<subseteq> v \<and>
                    {([+]' X \<psi>) | \<psi>. ([-]' X \<psi>) \<in> w} \<subseteq> v \<and>
                    {\<psi>. ([-]' X \<psi>) \<in> v} \<subseteq> w \<and>
                    {([-]' X \<psi>) | \<psi>. ([-]' X \<psi>) \<in> v} \<subseteq> w})
  \<rparr>"

text {* To prove the truth lemma for @{term "\<angle> \<phi>"}
 we shall prove the inductive steps for the boxes seperately.

 However, we first prove a variety of lemmas regarding basic
 propertiers of atoms. *}

--"I will admit that my ealier formulation of Atoms is awkward"
--"This new lemma declares a simplification I will want"
lemma evil_Atoms_simp[simp]:
   "(\<Gamma> \<in> Atoms \<Phi>) \<equiv>  
     (\<Gamma> \<subseteq> \<Phi> \<and>
     (\<forall>\<phi>\<in>\<Phi>. \<phi> \<in> \<Gamma> \<or> (\<sim> \<phi>) \<in> \<Gamma>) \<and>
     ~ (list \<Gamma> :\<turnstile> \<bottom>))"
using evil_ClassAx.Atoms_def [where \<Gamma>="\<Gamma>" and \<Phi>="\<Phi>"]
  by(unfold mem_def, auto)

declare evil_pBB_def [simp del] 
    and evil_pBBI_def [simp del]

text {* Apparently we have to prove several lemmas
  relating to Atoms in order to be able to proceed. *}

lemma evil_mem_prv:
     assumes "finite \<Phi>"
         and "\<Gamma> \<in> Atoms \<Phi>"
         and "\<phi> \<in> \<Gamma>"
       shows "list \<Gamma> :\<turnstile> \<phi>"
using assms
proof -
   from assms finite_subset have
        "finite \<Gamma>" by fastsimp
   with set_list [where A="\<Gamma>"]
   have "set (list \<Gamma>) = \<Gamma>" by fastsimp 
   with assms have "\<phi> \<in> set (list \<Gamma>)" by simp
   with evil_ClassAx.lift_elm show ?thesis by fast
qed

lemma evil_mem_prv2:
     assumes "finite \<Phi>"
         and "\<Gamma> \<in> Atoms \<Phi>"
         and "\<phi> \<in> \<Phi>"
         and "list \<Gamma> :\<turnstile> \<phi>"
       shows "\<phi> \<in> \<Gamma>"
using assms
proof -
   from assms finite_subset have
        "finite \<Gamma>" by fastsimp
   with set_list [where A="\<Gamma>"]
   have eq1: "set (list \<Gamma>) = \<Gamma>" by fastsimp
   --"Now proceed by reductio"
   { assume "\<phi> \<notin> \<Gamma>" 
     with assms have "(\<sim> \<phi>) \<in> \<Gamma>" by fastsimp
     with eq1 have "(\<sim> \<phi>) \<in> set (list \<Gamma>)" by simp
     with evil_ClassAx.lift_elm 
     have "list \<Gamma> :\<turnstile> \<sim> \<phi>" by blast
     moreover from evil_pneg_eq
                  evil_eq_weaken
     have "\<turnstile> (\<sim> \<phi>) \<rightarrow> \<not> \<phi>" by blast
     with evil_ClassAx.lift have 
        "list \<Gamma> :\<turnstile> (\<sim> \<phi>) \<rightarrow> \<not> \<phi>" by blast
     moreover note evil_ClassAx.lift_mp [where \<Gamma>="list \<Gamma>"] 
                   assms
     ultimately have "list \<Gamma> :\<turnstile> \<bottom>" by blast
     with assms have "False" by simp
   }
   with assms show ?thesis by fast
qed

lemma evil_pneg_nded:
    assumes "finite \<Phi>"
        and "\<Gamma> \<in> Atoms \<Phi>"
        and "list \<Gamma> :\<turnstile> \<phi>"
      shows "~(list \<Gamma> :\<turnstile> \<sim> \<phi>)"
using assms
proof -
  --"By reductio ad absurdem"
  { assume "list \<Gamma> :\<turnstile> \<sim> \<phi>"
    moreover from evil_pneg_eq
                  evil_eq_weaken
    have "\<turnstile> (\<sim> \<phi>) \<rightarrow> \<not> \<phi>" by blast
    with evil_ClassAx.lift have 
      "list \<Gamma> :\<turnstile> (\<sim> \<phi>) \<rightarrow> \<not> \<phi>" by blast
    moreover note evil_ClassAx.lift_mp
    ultimately have "list \<Gamma> :\<turnstile> \<not> \<phi>" by fastsimp
    with evil_ClassAx.lift_mp assms
    have "False" by fastsimp }
   thus ?thesis by fast
qed

lemma evil_Atom_mem_intro:
    assumes "finite \<Phi>"
        and "\<Gamma> \<in> Atoms \<Phi>"
        and "\<phi> \<in> \<Gamma>"
        and "\<psi> \<in> \<Phi>"
        and "list \<Gamma> :\<turnstile> \<phi> \<rightarrow> \<psi>"
      shows "\<psi> \<in> \<Gamma>"
using assms
proof -
   from assms evil_mem_prv
   have "list \<Gamma> :\<turnstile> \<phi>" by blast
   with assms evil_ClassAx.lift_mp
   have \<psi>: "list \<Gamma> :\<turnstile> \<psi>" by fast
   { assume "(\<sim> \<psi>) \<in> \<Gamma>"
     with assms evil_mem_prv have "list \<Gamma> :\<turnstile> \<sim> \<psi>" by fast
     with assms evil_pneg_nded \<psi> have "False" by blast }
   with assms show ?thesis by fastsimp
qed

lemma evil_Atom_pBB_intro:
    assumes "finite \<Phi>"
        and "\<Gamma> \<in> Atoms \<Phi>"
        and "[-] X \<phi> \<in> \<Gamma>"
        and "[-]' X \<phi> \<in> \<Phi>"
      shows "[-]' X \<phi> \<in> \<Gamma>"
using assms
proof -
    from evil_BB_pBB_eq [where X="X"]
         evil_eq_weaken evil_eq_symm
    have "\<turnstile> [-] X \<phi> \<rightarrow> [-]' X \<phi>" by blast
    with evil_ClassAx.lift 
    have "list \<Gamma> :\<turnstile> [-] X \<phi> \<rightarrow> [-]' X \<phi>" by blast
    with evil_Atom_mem_intro assms
    show ?thesis by blast
qed

lemma evil_Atom_BB_intro:
    assumes "finite \<Phi>"
        and "\<Gamma> \<in> Atoms \<Phi>"
        and "[-]' X \<phi> \<in> \<Gamma>"
        and "[-] X \<phi> \<in> \<Phi>"
      shows "[-] X \<phi> \<in> \<Gamma>"
using assms
proof -
    from evil_BB_pBB_eq [where X="X"]
         evil_eq_weaken
    have "\<turnstile> [-]' X \<phi> \<rightarrow> [-] X \<phi>" by blast
    with evil_ClassAx.lift 
    have "list \<Gamma> :\<turnstile> [-]' X \<phi> \<rightarrow> [-] X \<phi>" by blast
    with evil_Atom_mem_intro assms
    show ?thesis by blast
qed

lemma evil_Atom_pBBI_intro:
    assumes "finite \<Phi>"
        and "\<Gamma> \<in> Atoms \<Phi>"
        and "[+] X \<phi> \<in> \<Gamma>"
        and "[+]' X \<phi> \<in> \<Phi>"
      shows "[+]' X \<phi> \<in> \<Gamma>"
using assms
proof -
    from evil_BBI_pBBI_eq [where X="X"]
         evil_eq_weaken evil_eq_symm
    have "\<turnstile> [+] X \<phi> \<rightarrow> [+]' X \<phi>" by blast
    with evil_ClassAx.lift 
    have "list \<Gamma> :\<turnstile> [+] X \<phi> \<rightarrow> [+]' X \<phi>" by blast
    with evil_Atom_mem_intro assms
    show ?thesis by blast
qed

lemma evil_Atom_BBI_intro:
    assumes "finite \<Phi>"
        and "\<Gamma> \<in> Atoms \<Phi>"
        and "[+]' X \<phi> \<in> \<Gamma>"
        and "[+] X \<phi> \<in> \<Phi>"
      shows "[+] X \<phi> \<in> \<Gamma>"
using assms
proof -
    from evil_BBI_pBBI_eq [where X="X"]
         evil_eq_weaken
    have "\<turnstile> [+]' X \<phi> \<rightarrow> [+] X \<phi>" by blast
    with evil_ClassAx.lift 
    have "list \<Gamma> :\<turnstile> [+]' X \<phi> \<rightarrow> [+] X \<phi>" by blast
    with evil_Atom_mem_intro assms
    show ?thesis by blast
qed

--"We now relativize these lemmas to our model we are creating"

lemma evil_FL_mem_prv:
  assumes "\<Phi> \<in> W(\<angle> \<phi>)"
      and "\<psi> \<in> \<Phi>"
    shows "list \<Phi> :\<turnstile> \<psi>"
using assms
proof -
  from finite_dudes finite_evil_FL
  have "finite (\<Sigma> (\<delta> \<phi>) \<phi>)" by blast
  moreover from assms
  have "\<Phi> \<in> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  moreover note assms evil_mem_prv 
  ultimately show ?thesis by blast
qed

thm evil_mem_prv2

lemma evil_FL_mem_prv2:
  assumes "\<Phi> \<in> W(\<angle> \<phi>)"
      and "\<psi> \<in> \<Sigma> (\<delta> \<phi>) \<phi>"
      and "list \<Phi> :\<turnstile> \<psi>"
    shows "\<psi> \<in> \<Phi>"
using assms
proof -
  from finite_dudes finite_evil_FL
  have "finite (\<Sigma> (\<delta> \<phi>) \<phi>)" by blast
  moreover from assms
  have "\<Phi> \<in> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  moreover note assms evil_mem_prv2 
  ultimately show ?thesis by blast
qed

lemma evil_FL_pneg_nded:
  assumes "\<Phi> \<in> W(\<angle> \<phi>)"
      and "list \<Phi> :\<turnstile> \<psi>"
    shows "~ (list \<Phi> :\<turnstile> \<sim> \<psi>)"
using assms
proof -
  from finite_dudes finite_evil_FL
  have "finite (\<Sigma> (\<delta> \<phi>) \<phi>)" by blast
  moreover from assms
  have "\<Phi> \<in> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  moreover note assms evil_pneg_nded
  ultimately show ?thesis by blast
qed

lemma evil_FL_mem_intro:
  assumes "\<Phi> \<in> W(\<angle> \<phi>)"
        and "\<psi> \<in> \<Phi>"
        and "\<chi> \<in> \<Sigma> (\<delta> \<phi>) \<phi>"
        and "list \<Phi> :\<turnstile> \<psi> \<rightarrow> \<chi>"
      shows "\<chi> \<in> \<Phi>"
using assms
proof -
  from finite_dudes finite_evil_FL
  have "finite (\<Sigma> (\<delta> \<phi>) \<phi>)" by blast
  moreover from assms
  have "\<Phi> \<in> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  moreover note evil_Atom_mem_intro assms
  ultimately show ?thesis by blast
qed

lemma evil_FL_pBB_intro:
    assumes "\<Phi> \<in> W(\<angle> \<phi>)"
        and "[-] X \<psi> \<in> \<Phi>"
      shows "[-]' X \<psi> \<in> \<Phi>"
using assms
proof -
  from finite_dudes finite_evil_FL
  have "finite (\<Sigma> (\<delta> \<phi>) \<phi>)" by blast
  moreover from assms
  have "\<Phi> \<in> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  moreover
  from this assms
   have "[-] X \<psi> \<in> (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  with evil_FL_BB_to_pBB
   have "[-]' X \<psi> \<in> (\<Sigma> (\<delta> \<phi>) \<phi>)" by fast
  moreover note evil_Atom_pBB_intro [where X="X"] 
                assms
  ultimately show ?thesis by blast
qed

lemma evil_FL_BB_intro:
    assumes "\<Phi> \<in> W(\<angle> \<phi>)"
        and "[-]' X \<psi> \<in> \<Phi>"
        and "[-] X \<psi> \<in> \<Sigma> (\<delta> \<phi>) \<phi>"
      shows "[-] X \<psi> \<in> \<Phi>"
using assms
proof -
  from finite_dudes finite_evil_FL
  have "finite (\<Sigma> (\<delta> \<phi>) \<phi>)" by blast
  moreover from assms
  have "\<Phi> \<in> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  moreover note evil_Atom_BB_intro [where X="X"] 
                assms
  ultimately show ?thesis by blast
qed

lemma evil_FL_pBBI_intro:
  assumes "\<Phi> \<in> W(\<angle> \<phi>)"
        and "[+] X \<psi> \<in> \<Phi>"
      shows "[+]' X \<psi> \<in> \<Phi>"
using assms
proof -
  from finite_dudes finite_evil_FL
  have "finite (\<Sigma> (\<delta> \<phi>) \<phi>)" by blast
  moreover from assms
  have "\<Phi> \<in> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  moreover
  from this assms
   have "[+] X \<psi> \<in> (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  with evil_FL_BBI_to_pBBI
   have "[+]' X \<psi> \<in> (\<Sigma> (\<delta> \<phi>) \<phi>)" by fast
  moreover note evil_Atom_pBBI_intro [where X="X"] 
                assms
  ultimately show ?thesis by blast
qed

lemma evil_push:
  assumes "finite A"
      and "list ({\<psi>} \<union> A) :\<turnstile> \<phi>"
    shows "list A :\<turnstile> \<psi> \<rightarrow> \<phi>"
using assms
proof -
  from assms have "finite ({\<psi>} \<union> A)" by fastsimp
  with set_list [where A="{\<psi>} \<union> A"] have 
    eq1: "set (list ({\<psi>} \<union> A)) = {\<psi>} \<union> A" ..
  from assms set_list [where A="A"] 
    have "set (list A) = A" by fast
  hence eq2: "set (\<psi> # (list A)) = {\<psi>} \<union> A" by simp
  with eq1 eq2 have
  "set (list ({\<psi>} \<union> A)) = set (\<psi> # (list A))" by fast
  with assms evil_ClassAx.lift_eq have
    "\<psi> # (list A) :\<turnstile> \<phi>" by blast
  with evil_ClassAx.undisch show ?thesis by blast
qed 
  
lemma evil_push_dneg:
  assumes "finite A"
      and "list ({\<sim> \<psi>} \<union> A) :\<turnstile> \<bottom>"
    shows "list A :\<turnstile> \<psi>"
using assms
proof -
    from assms evil_push 
    have "list A :\<turnstile> \<not> \<sim> \<psi>" by blast
    moreover
    from evil_pdneg_eq 
         evil_eq_weaken
         evil_ClassAx.lift [where \<Gamma>="list A"]
    have "list A :\<turnstile> \<not> \<sim> \<psi> \<rightarrow> \<psi>" by blast
    moreover note evil_ClassAx.lift_mp
    ultimately show ?thesis by fast
qed

lemma map_to_comp:
   assumes "set L = S"
   shows "set (map f L) = {f x | x. x \<in> S}"
using assms
by (induct L,fastsimp+)

lemma image_of_comp:
  "f ` {g \<chi> | \<chi> . P(\<chi>)} = {f (g \<chi>) | \<chi> . P(\<chi>)}"
by fastsimp

lemma evil_unions_to_appends:
  assumes "finite A"
      and "finite B"
    shows "(list (A \<union> B) @ \<Delta> :\<turnstile> \<psi>)
         = (list A @ list B @ \<Delta> :\<turnstile> \<psi>)"
using assms
proof -
   let ?ASM1 = "list (A \<union> B) @ \<Delta>"
   and ?ASM2 = "list A @ list B @ \<Delta>"
   from assms have "finite (A \<union> B)" by fast
   with set_list [where A="A"]
        set_list [where A="B"]
        set_list [where A="A \<union> B"]
   have A: "set (list A) = A"
    and B: "set (list B) = B"
    and AuB: "set (list (A \<union> B)) = A \<union> B"
      by fastsimp+ 
   { fix A B; have "set (A @ B) = set A \<union> set B"
         by (induct A, fastsimp+) }
   note union = this
   from AuB union have 
   eq1: "set(?ASM1) = A \<union> B \<union> set \<Delta>"
      by fastsimp
   from A B union have 
   eq2: "set(?ASM2) = A \<union> B \<union> set \<Delta>"
      by fastsimp
   from eq1 eq2 have "set ?ASM1 = set ?ASM2" by blast
   with evil_ClassAx.lift_eq show ?thesis by blast
qed

--"With these lemmas behind us, we may proceed forward (literally)!"
--"We shall prove the foward direction for each box"

lemma evil_B_forward:
      assumes H1: "\<box> X \<psi> \<in> \<Phi>"
          and H2: "(\<Phi>,\<Psi>) \<in> RB(\<angle> \<phi>) X"
          shows "\<psi> \<in> \<Psi>"
using assms
by fastsimp

lemma evil_BB_forward:
      assumes H1: "[-] X \<psi> \<in> \<Phi>"
          and H2: "(\<Phi>,\<Psi>) \<in> RBB(\<angle> \<phi>) X"
          shows "\<psi> \<in> \<Psi>"
using assms
proof -
  from H2 have "\<Phi> \<in> W(\<angle> \<phi>)" by fastsimp
  with H1 evil_FL_pBB_intro
  have "[-]' X \<psi> \<in> \<Phi>" by fast
  with H2 show ?thesis by fastsimp
qed

lemma evil_BBI_forward:
      assumes H1: "[+] X \<psi> \<in> \<Phi>"
          and H2: "(\<Phi>,\<Psi>) \<in> RBBI(\<angle> \<phi>) X"
          shows "\<psi> \<in> \<Psi>"
using assms
proof -
  from H2 have "\<Phi> \<in> W(\<angle> \<phi>)" by fastsimp
  with H1 evil_FL_pBBI_intro
  have "[+]' X \<psi> \<in> \<Phi>" by fast
  with H2 show ?thesis by fastsimp
qed

--"With the forward directions out the way, we move backward"
--"These are all non-trivial lemmas"

lemma evil_B_back:
      assumes "\<Phi> \<in> W(\<angle> \<phi>)"
          and "\<box> X \<psi> \<notin> \<Phi>"
          and "\<box> X \<psi> \<in> \<Sigma> (\<delta> \<phi>) \<phi>"
          shows "\<exists> \<Psi>. (\<Phi>,\<Psi>) \<in> RB(\<angle> \<phi>) X \<and> (\<sim> \<psi>) \<in> \<Psi>"
using assms
proof -
  let ?s1 = "{\<chi> | \<chi>. \<box> X \<chi> \<in> \<Phi>}"
  let ?s2 = "{\<box> X \<chi> | \<chi>. \<box> X \<chi> \<in> \<Phi>}"

  --"We have a bunch of facts to establish"
  from finite_dudes finite_evil_FL
  have fin_\<Sigma>\<delta>\<phi>\<phi>: "finite (\<Sigma> (\<delta> \<phi>) \<phi>)" by blast
  moreover from assms
  have \<Phi>_atom: "\<Phi> \<in> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>)" by fastsimp
  moreover note finite_subset
  ultimately have fin_\<Phi>: "finite \<Phi>" 
              and s2_sub: "?s2 \<subseteq> \<Phi>" 
               by fastsimp+
  with finite_subset
  have fin_s2: "finite ?s2"
       by fastsimp
  hence "finite (\<surd> ` ?s2)" by simp 
  with image_of_comp [where g="\<lambda> x. \<box> X x"
                        and P="\<lambda> x. \<box> X x \<in> \<Phi>"
                        and f="\<surd>"]
  have fin_s1: "finite ?s1" by fastsimp
  from fin_s1 fin_s2 fin_\<Phi>
                   set_list [where A="?s1"]
                   set_list [where A="?s2"]
                   set_list [where A="\<Phi>"]
  have eq1: "set (list ?s1) = ?s1" 
   and eq2: "set (list ?s2) = ?s2" 
   and eq3: "set (list \<Phi>) = \<Phi>" by blast+
  from eq1 eq2 map_to_comp
  have eq4:
    "set (map (\<lambda> \<phi>. \<box> X \<phi>) (list ?s1)) = set (list ?s2)" 
        by fastsimp
  from s2_sub eq2 eq3 
  have s2_sub2: "set (list ?s2) \<subseteq> set (list \<Phi>)"
        by fastsimp

  --"Now reductio ad absurdem..."
  { assume "list ({\<sim> \<psi>} \<union> ?s1) :\<turnstile> \<bottom>"
     with fin_s1 evil_push_dneg
     have "list ?s1 :\<turnstile> \<psi>" by fastsimp
     with evil_B_lift_map [where X="X"]
     have "(map (\<lambda> \<phi>. \<box> X \<phi>) (list ?s1)) :\<turnstile> \<box> X \<psi>" by blast
     with eq4
      evil_ClassAx.lift_eq 
         [where \<Gamma>="map (\<lambda> \<phi>. \<box> X \<phi>) (list ?s1)"
            and \<Psi>="list ?s2"]
     have "list ?s2 :\<turnstile> \<box> X \<psi>" by fast
     with s2_sub2 evil_ClassAx.lift_mono
     have "list \<Phi> :\<turnstile> \<box> X \<psi>" by blast
     with assms evil_FL_mem_prv2 have "False" by fast }
  hence "~(list ({\<sim> \<psi>} \<union> ?s1) :\<turnstile> \<bottom>)" by blast
  note con = this

  { fix \<chi>; assume "(\<box> X \<chi>) \<in> \<Sigma> (\<delta> \<phi>) \<phi>"
    with evil_FL_subforms 
    have "\<Down> (\<box> X \<chi>) \<subseteq>  \<Sigma> (\<delta> \<phi>) \<phi>"
       by fast
     hence "\<chi> \<in> \<Sigma> (\<delta> \<phi>) \<phi>" by fastsimp }
  note mem = this

  from assms mem have "\<psi> \<in> \<Sigma> (\<delta> \<phi>) \<phi>" by blast
  with pneg_evil_FL have "(\<sim> \<psi>) \<in> \<Sigma> (\<delta> \<phi>) \<phi>" by fast
  moreover with s2_sub \<Phi>_atom
    have "?s2 \<subseteq> \<Sigma> (\<delta> \<phi>) \<phi>" by fastsimp
  with mem have "?s1 \<subseteq> \<Sigma> (\<delta> \<phi>) \<phi>" by fast
  ultimately have "{\<sim> \<psi>} \<union> ?s1 \<subseteq> \<Sigma> (\<delta> \<phi>) \<phi>" by fast
  with fin_\<Sigma>\<delta>\<phi>\<phi> con
       pneg_evil_FL [where \<phi>="\<phi>" and \<Delta>="\<delta> \<phi>"]
       evil_ClassAx.little_lindy [where \<Phi>="\<Sigma> (\<delta> \<phi>) \<phi>"
                                    and \<Gamma>="{\<sim> \<psi>} \<union> ?s1"
                                    and \<psi>="\<bottom>"]
     obtain \<Psi> where A: "\<Psi> \<in> Atoms (\<Sigma> (\<delta> \<phi>) \<phi>)"
                and B: "{\<sim> \<psi>} \<union> ?s1 \<subseteq> \<Psi>"
     by (simp add: mem_def, fast+)
  with \<Phi>_atom have "(\<Phi>,\<Psi>) \<in> RB(\<angle> \<phi>) X" by fastsimp
  with B show ?thesis by blast
qed