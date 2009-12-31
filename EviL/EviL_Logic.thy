header{* EviL Axiomatics *}

theory EviL_Logic
imports EviL_Semantics
begin

text {*
In this file, we turn to the task of providing
axiomatics for a Hilbert system giving the logic of EviL.  We shall
follow the treatment in Classic.thy, and instantiate EviL as a Classical
Logic. Since we'll continue the business of abusing notation, we first set our
notation appropriately. *}

no_notation
  bot ("\<bottom>") and
  imp (infixr "\<rightarrow>" 25)  and
  vdash ("\<turnstile> _" [20] 20) and
  lift_vdash (infix ":\<turnstile>" 10) and
  Not  ("\<not> _" [40] 40) and
  neg ("\<not> _" [40] 40) and
  Classic.cl_neg ("\<not> _" [40] 40) and
  pneg ("\<sim> _" [40] 40) and
  CL_P ("P#") and
  CL_Bot ("\<bottom>") and
  CL_Imp (infixr "\<rightarrow>" 25)

abbreviation
evil_neg :: "('a,'b) evil_form \<Rightarrow> ('a,'b) evil_form" ("\<not> _" [40] 40) where
"\<not> \<phi> \<equiv> (\<phi> \<rightarrow> \<bottom>)"

abbreviation
evil_D :: "'b \<Rightarrow> ('a,'b) evil_form \<Rightarrow> ('a,'b) evil_form" ("\<diamond>") where
"\<diamond> X \<phi> \<equiv> \<not> (\<box> X (\<not> \<phi>))"

abbreviation
evil_DD :: "'b \<Rightarrow> ('a,'b) evil_form \<Rightarrow> ('a,'b) evil_form" ("\<langle>+\<rangle>") where
"\<langle>+\<rangle> X \<phi> \<equiv> \<not> ([+] X (\<not> \<phi>))"

abbreviation
evil_DDI :: "'b \<Rightarrow> ('a,'b) evil_form \<Rightarrow> ('a,'b) evil_form" ("\<langle>-\<rangle>") where
"\<langle>-\<rangle> X \<phi> \<equiv> \<not> ([-] X (\<not> \<phi>))"

text {*
  Here are the axioms of EviL; since these principles have their basis in
  philosophy, we offer philosophical readings of each.
*}

inductive_set EviL :: "('a,'b) evil_form set" where 
  --{* If something is true, nothing can change this*}
  evil_ax1: "(\<phi> \<rightarrow> \<psi> \<rightarrow> \<phi>) \<in> EviL" |

  --{* If @{term "\<phi>"} and @{term "\<psi>"} jointly imply @{term "\<chi>"},*}
  --{* and @{term "\<phi>"} implies @{term "\<psi>"}, *}
  --{* then @{term "\<phi>"} alone is sufficient too show @{term "\<chi>"} *}
  evil_ax2: "((\<phi> \<rightarrow> \<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>)) \<in> EviL" |

  --{* If the failure of @{term "\<phi>"} ensures the failure of @{term "\<psi>"}, *}
  --{* then @{term "\<psi>"}'s success ensures @{term "\<phi>"}'s success. *}
  evil_ax3: "((\<not> \<phi>  \<rightarrow> \<not> \<psi>) \<rightarrow> \<psi> \<rightarrow> \<phi>) \<in> EviL" |

  --{* If under any further evidence $X$ considers, @{term "\<phi>"} holds, *}
  --{* then @{term "\<phi>"} holds simpliciter, *}
  --{* since considering no additional evidence is trivially considering further evidence *}
  evil_ax4: "([+] X \<phi> \<rightarrow> \<phi>) \<in> EviL" |

  --{* If under any further evidence $X$ considers,  @{term "\<phi>"} holds, *}
  --{* then @{term "\<phi>"} also holds whenever $X$ considers further further evidence. *}
  evil_ax5: "(([+] X \<phi>) \<rightarrow> ([+] X ([+] X \<phi>))) \<in> EviL" |

  --{* Changing one's mind does not effect matters of fact *}
  evil_ax6: "(P# p \<rightarrow> [+] X (P# p)) \<in> EviL" |
  evil_ax7: "(P# p \<rightarrow> [-] X (P# p)) \<in> EviL" |

  --{* If $X$ can imagine @{term "\<phi>"} being under some evidence she is considering, *}
  --{* then less evidence wouldn't make @{term "\<phi>"} any less conceivable for her. *}
  evil_ax8: "((\<diamond> X \<phi>) \<rightarrow> [-] X (\<diamond> A \<phi>)) \<in> EviL" |

  --{* If $X$ believes @{term "\<phi>"},  *}
  --{* she believes it despite what anyone thinks *}
  evil_ax9: "((\<box> X \<phi>) \<rightarrow> \<box> X ([+] Y \<phi>)) \<in> EviL" |
  evil_ax10: "((\<box> X \<phi>) \<rightarrow> \<box> X ([-] Y \<phi>)) \<in> EviL" |

  --{* If $X$'s evidence is sound, *}
  --{* then what she believes is true *}
  evil_ax11: "(\<odot> X \<rightarrow> (\<box> X \<phi>) \<rightarrow> \<phi>) \<in> EviL" |

  --{* If $X$'s evidence is sound, *}
  --{* then any subset of it she can consider must be sound too *}
  evil_ax12: "(\<odot> X \<rightarrow> [-] X (\<odot> X)) \<in> EviL" |

  --{* If @{term "\<phi>"} is true, *}
  --{* then no matter what further evidence $X$ considers, *}
  --{* she can forget it and @{term "\<phi>"} will still be true *}
  evil_ax13: "(\<phi> \<rightarrow> [+] X (\<langle>-\<rangle> X \<phi>)) \<in> EviL" |

  --{* If @{term "\<phi>"} is true, *}
  --{* then no matter what evidence $X$ dispenses with, *}
  --{* if $X$ remembers correctly then @{term "\<phi>"} will still be true *}
  evil_ax14: "(\<phi> \<rightarrow> [-] X (\<langle>+\<rangle>  X \<phi>)) \<in> EviL" |

  --{* If $X$ believes @{term "\<phi>"} implies @{term "\<psi>"} and @{term "\<phi>"} *}
  --{* on the basis of her evidence, she can come to believe @{term "\<psi>"} *}
  --{* on this same basis of her evidence. *}
  evil_ax15: "((\<box> X (\<phi> \<rightarrow> \<psi>)) \<rightarrow> (\<box> X \<phi>) \<rightarrow> \<box> X \<psi>) \<in> EviL"  |

  --{* If no matter what evidence $X$ tries to forget, *}
  --{* @{term "\<phi>"} implies @{term "\<psi>"}, and also @{term "\<phi>"} holds, *}
  --{* then no matter what evidence she disregards it must be that @{term "\<psi>"}. *}
  evil_ax16: "(([-] X (\<phi> \<rightarrow> \<psi>)) \<rightarrow> ([-] X \<phi>) \<rightarrow> [-] X \<psi>) \<in> EviL"  |

  --{* If no matter what further evidence $X$ considers, *}
  --{* @{term "\<phi>"} implies @{term "\<psi>"}, and also @{term "\<phi>"} holds, *}
  --{* then no matter what further evidence she consider it must be that @{term "\<psi>"}. *}
  evil_ax17: "(([+] X (\<phi> \<rightarrow> \<psi>)) \<rightarrow> ([+] X \<phi>) \<rightarrow> [+] X \<psi>) \<in> EviL"  |

  --{* If something is always true, then an agent can come to believe this *}
  evil_B_nec: "\<phi> \<in> EviL \<Longrightarrow> (\<box> X \<phi>) \<in> EviL" |
  
  --{* If something is always true, *}
  --{* then it's true no matter what an agent tries to forget *}
  evil_BB_nec: "\<phi> \<in> EviL \<Longrightarrow> ([-] X \<phi>) \<in> EviL" |

  --{* If something is always true, *}
  --{* then it's true regardless of what more an agent might choose to believe *}
  evil_BBI_nec: "\<phi> \<in> EviL \<Longrightarrow> ([+] X \<phi>) \<in> EviL" |

  --{* Modus ponens *}
  evil_mp: "\<lbrakk> (\<phi> \<rightarrow> \<psi>) \<in> EviL; \<phi> \<in> EviL \<rbrakk> \<Longrightarrow> \<psi> \<in> EviL"

abbreviation evil_vdash :: "('a,'b) evil_form \<Rightarrow> bool" ("\<turnstile> _" [20] 20) where
"(\<turnstile> \<phi>) \<equiv> \<phi> \<in> EviL"

text {* We now turn to developing some basic proof theory for EviL.  We start
by showing that it is an extesion of classical logic; it is in fact a conservative
extension (we assert this without proof).  So we shall establish that it is an 
instance of ClassAx. *}

interpretation evil_ClassAx: ClassAx "op \<rightarrow>" "evil_vdash" "\<bottom>"
proof qed (fastsimp intro: EviL.intros)+

text {* In the subsequent discussion, we'll have need to prove a lot of theorems in 
classical propositional logic; our basic approach will be to appeal to completeness
and apply automation to accomplish this. So we now reintroduce syntax for classical
logic. *}

notation
CL_P     ("P#\<^bsub>CL\<^esub>") and
CL_Bot   ("\<bottom>\<^bsub>CL\<^esub>")  and
cl_neg   ("\<not>\<^bsub>CL\<^esub>")  and
CL_Imp   (infixr "\<rightarrow>\<^bsub>CL\<^esub>" 25)

text {* Our first application of this approach will be to prove a rewrite rule for
EviL; we shall have intend to appeal to rewriting further on in our proof *}

primrec evil_sub :: 
 "[('a,'b) evil_form, ('a,'b) evil_form, ('a,'b) evil_form] 
            \<Rightarrow> ('a,'b) evil_form" ("_[_'/_]" [300, 0, 0] 300) where
     "(P# a)[\<phi>/\<psi>] = (if ((P# a) = \<phi>) then \<psi> else (P# a))"
   | "\<bottom>[\<phi>/\<psi>] = (if (\<bottom> = \<phi>) then \<psi> else \<bottom>)"
   | "(\<odot> X)[\<phi>/\<psi>] = (if ((\<odot> X) = \<phi>) then \<psi> else (\<odot> X))"
   | "(\<delta> \<rightarrow> \<kappa>)[\<phi>/\<psi>] = (if ((\<delta> \<rightarrow> \<kappa>) = \<phi>) then \<psi> 
                        else (\<delta>[\<phi>/\<psi>] \<rightarrow> \<kappa>[\<phi>/\<psi>]))"
   | "(\<box> X \<kappa>)[\<phi>/\<psi>] = (if ((\<box> X \<kappa>) = \<phi>) then \<psi>
                        else (\<box> X (\<kappa>[\<phi>/\<psi>])))"
   | "([-] X \<kappa>)[\<phi>/\<psi>] = (if (([-] X \<kappa>) = \<phi>) then \<psi> 
                        else ([-] X (\<kappa>[\<phi>/\<psi>])))"
   | "([+] X \<kappa>)[\<phi>/\<psi>] = (if (([+] X \<kappa>) = \<phi>) then \<psi> 
                        else ([+] X (\<kappa>[\<phi>/\<psi>])))"

abbreviation evil_iff :: 
  "[('a,'b) evil_form, ('a,'b) evil_form] 
   \<Rightarrow> ('a,'b) evil_form" (infixr "\<leftrightarrow>" 25) where
"(\<phi> \<leftrightarrow> \<psi>) \<equiv> ((\<phi> \<rightarrow> \<not> \<psi>) \<rightarrow> \<not>(\<not> \<phi> \<rightarrow> \<psi>))"

abbreviation cl_iff :: 
  "['a cl_form, 'a cl_form] \<Rightarrow> 'a cl_form" (infixr "\<leftrightarrow>\<^bsub>CL\<^esub>" 25) where
"(\<phi> \<leftrightarrow>\<^bsub>CL\<^esub> \<psi>) \<equiv> ((\<phi> \<rightarrow>\<^bsub>CL\<^esub> \<not>\<^bsub>CL\<^esub> \<psi>) \<rightarrow>\<^bsub>CL\<^esub> \<not>\<^bsub>CL\<^esub> (\<not>\<^bsub>CL\<^esub> \<phi> \<rightarrow>\<^bsub>CL\<^esub> \<psi>))"

text {* As the following shows, most elementary theorems
about logical equivalence reflect tautologies from classical
propositional logic; having automated semantics and completeness
makes this work rather straightforward. *}

lemma evil_eq_refl: "\<turnstile> \<phi> \<leftrightarrow> \<phi>"
proof -
  have "\<turnstile>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<phi>) \<leftrightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<phi>)" by fastsimp
  with evil_ClassAx.cl_translate
       [where \<phi>="(P#\<^bsub>CL\<^esub> \<phi>) \<leftrightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<phi>)"]
  show ?thesis by simp
qed

lemma evil_eq_symm: "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<psi> \<leftrightarrow> \<phi>"
proof -
  assume eq: "\<turnstile> \<phi> \<leftrightarrow> \<psi>"
  let ?\<theta> = "((P#\<^bsub>CL\<^esub> \<phi>) \<leftrightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<psi>)) 
            \<rightarrow>\<^bsub>CL\<^esub> ((P#\<^bsub>CL\<^esub> \<psi>) \<leftrightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<phi>))"
  have "?\<theta> \<in> CL" by fastsimp
  with evil_ClassAx.cl_translate [where \<phi>="?\<theta>"]
  have "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> (\<psi> \<leftrightarrow> \<phi>)" by simp
  with evil_mp eq show ?thesis by blast
qed

lemma evil_eq_trans: 
  "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<psi> \<leftrightarrow> \<chi> \<Longrightarrow> \<turnstile> \<phi> \<leftrightarrow> \<chi>"
proof -
  assume A: "\<turnstile> \<phi> \<leftrightarrow> \<psi>"
     and B: "\<turnstile> \<psi> \<leftrightarrow> \<chi>"
  let ?\<theta> = "((P#\<^bsub>CL\<^esub> \<phi>) \<leftrightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<psi>)) 
            \<rightarrow>\<^bsub>CL\<^esub> ((P#\<^bsub>CL\<^esub> \<psi>) \<leftrightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<chi>))
            \<rightarrow>\<^bsub>CL\<^esub> ((P#\<^bsub>CL\<^esub> \<phi>) \<leftrightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<chi>))"
  have "?\<theta> \<in> CL" by fastsimp
  with evil_ClassAx.cl_translate [where \<phi>="?\<theta>"]
  have "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> (\<psi> \<leftrightarrow> \<chi>) \<rightarrow> (\<phi> \<leftrightarrow> \<chi>)" by simp
  with evil_mp A B show ?thesis by blast
qed

text {* One should note that the above three lemmas 
establish that @{term "op \<leftrightarrow>"} is an equivalence relation,
which is of course an elementary result in basic logic. *}

lemma evil_eq_weaken: "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<phi> \<rightarrow> \<psi>"
proof -
  assume eq: "\<turnstile> \<phi> \<leftrightarrow> \<psi>"
  let ?\<theta> = "((P#\<^bsub>CL\<^esub> \<phi>) \<leftrightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<psi>)) \<rightarrow>\<^bsub>CL\<^esub> 
                (P#\<^bsub>CL\<^esub> \<phi>) \<rightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<psi>)"
  have "?\<theta> \<in> CL" by fastsimp
  with evil_ClassAx.cl_translate [where \<phi>="?\<theta>"]
  have "\<turnstile> (\<phi> \<leftrightarrow> \<psi>) \<rightarrow> \<phi> \<rightarrow> \<psi>" by simp
  with evil_mp eq show ?thesis by blast
qed

lemma evil_eq_mp: "\<turnstile> \<phi> \<leftrightarrow> \<psi> \<Longrightarrow> \<turnstile> \<phi> \<Longrightarrow> \<turnstile> \<psi>"
proof -
  assume eq: "\<turnstile> \<phi> \<leftrightarrow> \<psi>" and hyp: "\<turnstile> \<phi>"
  with evil_eq_weaken have "\<turnstile> \<phi> \<rightarrow> \<psi>" by fast
  with evil_mp hyp show ?thesis by fast
qed

lemma evil_eq_intro: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> \<psi> \<rightarrow> \<phi> \<Longrightarrow> \<turnstile> \<phi> \<leftrightarrow> \<psi>"
proof -
  assume A: "\<turnstile> \<phi> \<rightarrow> \<psi>"
     and B: "\<turnstile> \<psi> \<rightarrow> \<phi>"
  let ?\<theta>="(P#\<^bsub>CL\<^esub> \<phi> \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> \<psi>)
          \<rightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<psi> \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> \<phi>)
          \<rightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<phi> \<leftrightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> \<psi>)"
  have "?\<theta> \<in> CL" by fastsimp
  with evil_ClassAx.cl_translate [where \<phi>="?\<theta>"]
  have "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<phi> \<leftrightarrow> \<psi>)" by simp
  with A B evil_mp show ?thesis by blast
qed

lemma evil_contrapose:
  "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> \<not> \<psi> \<rightarrow> \<not> \<phi>"
proof -
  let ?\<theta>="(P#\<^bsub>CL\<^esub> \<phi> \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> \<psi>)
          \<rightarrow>\<^bsub>CL\<^esub> (\<not>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<psi>) \<rightarrow>\<^bsub>CL\<^esub> \<not>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<phi>))"
  have "?\<theta> \<in> CL" by fastsimp
  with evil_ClassAx.cl_translate [where \<phi>="?\<theta>"]
  have "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<not> \<psi> \<rightarrow> \<not> \<phi>)" by simp
  moreover assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  moreover note evil_mp 
  ultimately show ?thesis by blast
qed

lemma evil_B_map: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> \<box> X \<phi> \<rightarrow> \<box> X \<psi>"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  with evil_B_nec have "\<turnstile> \<box> X (\<phi> \<rightarrow> \<psi>)" by fast
  with evil_ax15 [where X="X" and \<phi>="\<phi>" and \<psi>="\<psi>"]
       evil_mp show ?thesis by fast
qed

lemma evil_DB_map: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> \<diamond> X \<phi> \<rightarrow> \<diamond> X \<psi>"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  with evil_contrapose have "\<turnstile> \<not> \<psi> \<rightarrow> \<not> \<phi>" .
  with evil_B_map have "\<turnstile> \<box> X (\<not> \<psi>) \<rightarrow> \<box> X (\<not> \<phi>)" .
  with evil_contrapose show ?thesis .
qed

lemma evil_BB_map: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> [-] X \<phi> \<rightarrow> [-] X \<psi>"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  with evil_BB_nec have "\<turnstile> [-] X (\<phi> \<rightarrow> \<psi>)" by fast
  with evil_ax16 [where X="X" and \<phi>="\<phi>" and \<psi>="\<psi>"]
       evil_mp show ?thesis by fast
qed

lemma evil_DBB_map: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> \<langle>-\<rangle> X \<phi> \<rightarrow> \<langle>-\<rangle> X \<psi>"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  with evil_contrapose have "\<turnstile> \<not> \<psi> \<rightarrow> \<not> \<phi>" .
  with evil_BB_map have "\<turnstile> [-] X (\<not> \<psi>) \<rightarrow> [-] X (\<not> \<phi>)" .
  with evil_contrapose show ?thesis .
qed

lemma evil_BBI_map: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> [+] X \<phi> \<rightarrow> [+] X \<psi>"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  with evil_BBI_nec have "\<turnstile> [+] X (\<phi> \<rightarrow> \<psi>)" by fast
  with evil_ax17 [where X="X" and \<phi>="\<phi>" and \<psi>="\<psi>"]
       evil_mp show ?thesis by fast
qed

lemma evil_DBBI_map: "\<turnstile> \<phi> \<rightarrow> \<psi> \<Longrightarrow> \<turnstile> \<langle>+\<rangle> X \<phi> \<rightarrow> \<langle>+\<rangle> X \<psi>"
proof -
  assume "\<turnstile> \<phi> \<rightarrow> \<psi>"
  with evil_contrapose have "\<turnstile> \<not> \<psi> \<rightarrow> \<not> \<phi>" .
  with evil_BBI_map have "\<turnstile> [+] X (\<not> \<psi>) \<rightarrow> [+] X (\<not> \<phi>)" .
  with evil_contrapose show ?thesis .
qed

lemma evil_sub: 
  assumes eq: "\<turnstile> \<phi> \<leftrightarrow> \<psi>" 
  shows "\<turnstile> \<chi> \<leftrightarrow> \<chi>[\<phi>/\<psi>]"
using eq
proof (induct \<chi>, (fastsimp intro: evil_eq_refl)+)
  --"Most base cases are delt with automatically;"
  --"we are left with implication and the three boxes"
  case (E_Imp \<delta> \<kappa>)
    hence A: "(\<turnstile> \<delta> \<leftrightarrow> \<delta>[\<phi>/\<psi>])" 
      and B: "(\<turnstile> \<kappa> \<leftrightarrow> \<kappa>[\<phi>/\<psi>])" by fast+
    --"This case follows from a lengthy tautology"
    let ?\<theta>="(P#\<^bsub>CL\<^esub> \<delta> \<leftrightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> (\<delta>[\<phi>/\<psi>]))
          \<rightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<kappa> \<leftrightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> (\<kappa>[\<phi>/\<psi>])) 
          \<rightarrow>\<^bsub>CL\<^esub> ((P#\<^bsub>CL\<^esub> \<delta> \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> \<kappa>) 
                 \<leftrightarrow>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> (\<delta>[\<phi>/\<psi>]) \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> (\<kappa>[\<phi>/\<psi>])))"
    have "?\<theta> \<in> CL" by fastsimp
    with evil_ClassAx.cl_translate [where \<phi>="?\<theta>"]
    have "\<turnstile> (\<delta> \<leftrightarrow> \<delta>[\<phi>/\<psi>]) \<rightarrow> (\<kappa> \<leftrightarrow> \<kappa> [\<phi>/\<psi>])
             \<rightarrow> ((\<delta> \<rightarrow> \<kappa>) \<leftrightarrow> (\<delta>[\<phi>/\<psi>] \<rightarrow> \<kappa>[\<phi>/\<psi>]))" by simp 
    with A evil_mp [where \<phi>="\<delta> \<leftrightarrow> \<delta>[\<phi>/\<psi>]"]
         B evil_mp [where \<phi>="\<kappa> \<leftrightarrow> \<kappa>[\<phi>/\<psi>]"] have
      "\<turnstile> (\<delta> \<rightarrow> \<kappa>) \<leftrightarrow> (\<delta>[\<phi>/\<psi>] \<rightarrow> \<kappa>[\<phi>/\<psi>])" by blast
    with eq evil_eq_refl show ?case by fastsimp

  --"The next three cases are all basically the same"
  next case (E_B X \<chi>)
    hence A: "\<turnstile> \<chi> \<leftrightarrow> \<chi>[\<phi>/\<psi>]" by fast
    from A evil_eq_weaken evil_B_map 
      have "\<turnstile> \<box> X \<chi> \<rightarrow> \<box> X (\<chi>[\<phi>/\<psi>])" by fast
    moreover from A evil_eq_symm evil_eq_weaken evil_B_map
      have "\<turnstile> \<box> X (\<chi>[\<phi>/\<psi>]) \<rightarrow> \<box> X \<chi>" by fast
    moreover note evil_eq_intro
    ultimately have "\<turnstile> \<box> X \<chi> \<leftrightarrow> \<box> X (\<chi>[\<phi>/\<psi>])" by fast
    with eq show ?case by fastsimp
  next case (E_BB X \<chi>)
    hence A: "\<turnstile> \<chi> \<leftrightarrow> \<chi>[\<phi>/\<psi>]" by fast
    from A evil_eq_weaken evil_BB_map 
      have "\<turnstile> [-] X \<chi> \<rightarrow> [-] X (\<chi>[\<phi>/\<psi>])" by fast
    moreover from A evil_eq_symm evil_eq_weaken evil_BB_map
      have "\<turnstile> [-] X (\<chi>[\<phi>/\<psi>]) \<rightarrow> [-] X \<chi>" by fast
    moreover note evil_eq_intro
    ultimately have "\<turnstile> [-] X \<chi> \<leftrightarrow> [-] X (\<chi>[\<phi>/\<psi>])" by fast
    with eq show ?case by fastsimp
  next case (E_BBI X \<chi>)
    hence A: "\<turnstile> \<chi> \<leftrightarrow> \<chi>[\<phi>/\<psi>]" by fast
    from A evil_eq_weaken evil_BBI_map 
      have "\<turnstile> [+] X \<chi> \<rightarrow> [+] X (\<chi>[\<phi>/\<psi>])" by fast
    moreover from A evil_eq_symm evil_eq_weaken evil_BBI_map
      have "\<turnstile> [+] X (\<chi>[\<phi>/\<psi>]) \<rightarrow> [+] X \<chi>" by fast
    moreover note evil_eq_intro
    ultimately have "\<turnstile> [+] X \<chi> \<leftrightarrow> [+] X (\<chi>[\<phi>/\<psi>])" by fast
    with eq show ?case by fastsimp
qed

text {* We now turn to showing an analogues of axioms 4 and 5 for @{term "[-]"};
        we shall expedite our proofs by employing rewriting now that we have it our
        disposal.

We shall first prove several theorems about inequalities, subformulae and substitutions. *}

--"A little function which gives the proper subforumulae"
primrec evil_psubforms 
 :: "('a,'b) evil_form \<Rightarrow> ('a,'b) evil_form set" ("\<Down>")
where
    "\<Down>(P# p) = {}"
  | "\<Down>(\<bottom>) = {}"
  | "\<Down>(\<odot> X) = {}"
  | "\<Down>(\<phi> \<rightarrow> \<psi>) = {\<phi>, \<psi>} \<union> \<Down>(\<phi>) \<union> \<Down>(\<psi>)"
  | "\<Down>(\<box> X \<phi>) = {\<phi>} \<union>  \<Down>(\<phi>)"
  | "\<Down>([-] X \<phi>) = {\<phi>} \<union>  \<Down>(\<phi>)"
  | "\<Down>([+] X \<phi>) = {\<phi>} \<union>  \<Down>(\<phi>)"

--"Here's a series of obvious inequalities we shall reuse"
lemma evil_limp_neq[intro]: "\<forall> \<chi>. (\<psi> \<rightarrow> \<chi>) \<noteq> \<psi>" 
  by (induct \<psi>, simp_all)

lemma evil_rimp_neq[intro]: "\<forall> \<psi>. (\<psi> \<rightarrow> \<chi>) \<noteq> \<chi>" 
  by (induct \<chi>, simp_all)

lemma evil_B_neq[intro]: "(\<box> X \<phi>) \<noteq> \<phi>"
 by (induct \<phi>, fastsimp+)

lemma evil_BB_neq[intro]: "([-] X \<phi>) \<noteq> \<phi>"
 by (induct \<phi>, fastsimp+)

lemma evil_BBI_neq[intro]: "([+] X \<phi>) \<noteq> \<phi>"
 by (induct \<phi>, fastsimp+)

lemma evil_not_neq[intro]: "(\<not> \<phi>) \<noteq> \<phi>"
 by (induct \<phi>, fastsimp+)

--"Here's a series of deconstruction lemmas"
lemma evil_psform_limp_elim[intro]: 
 "(\<delta> \<rightarrow> \<kappa>) \<in> \<Down> \<psi> \<Longrightarrow> \<delta> \<in> \<Down> \<psi>"
   by (induct \<psi>, fastsimp+)

lemma evil_psform_rimp_elim[intro]: 
 "(\<delta> \<rightarrow> \<kappa>) \<in> \<Down> \<psi> \<Longrightarrow> \<kappa> \<in> \<Down> \<psi>"
   by (induct \<psi>, fastsimp+)

lemma evil_psform_B_elim[intro]:
 "\<box> X \<psi> \<in> \<Down> \<phi> \<Longrightarrow> \<psi> \<in> \<Down> \<phi>"
   by (induct \<phi>, fastsimp+)

lemma evil_psform_BB_elim[intro]:
 "[-] X \<psi> \<in> \<Down> \<phi> \<Longrightarrow> \<psi> \<in> \<Down> \<phi>"
   by (induct \<phi>, fastsimp+)

lemma evil_psform_BBI_elim[intro]:
 "[+] X \<psi> \<in> \<Down> \<phi> \<Longrightarrow> \<psi> \<in> \<Down> \<phi>"
   by (induct \<phi>, fastsimp+)

--"All of the above lemmas are used implicitly by what follows:"
lemma evil_psform_nin [intro!]: "\<phi> \<notin> \<Down> \<phi>"
proof (induct \<phi>)
       case E_P show ?case by simp
  next case E_Bot show ?case by simp
  next case E_PP show ?case by simp
  next case (E_Imp \<psi> \<chi>) thus ?case
    using evil_limp_neq [where \<psi>="\<psi>"] 
          evil_rimp_neq [where \<chi>="\<chi>"]
      by (simp,blast)
  next case (E_B X \<phi>) thus ?case
    using evil_B_neq [where X="X" and \<phi>="\<phi>"]
      by (simp,blast)
  next case (E_BB X \<phi>) thus ?case
    using evil_BB_neq [where X="X" and \<phi>="\<phi>"]
      by (simp,blast)
 next case (E_BBI X \<phi>) thus ?case
    using evil_BBI_neq [where X="X" and \<phi>="\<phi>"]
      by (simp,blast)
qed

lemma sub_neq [intro!]: 
   assumes sf: "\<psi> \<in> \<Down> \<phi>"
     shows "\<psi> \<noteq> \<phi>"
using sf
proof - 
  from sf have "\<psi> = \<phi> \<longrightarrow> \<phi> \<in> \<Down> \<phi>" by auto
  with evil_psform_nin show ?thesis by fast
qed

lemma sub_nosub [intro]: 
  assumes psub: "\<psi> \<in> \<Down> \<phi>"
     shows "\<psi>[\<phi>/\<chi>] = \<psi>"
using psub
proof (induct \<psi>)
       case E_P thus ?case by fastsimp
  next case E_Bot thus ?case by fastsimp
  next case E_PP thus ?case by fastsimp
  next case (E_Imp \<delta> \<kappa>)
   moreover hence "(\<delta> \<rightarrow> \<kappa>) \<noteq> \<phi>" by fast
   ultimately show ?case by (simp, blast)
  next case (E_B X \<psi>)
   moreover hence "\<box> X \<psi> \<noteq> \<phi>" by fast
   ultimately show ?case by (simp, blast)
  next case (E_BB X \<psi>)
   moreover hence "[-] X \<psi> \<noteq> \<phi>" by fast
   ultimately show ?case by (simp, blast)
  next case (E_BBI X \<psi>)
   moreover hence "[+] X \<psi> \<noteq> \<phi>" by fast
   ultimately show ?case by (simp, blast)
qed

text {* After showing all of the above, we have what we need to
  formalize our reasoning about EviL. *}

lemma evil_dneg_eq: "\<turnstile> \<not> (\<not> \<phi>) \<leftrightarrow> \<phi>"
proof -
  let ?\<theta> = "(\<not>\<^bsub>CL\<^esub> (\<not>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<phi>)) \<leftrightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> \<phi>)" 
  have "?\<theta> \<in> CL" by fastsimp
  with evil_ClassAx.cl_translate [where \<phi>="?\<theta>"] 
  show ?thesis by simp
qed

lemma "\<turnstile> [-] X \<phi> \<rightarrow> \<phi>"
--{* If @{term "\<phi>"} holds no matter what $X$ tries to forget, *}
--{* then it must be that @{term "\<phi>"} holds simpliciter *}
proof -
  from evil_ax13 evil_ax4 evil_ClassAx.hs
    have \<heartsuit>: "\<turnstile> (\<not> \<phi>) \<rightarrow> \<langle>-\<rangle> X (\<not> \<phi>)" by fast
  moreover have "\<phi> \<in> \<Down> (\<not> \<not> \<phi>)" by simp
    with sub_nosub have "\<phi>[\<not> \<not> \<phi>/ \<phi>] = \<phi>" by blast
  moreover have "\<bottom> \<in> \<Down> (\<not> \<not> \<phi>)" by simp
    with sub_nosub have "\<bottom>[\<not> \<not> \<phi>/ \<phi>] = \<bottom>" by blast
  moreover note
    evil_sub [where \<phi>="\<not> \<not> \<phi>"
                and \<psi>="\<phi>"
                and \<chi>="(\<not> \<phi>) \<rightarrow> \<langle>-\<rangle> X (\<not> \<phi>)"]
    evil_not_neq [where \<phi>="\<phi>"]
    evil_dneg_eq [where \<phi>="\<phi>"]
    evil_eq_mp
  ultimately have
    "\<turnstile> \<not> \<phi> \<rightarrow> \<not> [-] X \<phi>" by auto
  with evil_ax3 evil_mp
    show ?thesis by blast
qed

lemma evil_dax13: "\<turnstile> \<langle>-\<rangle> X ([+] X \<phi>) \<rightarrow> \<phi>"
proof -
  from evil_ax14 [where \<phi>="\<not> \<phi>" and X="X"]
  moreover have "(\<not> \<phi>) \<in> \<Down> (\<not> \<not> \<phi>)" by simp
    with sub_nosub have "(\<not> \<phi>)[\<not> \<not> \<phi>/ \<phi>] = (\<not> \<phi>)" by blast
  moreover have "\<bottom> \<in> \<Down> (\<not> \<not> \<phi>)" by simp
    with sub_nosub have "\<bottom>[\<not> \<not> \<phi>/ \<phi>] = \<bottom>" by blast
  moreover note
    evil_sub [where \<phi>="\<not> \<not> \<phi>"
                and \<psi>="\<phi>"
                and \<chi>="\<not> \<phi> \<rightarrow> [-] X (\<langle>+\<rangle> X (\<not> \<phi>))"]
    evil_not_neq [where \<phi>="\<phi>"]
    evil_dneg_eq [where \<phi>="\<phi>"]
    evil_eq_mp
  ultimately
    have "\<turnstile> \<not> \<phi> \<rightarrow> [-] X (\<not> [+] X \<phi>)" by auto
  moreover 
    let ?\<theta>="(\<not>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> \<phi>) \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> ([-] X (\<not> [+] X \<phi>)))
            \<rightarrow>\<^bsub>CL\<^esub> (\<not>\<^bsub>CL\<^esub> (P#\<^bsub>CL\<^esub> ([-] X (\<not> [+] X \<phi>))) \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub> \<phi>)"
    have "?\<theta> \<in> CL" by fastsimp
  moreover note evil_ClassAx.cl_translate [where \<phi>="?\<theta>"]
                evil_mp
  ultimately show ?thesis by fastsimp
qed

lemma evil_BB_ax5: "\<turnstile> [-] X \<phi> \<rightarrow> [-] X ([-] X \<phi>)"
--{* If @{term "\<phi>"} is true no matter what $X$ *}
--{* tries to forget, then it's true no matter *}
--{* what further evidence she disregards *}
proof -
  from EviL.intros have "\<turnstile> \<not> \<phi> \<rightarrow> [+] X (\<langle>-\<rangle> X (\<not> \<phi>))" by fast
  with evil_ax5 [where X="X"]
       evil_ClassAx.hs 
    have "\<turnstile> \<not> \<phi> \<rightarrow> [+] X ([+] X (\<langle>-\<rangle> X (\<not> \<phi>)))" by blast
  with evil_DBB_map [where X="X"] have 
   "\<turnstile> \<langle>-\<rangle> X (\<langle>-\<rangle> X (\<not> \<phi>)) 
      \<rightarrow> \<langle>-\<rangle> X (\<langle>-\<rangle> X ([+] X ([+] X (\<langle>-\<rangle> X (\<not> \<phi>)))))" by blast
  with evil_dax13 [where X="X"
                     and \<phi>="[+] X (\<langle>-\<rangle> X (\<not> \<phi>))"]
       evil_DBB_map [where X="X"]
       evil_ClassAx.hs
  have "\<turnstile> \<langle>-\<rangle> X (\<langle>-\<rangle> X (\<not> \<phi>)) \<rightarrow> \<langle>-\<rangle> X ([+] X (\<langle>-\<rangle> X (\<not> \<phi>)))" by blast
  with evil_dax13 [where X="X"
                     and \<phi>="\<langle>-\<rangle> X (\<not> \<phi>)"]
       evil_DBB_map [where X="X"]
       evil_ClassAx.hs
  have "\<turnstile> \<langle>-\<rangle> X (\<langle>-\<rangle> X (\<not> \<phi>)) \<rightarrow> \<langle>-\<rangle> X (\<not> \<phi>)" by blast
  moreover have "\<bottom> \<in> \<Down> (\<not> \<not> \<phi>)" by simp
    hence "\<bottom>[\<not> \<not> \<phi>/ \<phi>] = \<bottom>" by fast
  moreover have "\<phi> \<in> \<Down> ([-] X (\<not> \<not> \<phi>))" by simp
    hence "\<phi> \<noteq> [-] X (\<not> \<not> \<phi>)" by fast
  moreover note 
    evil_sub [where \<phi>="\<not> \<not> \<phi>"
                and \<psi>="\<phi>"
                and \<chi>="\<langle>-\<rangle> X (\<langle>-\<rangle> X (\<not> \<phi>)) \<rightarrow> \<langle>-\<rangle> X (\<not> \<phi>)"]
    evil_dneg_eq [where \<phi>="\<phi>"]
    evil_eq_mp
  ultimately have
    "\<turnstile> \<langle>-\<rangle> X (\<not> ([-] X \<phi>)) \<rightarrow> \<not> ([-] X \<phi>)" by fastsimp
  moreover have "\<bottom> \<in> \<Down> (\<not> \<not> [-] X \<phi>)" by simp
    hence "\<bottom>[\<not> \<not> [-] X \<phi> / [-] X \<phi>] = \<bottom>" by fast
  moreover have "(\<not> [-] X \<phi>) \<in> \<Down> (\<not> \<not> [-] X \<phi>)" by simp
    hence "(\<not> [-] X \<phi>)[\<not> \<not> [-] X \<phi> / [-] X \<phi>] 
           = (\<not> [-] X \<phi>)" by fast
  moreover note 
    evil_sub [where \<phi>="\<not> \<not> [-] X \<phi>"
                and \<psi>="[-] X \<phi>"
                and \<chi>="\<langle>-\<rangle> X (\<not> [-] X \<phi>) \<rightarrow> (\<not> [-] X \<phi>)"]
    evil_dneg_eq [where \<phi>="[-] X \<phi>"]
    evil_eq_mp
  ultimately have "\<turnstile> \<not> [-] X ([-] X \<phi>) \<rightarrow> \<not> ([-] X \<phi>)"
    by fastsimp 
  with evil_ax3 evil_mp show ?thesis by blast
qed