header {* Locales for EviL Properties *}

theory EviL_Properties
imports EviL_Semantics
begin

text
{* In this file we define two locales on EviL Kripke models, 
   which we will be critical for proving the \emph{column lemmas} 
   and ultimately the \emph{translation lemma}.

   The first locale will assume properties which we 
   shall prove our Lindenbaum construction satisfies.  
*}

locale partly_EviL =
  fixes M :: "('w,'a,'b) evil_kripke"
  assumes prop0: "RBB(M)(X) \<subseteq> (W(M) <*> W(M))"
      and prop1: "finite (W(M))"
      and prop2: "refl_on (W(M)) (RBB(M)(X))"
      and prop3: "trans (RBB(M)(X))"
      and prop4: "RBBI(M)(X) = (RBB(M)(X))^-1"
      and prop5: "(w,v) \<in> RBB(M)(X) \<Longrightarrow> V(M)(w) = V(M)(v)" 
      and prop6: "\<lbrakk>(w,v) \<in> RBB(M)(X); (w,u) \<in> RB(M)(X)\<rbrakk>
                    \<Longrightarrow> (v,u) \<in> RB(M)(X)"
      and prop7: "(w,v) \<in> RBB(M)(X) 
                    \<Longrightarrow> ((u,w) \<in> RB(M)(Y)) = ((u,v) \<in> RB(M)(Y))"
      and prop8: "w \<in> PP(M)(X) \<Longrightarrow> (w,w) \<in> RB(M)(X)"

text
{* Our second locale strengthens the final 8th property of the
   first locale to a full biconditional; the \emph{EviL
   bisimulation lemma} will establish that any \emph{partly EviL}
   Kripke model is bisimular to a \emph{completely EviL}
   Kripke model. *}

locale completely_EviL = partly_EviL +
  assumes prop9: "(w \<in> PP(M)(X)) = ((w,w) \<in> RB(M)(X))"

end