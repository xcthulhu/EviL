header{* EviL Grammar and Semantics *}

theory EviL_Semantics
imports Classic
begin

text
{* We now give the grammar and semantics for EviL.
   We shall be employing two different kinds of semantics
   for EviL - EviL world sets / EviL world pairs and
   also conventional Kripke semantics. *}

no_notation
  bot ("\<bottom>") and
  imp (infixr "\<rightarrow>" 25)  and
  vdash ("\<turnstile> _" [20] 20) and
  lift_vdash (infix ":\<turnstile>" 10) and
  Not  ("\<not> _" [40] 40) and
  neg ("\<not> _" [40] 40) and
  pneg ("\<sim> _" [40] 40) and
  CL_P ("P#") and
  CL_Bot ("\<bottom>") and
  CL_Imp (infixr "\<rightarrow>" 25)

text
{* The datatype below defines a language of a modal logic with
   a possibly infinite number of agents, which we represent with a
   @{typ "'b"}.  Informally, we might write this using the following
   BNF grammar (with some Isabelle style type annotations):
   \[ \phi\ ::=\ \alpha\ |\ \bot\ |\ \phi \rightarrow \psi\ 
      | \Box_X \phi \ |\ \odot_X\  
      |\ \boxbox_X \phi\ |\ \boxbox^{-1}_X \phi \] *}

datatype ('a,'b) evil_form = 
    E_P 'a                                         ("P# _")
  | E_Bot                                          ("\<bottom>")
  | E_Imp "('a,'b) evil_form" "('a,'b) evil_form"  (infixr "\<rightarrow>" 25)
  | E_B 'b "('a,'b) evil_form"                     ("\<box>")
  | E_PP 'b                                        ("\<odot>")
  | E_BB 'b "('a,'b) evil_form"                    ("[-]")
  | E_BBI 'b "('a,'b) evil_form"                   ("[+]")

types ('a,'b) evil_world = "'a set * ('b \<Rightarrow> ('a cl_form set))"

text
{* We now turn to giving the recursive, compositional EviL semantic 
   evaluation function.  EviL can be understood to rest on the 
   semantics for classical propositional logic we have previously 
   given.  This gives EviL a sort of Russian doll semantics, in way. *}

fun evil_eval :: "('a,'b) evil_world set 
                       \<Rightarrow> ('a,'b) evil_world 
                         \<Rightarrow> ('a,'b) evil_form 
                           \<Rightarrow> bool" ("_,_ |\<Turnstile> _" 50) where
     "(_,(a,_) |\<Turnstile> P# p) = (p \<in> a)"
  |  "(_,_ |\<Turnstile> \<bottom>) = False"
  |  "(\<Omega>,(a,A) |\<Turnstile> \<phi> \<rightarrow> \<psi>) = 
        ((\<Omega>,(a,A) |\<Turnstile> \<phi>) \<longrightarrow> (\<Omega>,(a,A) |\<Turnstile> \<psi>))"
  |  "(\<Omega>,(a,A) |\<Turnstile> \<box> X \<phi>) = 
        (\<forall>(b,B) \<in> \<Omega>. (\<forall>\<chi> \<in> A(X). b \<Turnstile> \<chi>)  
                        \<longrightarrow>  \<Omega>,(b,B) |\<Turnstile> \<phi>)"
  |  "(\<Omega>,(a,A) |\<Turnstile> \<odot> X) = (\<forall>\<chi> \<in> A(X). a \<Turnstile> \<chi>)"
  |  "(\<Omega>,(a,A) |\<Turnstile> [-] X \<phi>) = 
        (\<forall>(b,B) \<in> \<Omega>. a = b 
           \<longrightarrow> B(X) \<subseteq> A(X) 
             \<longrightarrow>  \<Omega>,(b,B) |\<Turnstile> \<phi>)"
  |  "(\<Omega>,(a,A) |\<Turnstile> [+] X \<phi>) = 
        (\<forall>(b,B) \<in> \<Omega>. a = b 
           \<longrightarrow> B(X) \<supseteq> A(X) 
             \<longrightarrow>  \<Omega>,(b,B) |\<Turnstile> \<phi>)"

text
{* Here are the Kripke semantics for EviL, which shall be critical
   for Henkin truth lemmas, Lindenbaum model construction and other
   model theoretic concerns. *}

record ('w,'a,'b) evil_kripke =
  W :: "'w set"
  V :: "'w \<Rightarrow> 'a \<Rightarrow> bool"
  PP :: "'b \<Rightarrow> 'w set"
  RB :: "'b \<Rightarrow> ('w * 'w) set"
  RBB :: "'b \<Rightarrow> ('w * 'w) set"
  RBBI :: "'b \<Rightarrow> ('w * 'w) set"

fun evil_modal_eval :: "('w,'a,'b) evil_kripke 
                         \<Rightarrow> 'w
                           \<Rightarrow> ('a,'b) evil_form
                             \<Rightarrow> bool" ("_,_ |\<turnstile> _" 50) where
     "(M,w |\<turnstile> P# p) = (p \<in> V(M)(w))"
  |  "(_,_ |\<turnstile> \<bottom>) = False"
  |  "(M,w |\<turnstile> \<phi> \<rightarrow> \<psi>) = 
          ((M,w |\<turnstile> \<phi>) \<longrightarrow> (M,w |\<turnstile> \<psi>))"
  |  "(M,w |\<turnstile>  \<box> X \<phi>) = 
          (\<forall>v \<in> W(M). (w,v) \<in> RB(M)(X)  
                      \<longrightarrow>  M,v |\<turnstile> \<phi>)"
  |  "(M,w |\<turnstile> \<odot> X) = (w \<in> PP(M)(X))"
  |  "(M,w |\<turnstile> [-] X \<phi>) = 
          (\<forall>v \<in> W(M). (w,v) \<in> RBB(M)(X) 
                      \<longrightarrow>  M,v |\<turnstile> \<phi>)"
  |  "(M,w |\<turnstile> [+] X \<phi>) = 
          (\<forall>v \<in> W(M). (w,v) \<in> RBBI(M)(X) 
                      \<longrightarrow>  M,v |\<turnstile> \<phi>)"

end