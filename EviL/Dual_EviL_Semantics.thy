header{* Dual EviL Grammar and Semantics *}

theory Dual_EviL_Semantics
imports EviL_Semantics
begin

text
{* It should be noted that the previous grammar and 
   semantics for EviL we have given are convenient 
   for certain parts of the model theory of EviL and
   inconvenient for others.  For instance, since 
   classical logic may be axiomatized so succinctly using
   just letters, implication and falsum, and then confers 
   Lindenbaum constructions to \emph{any} extension, it is
   useful to have a grammar that reflects this. Likewise,
   the celebrated \emph{axiom K} suggests that modal logic
   is naturally captured by extending the grammar of classical 
   logic in precisely the manner we have, that is by 
   incorporating modal $\Box$ operators. On the other hand, 
   inductive arguments in this grammar and resulting can 
   be challenging at times. However, the same inductive arguments 
   in the \emph{dual} grammar, incorporating letters, 
   disjunction, negation, verum, and modal $\Diamond$ can 
   be significantly simpler. *}

text
{* In this file, we give an alternate, \emph{dual} grammar 
   and semantics for both the Kripke and set-theoretic 
   semantics for EviL, and in both cases we show
   that the original semantics are equivalent to the dual 
   semantics under translation. *}

datatype ('a,'b) devil_form = 
    DE_P 'a                         ("P#' _")
  | DE_Top                          ("\<top>")
  | DE_Conj "('a,'b) devil_form" 
            "('a,'b) devil_form"    (infixr "\<and>" 30)
  | DE_Neg "('a,'b) devil_form"     ("\<not> _" [40] 40)
  | DE_D 'b "('a,'b) devil_form"    ("\<diamond>")
  | DE_PP 'b                        ("\<odot>'")
  | DE_DD 'b "('a,'b) devil_form"   ("\<langle>-\<rangle>")
  | DE_DDI 'b "('a,'b) devil_form"  ("\<langle>+\<rangle>")

fun devil_eval :: "('a,'b) evil_world set 
                       \<Rightarrow> ('a,'b) evil_world 
                         \<Rightarrow> ('a,'b) devil_form 
                           \<Rightarrow> bool" ("_,_ ||\<Turnstile> _" 50) where
     "(_,(a,_) ||\<Turnstile> P#' p) = (p \<in> a)"
  |  "(_,_ ||\<Turnstile> \<top>) = True"
  |  "(\<Omega>,(a,A) ||\<Turnstile> \<phi> \<and> \<psi>) = 
      ((\<Omega>,(a,A) ||\<Turnstile> \<phi>) \<and> (\<Omega>,(a,A) ||\<Turnstile> \<psi>))"
  |  "(\<Omega>,(a,A) ||\<Turnstile> \<not> \<phi>) = (~ (\<Omega>,(a,A) ||\<Turnstile> \<phi>))"
  |  "(\<Omega>,(a,A) ||\<Turnstile> \<diamond> X \<phi>) = 
      (\<exists>(b,B) \<in> \<Omega>. (\<forall>\<chi> \<in> A(X). b \<Turnstile> \<chi>)  
                    \<and>  \<Omega>,(b,B) ||\<Turnstile> \<phi>)"
  |  "(\<Omega>,(a,A) ||\<Turnstile> \<odot>' X) = (\<forall>\<chi> \<in> A(X). a \<Turnstile> \<chi>)"
  |  "(\<Omega>,(a,A) ||\<Turnstile> \<langle>-\<rangle> X \<phi>) = (\<exists>(b,B) \<in> \<Omega>. a = b 
                              \<and> B(X) \<subseteq> A(X) 
                              \<and>  \<Omega>,(b,B) ||\<Turnstile> \<phi>)"
  |  "(\<Omega>,(a,A) ||\<Turnstile> \<langle>+\<rangle> X \<phi>) = 
      (\<exists>(b,B) \<in> \<Omega>. a = b \<and> B(X) \<supseteq> A(X) \<and>  \<Omega>,(b,B) ||\<Turnstile> \<phi>)"

fun devil_modal_eval :: "('w,'a,'b) evil_kripke 
                         \<Rightarrow> 'w
                           \<Rightarrow> ('a,'b) devil_form
                             \<Rightarrow> bool" ("_,_ ||\<turnstile> _" 50) where
     "(M,w ||\<turnstile> P#' p) = (p \<in> V(M)(w))"
  |  "(_,_ ||\<turnstile> \<top>) = True"
  |  "(M,w ||\<turnstile> \<phi> \<and> \<psi>) = 
      ((M,w ||\<turnstile> \<phi>) \<and> (M,w ||\<turnstile> \<psi>))"
  |  "(M,w ||\<turnstile> \<not> \<phi>) = (~ (M,w ||\<turnstile> \<phi>))"
  |  "(M,w ||\<turnstile>  \<diamond> X \<phi>) = 
      (\<exists>v \<in> W(M). (w,v) \<in> RB(M)(X) \<and> M,v ||\<turnstile> \<phi>)"
  |  "(M,w ||\<turnstile> \<odot>' X) = (w \<in> PP(M)(X))"
  |  "(M,w ||\<turnstile> \<langle>-\<rangle> X \<phi>) = 
      (\<exists>v \<in> W(M). (w,v) \<in> RBB(M)(X) \<and> M,v ||\<turnstile> \<phi>)"
  |  "(M,w ||\<turnstile> \<langle>+\<rangle> X \<phi>) = 
      (\<exists>v \<in> W(M). (w,v) \<in> RBBI(M)(X) \<and> M,v ||\<turnstile> \<phi>)"

primrec devil :: "('a,'b) evil_form 
                   \<Rightarrow> ('a,'b) devil_form" where
    "devil P# p = P#' p"
  | "devil \<bottom> = (\<not> \<top>)"
  | "devil (\<phi> \<rightarrow> \<psi>) = (\<not> ((devil \<phi>) \<and> \<not> (devil \<psi>)))"
  | "devil (\<box> X \<phi>) = (\<not> (\<diamond> X  (\<not> (devil \<phi>))))"
  | "devil (\<odot> X) = \<odot>' X"
  | "devil ([-] X \<phi>) = (\<not> (\<langle>-\<rangle> X  (\<not> (devil \<phi>))))"
  | "devil ([+] X \<phi>) = (\<not> (\<langle>+\<rangle> X  (\<not> (devil \<phi>))))"

text
{* In all cases, the equivalence 
   of the semantics follows from routine,
   utterly mechanical induction. *}

lemma evil_devil1:
  "\<forall>M. \<forall>w. (M,w |\<Turnstile> \<phi>) = (M,w ||\<Turnstile> devil \<phi>)"
by (induct \<phi>, fastsimp+)

lemma evil_devil2:
  "\<forall>M. \<forall>w. (M,w |\<turnstile> \<phi>) = (M,w ||\<turnstile> devil \<phi>)"
by (induct \<phi>, fastsimp+)

text
{* Next, we present a primitive recursive 
   subformula operation.  We show
   that it results in a finite list. *}

primrec devil_subforms 
 :: "('a,'b) devil_form \<Rightarrow> ('a,'b) devil_form set" ("\<down>")
where
    "\<down>(P#' p) = {P#' p}"
  | "\<down>(\<top>) = {\<top>}"
  | "\<down>(\<not> \<phi>) = {\<not> \<phi>} \<union> \<down>(\<phi>)"
  | "\<down>(\<phi> \<and> \<psi>) = {\<phi> \<and> \<psi>} \<union> \<down>(\<phi>) \<union> \<down>(\<psi>)"
  | "\<down>(\<diamond> X \<phi>) = {\<diamond> X \<phi>} \<union> \<down>(\<phi>)"
  | "\<down>(\<odot>' X) = {\<odot>' X}"
  | "\<down>(\<langle>-\<rangle> X \<phi>) = {\<langle>-\<rangle> X \<phi>} \<union> \<down>(\<phi>)"
  | "\<down>(\<langle>+\<rangle> X \<phi>) = {\<langle>+\<rangle> X \<phi>} \<union> \<down>(\<phi>)"

lemma finite_devil_subforms:
"finite (\<down> \<phi>)"
   by (induct \<phi>, simp_all)

lemma subform_refl [simp]:
"\<phi> \<in> \<down>\<phi>" 
  by (induct \<phi>, simp_all)
 
text
{* We next define a locale for a letter
   grabbing operation @{term "\<rho>"},
   which we shall employ in various model
   theoretic arguments.  *}

locale EviL_\<rho> =
  fixes \<phi> :: "('a, 'b) devil_form"
  fixes Ws :: "'w set"
  fixes L :: "'a set"
  assumes infi_L: "infinite L"
      and fini_Ws: "finite Ws"

definition (in EviL_\<rho>) \<rho> :: "'w \<Rightarrow> 'a"
where "\<rho> == SOME g. inj_on g Ws 
                  \<and> range g \<subseteq> (L - {p. (P#' p) \<in> (\<down> \<phi>)})"

text
{* Above, we have picked @{term "\<rho>"} to have the
   properties we desire, but we really have to prove
   that something like this exists or else we are
   talking nonsense (alas, this is the eternal curse
   of Brouwer's fallen angels, who forsook intuition
   and instead chose choice).  Fortunately, the existance of
   the desired function is a consequence of various
   other facts we have as background. *}

lemma (in EviL_\<rho>) \<rho>_works:
  "inj_on \<rho> Ws
       \<and> range \<rho> \<subseteq> L - {p. (P#' p) \<in> (\<down> \<phi>)}"
proof -
  have "finite {p. (P#' p) \<in> (\<down> \<phi>)}"
    by (induct \<phi>) simp_all
  with infi_L Diff_infinite_finite
  have "infinite (L - {p. (P#' p) \<in> (\<down> \<phi>)})"
    by blast
  with fini_Ws have "\<exists> g. inj_on g Ws 
         \<and> range g \<subseteq> (L - {p. (P#' p) \<in> (\<down> \<phi>)})"
   by (fastsimp intro!: fin_inj_on_infi)
  with \<rho>_def
   and someI_ex [where P="% g. inj_on g Ws
                 \<and> range g \<subseteq> (L - {p. (P#' p) \<in> (\<down> \<phi>)})"]
  show ?thesis by fastsimp
qed

text
{* Next we'll show that @{term "\<phi>"} can't really talk about
   @{term "P#' \<rho>(w)"}, and that @{term "\<rho>"} preserves
   equality in @{term "Ws"}. *}

lemma (in EviL_\<rho>) \<phi>_vocab:
shows "P#' \<rho>(w) \<notin> \<down>\<phi>"
using \<rho>_works rangeI
  by fastsimp

lemma (in EviL_\<rho>) \<rho>_eq:
shows "{w,v} \<subseteq> Ws \<Longrightarrow> (w = v) = (\<rho>(w) = \<rho>(v))"
using \<rho>_works
 by (auto, unfold inj_on_def, blast)

end