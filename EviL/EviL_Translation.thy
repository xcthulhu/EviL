header{* Translating EviL Kripke Semantics *}

theory EviL_Translation
imports Dual_EviL_Semantics 
        EviL_Properties
        EviL_Columns
begin

text
{* In this file we give the translation
   lemma, which states that if there is if
   the type we have been employing has an
   infinite number of inhabitants, then
   for each Kripke
   model and each formula, there's
   some set-based EviL model that makes
   that formula true. *}

text
{* To prove this theorem, we shall introduce
   work in a locale extending \textsf{completely_Evil}.
   We would have prefered to not have @{term "w"} in  *} 

locale translate_EviL = completely_EviL +
  fixes w :: "'w"
  fixes \<phi> :: "('a, 'b) devil_form"
  fixes L :: "'a set"
  fixes Ws :: "'w set set"
  assumes infi_L: "infinite L"
      and models: "M,w ||\<turnstile> \<phi>"
      and Ws_def: "Ws = Pow (W(M))"

text
{* First, we'll introduce @{term "\<rho>"}, the letter picker,
   which is critical to our model construction *}

sublocale translate_EviL \<subseteq> EviL_\<rho>
proof unfold_locales
  from infi_L
  show "infinite L" .
  from prop1 Ws_def
  show "finite Ws" by simp
qed

text
{* Next, we'll abbreviate a bunch of helper functions; 
   these are part of a much more elaborate function we'll
   define afterwards. *}

definition (in translate_EviL)
--"The visible letters"
vletts :: "'w \<Rightarrow> 'a set" where 
  "vletts v == {a. ((P#' a) \<in> \<down>\<phi>) \<and> (M,v ||\<turnstile> P#' a)}"

definition (in translate_EviL)
--"The invisible letter"
ilett :: "'w \<Rightarrow> 'a set" where 
  "ilett v = {\<rho> (col M v)}"

definition (in translate_EviL)
letts :: "'w \<Rightarrow> 'a set" where
  "letts v = (vletts v) \<union> (ilett v)"

text
{* Now is a good time to introduce some notation
   for classical logic syntax. *}

notation (in translate_EviL)
CL_P     ("P#\<^bsub>CL\<^esub>") and
CL_Bot   ("\<bottom>\<^bsub>CL\<^esub>")  and
CL_Imp   (infixr "\<rightarrow>\<^bsub>CL\<^esub>" 25)

text
{* We now turn to coding up agents' beliefs. *}

definition (in translate_EviL)
--{*That which @{term "X"} refuses to believe*}
disblvs :: "'w \<Rightarrow> 'b \<Rightarrow> 'a cl_form set" where
  "disblvs v X = {\<phi>. \<exists>w \<in> W(M). \<phi>=(P#\<^bsub>CL\<^esub>(\<rho>(col M w)) \<rightarrow>\<^bsub>CL\<^esub> \<bottom>\<^bsub>CL\<^esub>) 
                    \<and> (v,w) \<notin> RB(M)(X)}"

definition (in translate_EviL)
--{*Tautologies @{term "X"} believes about her ancestors*}
parblvs :: "'w \<Rightarrow> 'b \<Rightarrow> 'a cl_form set" where
  "parblvs v X = 
   {\<phi>. \<exists>w \<in> W(M). \<phi>=(\<bottom>\<^bsub>CL\<^esub> \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub>(\<rho> {w})) 
                  \<and> (v,w) \<in> RBB(M)(X)}"

definition (in translate_EviL)
blvs :: "'w \<Rightarrow> 'b \<Rightarrow> 'a cl_form set" where
  "blvs v X = (parblvs v X) \<union> (disblvs v X)"

text
{* We now give the map, which we shall call @{term "\<xi>"},
   which takes worlds in the model @{term "M"} to 
   their EviL counterparts. *}

definition (in translate_EviL)
\<xi> :: "'w \<Rightarrow> ('a,'b) evil_world" where
  "\<xi> v = (letts v, (% X. blvs v X))"

declare (in translate_EviL) 
  vletts_def [simp] and
  ilett_def [simp]  and
  letts_def [simp] and
  parblvs_def [simp] and
  disblvs_def [simp] and
  blvs_def [simp]

text
{* We now define @{term "\<Omega>"}, the EviL model we are constructing,
   along with ghost-relations it possesses.  We shall prove some
   basic theorems about these ghost-relations that we will need 
   for proving the main lemma. *}

definition (in translate_EviL)
\<Omega> :: "('a,'b) evil_world set" where
  "\<Omega> = \<xi> ` W(M)"

definition (in translate_EviL)
\<Omega>RB :: "'b \<Rightarrow> (('a,'b) evil_world * ('a,'b) evil_world) set" where
  "\<Omega>RB X = {((a,A),(b,B)) . \<forall>\<chi> \<in> A(X). b \<Turnstile> \<chi>}"

definition (in translate_EviL)
\<Omega>RBB :: "'b \<Rightarrow>   (('a,'b) evil_world 
                 * ('a,'b) evil_world) set" where
  "\<Omega>RBB X = {((a,A),(b,B)) . a = b \<and> B(X) \<subseteq> A(X)}"

definition (in translate_EviL)
\<Omega>RBBI :: "'b \<Rightarrow> (('a,'b) evil_world 
                * ('a,'b) evil_world) set" where
  "\<Omega>RBBI X = {((a,A),(b,B)) . a = b \<and> A(X) \<subseteq> B(X)}"

declare (in translate_EviL) 
   \<Omega>RB_def [simp] and
   \<Omega>RBB_def [simp] and
   \<Omega>RBBI_def [simp]

lemma (in translate_EviL) D_ghost_of_RB:
   assumes "\<Omega>,bB ||\<Turnstile> \<psi>" 
       and "(aA,bB) \<in> \<Omega>RB(X)"
       and "bB \<in> \<Omega>"
     shows "\<Omega>,aA ||\<Turnstile> \<diamond> X \<psi>"
using assms
by fastsimp

lemma (in translate_EviL) ghost_of_RB:
  assumes A: "{v,u} \<subseteq> W(M)"
  shows "((v,u) \<in> RB(M)(X)) = ((\<xi> v, \<xi> u) \<in> \<Omega>RB(X))"
proof -
  let ?vXBeliefs = "snd (\<xi> v) X"
  let ?uwrld = "fst(\<xi> u)"
  { assume B: "(v,u) \<in> RB(M)(X)"
    have "(\<xi> v, \<xi> u) \<in> \<Omega>RB(X)"
    proof -
      { fix q; assume C: "q \<in> W(M)"
        with A B col_RB_eqp col_mem_eq col_refl
        have "(col M u) = (col M q) 
                 \<longrightarrow> (v,q) \<in> RB(M)(X)" by fast
        moreover from A C mem_col_subseteq Ws_def
        have "{col M u, col M q} \<subseteq>  Ws" by simp
        moreover note \<rho>_eq
        ultimately have "\<rho> (col M u) = \<rho> (col M q)
                          \<longrightarrow> (v,q) \<in> RB(M)(X)" by blast }
      hence "(P#\<^bsub>CL\<^esub>(\<rho>(col M u)) \<rightarrow>\<^bsub>CL\<^esub> \<bottom>\<^bsub>CL\<^esub>) \<notin> ?vXBeliefs" 
        by (simp add: \<Omega>_def \<xi>_def)
      with A \<phi>_vocab show ?thesis 
         by (fastsimp simp add: \<Omega>_def \<xi>_def)
    qed }
  moreover 
  { assume D: "(v,u) \<notin> RB(M)(X)"
    have "(\<xi> v, \<xi> u) \<notin> \<Omega>RB(X)"
    proof -
      from A D have "(P#\<^bsub>CL\<^esub>(\<rho>(col M u)) \<rightarrow>\<^bsub>CL\<^esub> \<bottom>\<^bsub>CL\<^esub>) \<in> ?vXBeliefs" 
        by (fastsimp simp add: \<Omega>_def \<xi>_def)
      hence "~ (\<forall>\<chi> \<in> ?vXBeliefs. ?uwrld \<Turnstile> \<chi>)" 
        by (fastsimp simp add: \<Omega>_def \<xi>_def)
      thus ?thesis by (simp add: \<Omega>_def \<xi>_def)
    qed }
   ultimately show ?thesis by fast
qed

lemma (in translate_EviL) D_ghost_of_RBB: 
   assumes "\<Omega>,bB ||\<Turnstile> \<psi>" 
       and "(aA,bB) \<in> \<Omega>RBB(X)"
       and "bB \<in> \<Omega>"
     shows "\<Omega>,aA ||\<Turnstile> \<langle>-\<rangle> X \<psi>"
using assms
by (auto,blast)

lemma (in translate_EviL) ghost_of_RBB:
  assumes A: "{v,u} \<subseteq> W(M)"
  shows "((v,u) \<in> RBB(M)(X)) = ((\<xi> v, \<xi> u) \<in> \<Omega>RBB(X))"
using A
proof -
  { assume B: "(\<xi> v, \<xi> u) \<in> \<Omega>RBB(X)"
      have "(v,u) \<in> RBB(M)(X)"
      proof -
        from prop2 A
        have "(\<bottom>\<^bsub>CL\<^esub> \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub>(\<rho> {u})) \<in> (blvs u) X"
          by (unfold refl_on_def,
              simp add: \<Omega>_def \<xi>_def,
              blast)
        moreover from B 
        have "(blvs u) X \<subseteq> (blvs v) X"
          by (simp add: \<Omega>_def \<xi>_def)
        ultimately have
          "(\<bottom>\<^bsub>CL\<^esub> \<rightarrow>\<^bsub>CL\<^esub> P#\<^bsub>CL\<^esub>(\<rho> {u})) \<in> (blvs v) X"
          by fast
        from this obtain w where
              "w\<in>W M"
          and "EviL_\<rho>.\<rho> \<phi> Ws L {u} = EviL_\<rho>.\<rho> \<phi> Ws L {w}"
          and \<heartsuit>: "(v, w) \<in> RBB(M)(X)" 
          by (fastsimp simp add: \<Omega>_def \<xi>_def) 
        with A Ws_def \<rho>_eq [where v="{u}" and w="{w}"]
          show ?thesis by simp
      qed
  }
  moreover  
  { assume C: "(v,u) \<in> RBB(M)(X)"
    with col_def [where M="M" and w="v"] 
      have "u \<in> col M v" by fastsimp
    with col_mem_eq [where w="v" and v="u" and M="M"]
         col_V_eq [where w="v" and v="u"]
    have "letts u = letts v" by simp
    moreover 
    have "blvs u X \<subseteq>  blvs v X"
    proof -
      from C prop3 have "parblvs u X \<subseteq> parblvs v X"
        by (unfold trans_def parblvs_def, blast)
      moreover 
      from C prop6 have "disblvs u X \<subseteq> disblvs v X"
        by (unfold disblvs_def, blast)
      ultimately show ?thesis by (simp, blast)
    qed 
    ultimately have "(\<xi> v, \<xi> u) \<in> \<Omega>RBB(X)" 
      by (simp add: \<xi>_def del: blvs_def) }
  ultimately show ?thesis by fast
qed

lemma (in translate_EviL) D_ghost_of_RBBI: 
   assumes "\<Omega>,bB ||\<Turnstile> \<psi>" 
       and "(aA,bB) \<in> \<Omega>RBBI(X)"
       and "bB \<in> \<Omega>"
     shows "\<Omega>,aA ||\<Turnstile> \<langle>+\<rangle> X \<psi>"
using assms
by (auto,blast)

lemma (in translate_EviL) ghost_of_RBBI:
  assumes A: "{v,u} \<subseteq> W(M)"
  shows "((v,u) \<in> RBBI(M)(X)) = ((\<xi> v, \<xi> u) \<in> \<Omega>RBBI(X))"
using A prop4 ghost_of_RBB
by fastsimp

text
{* We now turn to showing that our construction is finite
   in two important ways. *}

definition
  pretty_finite :: "('a,'b) evil_world set \<Rightarrow> bool" where
  "pretty_finite \<Omega> = (\<forall>(a,A) \<in> \<Omega> . (finite a) 
                       \<and> (\<forall>X . finite (A(X))))"

declare
  pretty_finite_def [simp]

lemma (in translate_EviL) finite_letts:
"pretty_finite \<Omega>"
proof -
  { fix w;
    have "finite {a. (P#' a) \<in> \<down>\<phi>}"
      by (induct \<phi>, simp_all) 
    hence "finite (letts w)" by fastsimp }
  moreover
  { fix v X; from prop1 have "finite (blvs v X)" by simp }
  ultimately show ?thesis 
    by (simp add: \<Omega>_def \<xi>_def del: blvs_def)
qed

text
{* We now turn to proving the central lemma; this is done
   proving a much stronger induction and then weakening. *}

declare (in translate_EviL) 
   \<Omega>_def [simp] and
   \<xi>_def [simp]

lemma (in translate_EviL) translate_EviL_lemma:
assumes subform: "\<psi> \<in> (\<down> \<phi>)"
shows "\<forall> v \<in> W(M).  (M,v ||\<turnstile> \<psi>) = (\<Omega>,\<xi> v ||\<Turnstile> \<psi>)"
using subform
proof (induct \<psi>)
  case (DE_P p)
    assume Pp: "P#' p \<in> (\<down> \<phi>)"
    { fix v
      { assume "M,v ||\<turnstile> P#' p"
        with Pp have "p \<in> vletts v" by simp
        hence "\<Omega>, \<xi> v ||\<Turnstile> P#' p" by simp }
      moreover
      { assume "\<Omega>, \<xi> v ||\<Turnstile> P#' p"
        with Pp \<phi>_vocab have "p \<in> V(M)(v)" by fastsimp
        hence "M,v ||\<turnstile> P#' p" by simp } 
      ultimately have
        "(M,v ||\<turnstile> P#' p) = (\<Omega>, \<xi> v ||\<Turnstile> P#' p)" by fast }
    thus ?case by simp
  next case DE_Top
    show ?case by simp
  next case (DE_Conj \<psi> \<sigma>)
    moreover have "(\<psi> \<and> \<sigma>) \<in> \<down> \<phi> \<longrightarrow> {\<psi>,\<sigma>} \<subseteq> \<down> \<phi>"
      by (induct \<phi>, fastsimp+)
    ultimately show ?case by fastsimp
  next case (DE_Neg \<psi>)
    moreover have "(\<not> \<psi>) \<in> \<down> \<phi> \<longrightarrow> \<psi> \<in> \<down> \<phi>"
      by (induct \<phi>, fastsimp+)
    ultimately show ?case by fastsimp
  next case (DE_D X \<psi>)
    moreover have "(\<diamond> X \<psi>) \<in> \<down> \<phi> \<longrightarrow> \<psi> \<in> \<down> \<phi>"
      by (induct \<phi>, fastsimp+)
    ultimately have \<heartsuit>: "\<forall>v \<in> W(M). (M,v ||\<turnstile> \<psi>) = (\<Omega>,\<xi> v ||\<Turnstile> \<psi>)"
      by fast
    { fix v; assume \<spadesuit>: "v \<in> W(M)" 
                and "M,v ||\<turnstile> \<diamond> X \<psi>"
      from this obtain u where
          "M,u ||\<turnstile> \<psi>" 
      and "u \<in> W(M)" 
      and "(v,u) \<in> RB(M)(X)" by fastsimp 
      with \<heartsuit> \<spadesuit> ghost_of_RB 
      have "\<xi> u \<in> \<Omega>"
       and "\<Omega>,\<xi> u ||\<Turnstile> \<psi>"
       and "(\<xi> v, \<xi> u) \<in> \<Omega>RB(X)" by (simp del: \<xi>_def, fast+)
      hence "\<Omega>,\<xi> v ||\<Turnstile> \<diamond> X \<psi>" by (simp only: D_ghost_of_RB) }
    moreover
    { fix v; assume \<spadesuit>: "v \<in> W(M)"
                and "\<Omega>,\<xi> v ||\<Turnstile> \<diamond> X \<psi>"
      from this obtain u where
          "\<Omega>,\<xi> u ||\<Turnstile> \<psi>" 
      and "u \<in> W(M)" 
      and "(\<xi> v, \<xi> u) \<in> \<Omega>RB(X)" by fastsimp
      moreover with \<heartsuit> \<spadesuit> ghost_of_RB
        have "M,u ||\<turnstile> \<psi>" 
         and "(v, u) \<in> RB(M)(X)" by fast+
      ultimately have "M,v ||\<turnstile> \<diamond> X \<psi>" by fastsimp }
    ultimately show ?case by fast
  next case (DE_PP X)
    { fix v; assume \<spadesuit>: "v \<in> W(M)"
      moreover 
      from prop9
      have "(M,v ||\<turnstile> \<odot>' X) = ((v,v) \<in> RB(M)(X))" 
        by simp
      moreover 
      from \<spadesuit> \<phi>_vocab have 
        "(\<Omega>,\<xi> v ||\<Turnstile> \<odot>' X) = ((\<xi> v,\<xi> v) \<in> \<Omega>RB(X))"
        by fastsimp
      moreover note ghost_of_RB
      ultimately have
        "(M,v ||\<turnstile> \<odot>' X) = (\<Omega>,\<xi> v ||\<Turnstile> \<odot>' X)"
        by blast }
    thus ?case by fast
  next case (DE_DD X \<psi>)
    moreover have "(\<langle>-\<rangle> X \<psi>) \<in> \<down> \<phi> \<longrightarrow> \<psi> \<in> \<down> \<phi>"
      by (induct \<phi>, fastsimp+)
    ultimately have \<heartsuit>: "\<forall>v \<in> W(M). (M,v ||\<turnstile> \<psi>) = (\<Omega>,\<xi> v ||\<Turnstile> \<psi>)"
      by fast
    { fix v; assume \<spadesuit>: "v \<in> W(M)"
                   and "M,v ||\<turnstile> \<langle>-\<rangle> X \<psi>"
      from this obtain u where
          "M,u ||\<turnstile> \<psi>" 
      and "u \<in> W(M)" 
      and "(v,u) \<in> RBB(M)(X)" by fastsimp
      with \<heartsuit> \<spadesuit> ghost_of_RBB 
        have "\<xi> u \<in> \<Omega>" 
         and "\<Omega>,\<xi> u ||\<Turnstile> \<psi>"
         and "(\<xi> v, \<xi> u) \<in> \<Omega>RBB(X)" by (simp del: \<xi>_def, fast+)
      hence "\<Omega>,\<xi> v ||\<Turnstile> \<langle>-\<rangle> X \<psi>" by (simp only: D_ghost_of_RBB) }
    moreover
    { fix v; assume \<spadesuit>: "v \<in> W(M)"
                   and "\<Omega>,\<xi> v ||\<Turnstile> \<langle>-\<rangle> X \<psi>"
      from this obtain u where
          "\<Omega>,\<xi> u ||\<Turnstile> \<psi>" 
      and "u \<in> W(M)" 
      and "(\<xi> v, \<xi> u) \<in> \<Omega>RBB(X)" by fastsimp
      moreover with \<heartsuit> \<spadesuit> ghost_of_RBB
        have "M,u ||\<turnstile> \<psi>" 
         and "(v, u) \<in> RBB(M)(X)" by fast+
      ultimately have "M,v ||\<turnstile> \<langle>-\<rangle> X \<psi>" by fastsimp }
    ultimately show ?case by fast
  next case (DE_DDI X \<psi>)
    moreover have "(\<langle>+\<rangle> X \<psi>) \<in> \<down> \<phi> \<longrightarrow> \<psi> \<in> \<down> \<phi>"
      by (induct \<phi>, fastsimp+)
    ultimately have \<heartsuit>: "\<forall>v \<in> W(M). (M,v ||\<turnstile> \<psi>) = (\<Omega>,\<xi> v ||\<Turnstile> \<psi>)"
      by fast
    { fix v; assume \<spadesuit>: "v \<in> W(M)"
                   and "M,v ||\<turnstile> \<langle>+\<rangle> X \<psi>"
      from this obtain u where
          "M,u ||\<turnstile> \<psi>" 
      and "u \<in> W(M)" 
      and "(v,u) \<in> RBBI(M)(X)" by fastsimp
      with \<heartsuit> \<spadesuit> ghost_of_RBBI
        have "\<xi> u \<in> \<Omega>" 
         and "\<Omega>,\<xi> u ||\<Turnstile> \<psi>"
         and "(\<xi> v, \<xi> u) \<in> \<Omega>RBBI(X)" by (simp del: \<xi>_def, fast+)
      hence "\<Omega>,\<xi> v ||\<Turnstile> \<langle>+\<rangle> X \<psi>" by (simp only: D_ghost_of_RBBI) }
    moreover
    { fix v; assume \<spadesuit>: "v \<in> W(M)"
                   and "\<Omega>,\<xi> v ||\<Turnstile> \<langle>+\<rangle> X \<psi>"
      from this obtain u where
          "\<Omega>,\<xi> u ||\<Turnstile> \<psi>" 
      and "u \<in> W(M)" 
      and "(\<xi> v, \<xi> u) \<in> \<Omega>RBBI(X)" by fastsimp
      moreover with \<heartsuit> \<spadesuit> ghost_of_RBBI
        have "M,u ||\<turnstile> \<psi>" 
         and "(v, u) \<in> RBBI(M)(X)" by fast+
      ultimately have "M,v ||\<turnstile> \<langle>+\<rangle> X \<psi>" by fastsimp }
    ultimately show ?case by fast
qed

lemma (in translate_EviL) EviL_translation_lemma:
shows "\<exists> \<Omega> a A. (pretty_finite \<Omega>) \<and> (\<Omega>,(a,A) ||\<Turnstile> \<phi>)"
proof -
  have "\<phi> \<in> \<down>\<phi>" 