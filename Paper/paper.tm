<TeXmacs|1.0.7.4>

<style|acmconf>

<\body>
  <doc-data|<doc-title|Epistemic Logics as Logics of
  Argument>|<doc-author-data|<author-name|Matthew P. Wampler-Doty>>>

  <\abstract>
    In <cite|van_benthem_reflectionsepistemic_1991>, Johan van Benthem
    proposed a research program for logic of <with|font-shape|italic|explicit
    knowledge>. \ Two efforts have since emerged with proposals for logic of
    explicit knowledge: the <with|font-shape|italic|Dynamics of Awareness>
    <cite|van_benthem_inference_2009> and
    <with|font-shape|italic|Justification Logic>
    <cite|artemov_introducing_2005>. \ The purpose of this paper is to
    propose novel, argument based semantics for various modal logics related
    to these previous efforts, for use in reasoning about knowledge bases.
    \ We conclude with an application to naturalized epistemology. \ The
    results in this paper are based on previous work carried out in (FIXME
    citation to self).
  </abstract>

  <section|Introduction<label|intro>>

  The modern tradition in epistemic logic is to assume knowledge modalities
  conform to the <math|S5> axiom schema. \ As noted in
  <cite|halpern_set-theoretic_1999|rubinstein_modeling_1998>, the semantics
  of <math|S5> knowledge correspond exactly to partitioning a collection of
  situations into <with|font-shape|italic|information sets>, which is the
  traditional approach in game theory and decision theory. \ While it is not
  commonly acknowledged in epistemic logic, economists and philosophers
  accept that traditional decision theory is externalist and behaviourist in
  nature<\footnote>
    An early essay by Amartya Sen on the philosophical foundations of
    traditional decision theory makes the behaviorist reading of decision
    theory clear <cite|sen_behaviour_1973>. \ Kaushik Basu also discusses the
    behaviorist nature of decision theory
    <cite-detail|basu_revealed_1980|pgs. 53--54>. \ Finally, Donald Davidson
    appeals to decision theory to motivate an externalist epistemology in
    <cite|davidson_could_1995>.
  </footnote>.

  \;

  In <cite|van_benthem_reflectionsepistemic_1991>, Johan van Benthem proposed
  a research program to find logics for explicit knowledge, providing the
  first suggestion of an internalist perspective on epistemic logic.
  \ Subsequently, Sergei Artemov and Elena Nogina proposed a logic of
  explicit justification, which has come to be known as
  <with|font-shape|italic|Justification Logic> (JL)
  <cite|artemov_introducing_2005>, based on Artemov's
  <with|font-shape|italic|Logic of Proofs> <cite|artemov_logic_1994>. \ While
  the original semantics of JL was interpretability into Peano Arithmetic,
  Melvin Fitting proposed Kripke semantics for JL in
  <cite|fitting_logic_2005>. \ Recently, Fernando Velázquez-Quesada and Johan
  van Benthem have developed a simpler framework for explicit epistemics in
  <cite|van_benthem_inference_2009>, entitled the
  <with|font-shape|italic|Dynamics of Awareness>. \ This work was based on
  Joseph Halpern and Ronald Fagin's original
  <with|font-shape|italic|Awareness Logic> <cite|fagin_belief_1987>.

  \;

  In this essay we repurpose various externalist logics to take on an
  internalist reading. \ The concept of a <with|font-shape|italic|knowledge
  base>, from which beliefs may be implicitly deduced, will play a crucial
  role in our discussion. \ We propose this as an avenue for representing
  foundationalist perspectives on epistemology in epistemic logic. \ Our
  philosophical motivation is taken from two sources. \ The first is Vincent
  Hendricks in <cite|hendricks_mainstream_2006>, where he characterizes the
  principal of <em|logical omniscience> for implicit knowledge in epistemic
  logic<\footnote>
    We have modified Hendricks' notation here slightly to match our own.
  </footnote>:

  <\quote-env>
    <em|Whenever an agent <math|\<Xi\>> knows all of the formulae in
    <math|<with|math-font|cal|A>>, and <math|\<phi\>> follows logically from
    <math|<with|math-font|cal|A>>, then <math|\<Xi\>> [implicitly] knows
    <math|\<phi\>>.>
  </quote-env>

  We will design our semantics such that ``<math|\<box\>\<phi\>>'' may be
  equated with ``<math|\<phi\>> follows logically from a knowledge base
  <math|<with|math-font|cal|A>>,'' which is sometimes written as
  <math|\<phi\>\<in\>Cn(<with|math-font|cal|A>)> in the artificial
  intelligence literature. \ Our second inspiration comes from what Hilary
  Kornblith calls the <with|font-shape|italic|the arguments on paper thesis>
  <cite|kornblith_beyond_1980>, which he feels characterizes apsychological,
  internalist theories of knowledge:

  <\quote-env>
    Let us suppose that, for any person, it is possible, at least in
    principle, to list all of the propositions that person believes. \ The
    arguments-on-paper thesis is just the view that a person has a justified
    belief that a particular proposition is true just in case that
    proposition appears on the list of propositions that person believes, and
    either it requires no argument, or a <em|good argument> can be given for
    it which takes as premises certain other propositions on the list.
  </quote-env>

  Kornblith asserts that foundationalism and coherentism vie for accounts of
  a ``good argument'' in the above thesis. \ He provides an extensive
  bibliography citing proposals for this principle by a number of 20th
  century epistemologists, including figures such as A.J. Ayer and C.I.
  Lewis. \ The rest of Kornblith's paper is devoted to attacking this view
  and proposing a form of naturalized epistemology; we will not address this
  debate here, however.

  \;

  We adopt a arguments-on-paper-thesis perspective on epistemic logic in this
  paper. \ We consider a <with|font-shape|italic|good argument> to be a
  logical derivation from propositions present in a knowledge base. \ In this
  fashion, our \ \ Special attention will be given to
  <with|font-shape|italic|sound derivations>, which will be thought of as a
  form of knowledge. \ In Awareness Logic, we will interpret awareness of a
  formula as membership in a knowledge base. \ We prove completeness for
  basic awareness logic and a hybrid logic extension. \ Logics of multiple
  knowledge bases are also presented: a simplified form of Justification
  Logic, a logic with neighborhood semantics, an a logic with modalities for
  quantifying over knowledge bases. \ We conclude with an application to
  naturalized epistemology found in the psychological literature.

  <section|Basic Explicit Logics of Knowledge Bases>

  <subsection|Awareness Logic<label|awarenesslogic>>

  In this section, we give the explicit semantics to basic awareness logic,
  originally presented in <cite|fagin_belief_1987>, with an additional axiom.
  \ One difference in our presentation is the inclusion of a novel letter and
  a superficial change in notation. \ This work is inspired by the
  developments in van Benthem and Velázquez-Quesada
  <cite|van_benthem_inference_2009>.

  <\definition>
    Let <math|\<Phi\>> be a set of letters and define the language
    <math|<with|math-font|cal|L><rsub|A>(\<Phi\>)> as:

    <\equation*>
      \<phi\> <space|1spc>: :=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>\<circlearrowleft\><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<box\>\<phi\><space|1spc>\|<space|1spc>A:\<phi\><space|1spc>
    </equation*>
  </definition>

  We define the other connectives and modal operators as usual for classical
  modal logics.

  <\definition>
    <label|awarenessmodels>An <strong|awareness model>
    <math|\<bbb-M\>=\<langle\>W,V,R,<with|math-font|cal|A>\<rangle\>> is a
    Kripke model with a valuation <math|V:\<Phi\>\<cup\>{\<circlearrowleft\>}\<rightarrow\>2<rsup|W>>
    and an awareness function <math|<with|math-font|cal|A>:W\<rightarrow\>2<rsup|<with|math-font|cal|L><rsub|A>(\<Phi\>)>>.
    \ We will usually denote <math|<with|math-font|cal|A>(w)> as
    <math|<with|math-font|cal|A><rsub|w>>.

    \;

    Define the semantic entailment relation <math|\<vDash\>> where atomic
    propositions, logical connectives and modality are interpreted as usual.
    \ We employ the following novel definition:

    <\eqnarray*>
      <tformat|<table|<row|<cell|\<bbb-M\>,w\<vDash\>A:
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|\<phi\>\<in\><with|math-font|cal|A<rsub|w>>>>>>
    </eqnarray*>
  </definition>

  The following definition distinguishes us from previously investigations of
  awareness logic:

  <\definition>
    Define the ``<with|font-series|bold|theory of a model> <math|\<bbb-M\>>''
    as:

    <\equation*>
      Th(\<bbb-M\>)\<assign\>{\<phi\><space|1spc>\|<space|1spc>\<bbb-M\>,v\<vDash\>\<phi\><with|mode|text|
      for all >v\<in\>W}
    </equation*>

    We define the following properties that a model <math|\<bbb-M\>> may
    posses:

    <\description-dash>
      <item*|CSQ><math|\<bbb-M\>,w\<vDash\>\<box\>\<phi\><with|mode|text| iff
      >Th(\<bbb-M\>)\<cup\><with|math-font|cal|A><rsub|w>\<vdash\>\<phi\>>

      <item*|SND><math|\<bbb-M\>,w\<vDash\>\<circlearrowleft\><with|mode|text|
      iff >\<bbb-M\>,w\<vDash\>\<phi\>> for all
      <math|\<phi\>\<in\><with|math-font|cal|A><rsub|w>>
    </description-dash>

    Here <math|\<vdash\>> is any logical consequence relation which is sound
    for <math|\<vDash\>>, making true <with|font-series|bold|modus ponens>
    and <with|font-series|bold|reflection> (ie,
    <math|\<Gamma\>\<vdash\>\<phi\>> if <math|\<phi\>\<in\>\<Gamma\>>)
  </definition>

  Neither <with|font-series|bold|CSQ> nor <with|font-series|bold|SND>
  correspond to simple modally definable properties.

  \;

  Intuitively, the <with|font-series|bold|CSQ> asserts that an agent believes
  a formula <math|\<phi\>> if and only if it follows logically from their
  knowledge base and their background knowledge, represented by
  <math|Th(\<bbb-M\>)>. \ <with|font-series|bold|CSQ> is Vincent Hendrik's
  principle of logical omniscience mentioned in Ÿ<reference|intro>.

  \;

  <with|font-series|bold|SND> asserts that
  <with|mode|math|\<circlearrowleft\>> corresponds to the agent's knowledge
  base being sound. A sound knowledge base will only render true conclusions
  when used in deductions. \ If one considers ``the existance of a sound
  deduction'' sufficient for a kind of knowledge, then
  <with|mode|math|\<circlearrowleft\>> is suitable for investigating this
  notion of epistemology. \ That is, if <math|\<bbb-M\>,w\<vDash\>\<circlearrowleft\>\<wedge\>\<box\>\<phi\>>,
  then we may naturally say that the agent (implicitly) <em|knows>
  <math|\<phi\>> on the basis of <math|<with|math-font|cal|A><rsub|w>>,
  rather than merely <em|believing> <math|\<phi\>> on the basis of
  <math|<with|math-font|cal|A><rsub|w>>.

  \;

  The logic of models making true <with|font-series|bold|CSQ> and
  <with|font-series|bold|SND> is provided in Table <reference|logic1>.

  <big-table|<tabular|<tformat|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>\<box\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<box\>\<phi\>\<rightarrow\>\<box\>\<psi\>>>>|<row|<cell|<math|\<vdash\>A:\<phi\>\<rightarrow\>\<box\>\<phi\>>>>|<row|<cell|<math|\<vdash\>\<circlearrowleft\>\<rightarrow\>\<box\>\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|<space|6spc>>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>|\<vdash\>\<box\>\<phi\>>>>>>>>>>>>>>|<label|logic1>Awareness
  Logic for <with|font-series|bold|CSQ> and <with|font-series|bold|SND>>

  <\theorem>
    <label|completeness1>Assuming an infinite store of proposition letters
    <math|\<Phi\>>, the awareness logic presented is sound and weakly
    complete for awareness models making true <with|font-series|bold|CSQ> and
    <with|font-series|bold|SND>.
  </theorem>

  <\proof>
    Soundness is straightforward, so we will only address completeness.
    \ Assume <math|\<nvdash\>\<psi\>>. \ Consider the finite canonical model
    <math|\<bbb-M\>=\<langle\>W,V,R,<with|math-font|cal|A>\<rangle\>> formed
    of maximally consistent sets of subformulae of <math|\<phi\>> (closed
    under single negations<\footnote>
      A discussion of this property may be found in
      <cite-detail|blackburn_modal_2001|pg. 243>.
    </footnote>), as per the finitary modal completeness proofs found in
    <cite-detail|blackburn_modal_2001|chapter 4.8> and
    <cite-detail|boolos_logic_1995|chapter 5>. \ Typical presentations do not
    include awareness, however it is defined intuitively in this case:

    <\equation*>
      \<phi\>\<in\><with|math-font|cal|A><rsub|w>\<Longleftrightarrow\>A:\<phi\>\<in\>w
    </equation*>

    Since <math|\<psi\>> is a subformula of itself, we have
    <math|\<bbb-M\>,w\<nvDash\>\<psi\>> for some world <math|w> by a finitary
    <em|Lindenbaum Lemma> and <em|Truth Theorem>. \ Moreover, it is
    straightforward to verify that <math|\<bbb-M\>> makes true the following
    properties:

    <\enumerate-numeric>
      <item><math|W> and <math|<with|math-font|cal|A><rsub|v>> are finite,
      and <math|\<psi\>\<in\><with|math-font|cal|A><rsub|v>> only if
      <math|\<psi\>> is a (possibly negated) subformula of <math|\<phi\>>

      <item>if <math|\<bbb-M\>,v\<vDash\>A:\<psi\>> then
      <math|\<bbb-M\>,v\<vDash\>\<box\>\<psi\>>

      <item>if <math|\<bbb-M\>,v\<vDash\>\<circlearrowleft\>> then <math|v R
      v>
    </enumerate-numeric>

    \;

    We next produce a bisimular<\footnote>
      The notion of bisimulation is discussed at length in
      <cite-detail|blackburn_modal_2001|chapter 2.2>. \ We note that the
      basic definition and all of the usual theorems (modal equivalence,
      Henessy Milner, etc.) may be generalized to awareness models in a
      straightforward fashion.\ 
    </footnote> model <math|\<bbb-M\><rprime|'>> which makes true (1), (2)
    and a stronger from of (3):

    \;

    <htab|5mm><tabular|<tformat|<table|<row|<cell|<with|font-series|bold|3<math|<rprime|'>>.>>|<cell|<math|\<bbb-M\><rprime|'>,v\<vDash\>\<circlearrowleft\>>
    iff <math|v R v>>>>>><htab|5mm>

    \;

    To this end define <math|\<bbb-M\><rprime|'>\<assign\>\<langle\>W<rprime|'>,V<rprime|'>,R<rprime|'>,<with|math-font|cal|A><rprime|'>\<rangle\>>
    such that<\footnote>
      Throughout this article, we use <math|l> and <math|r> to denote the two
      canonical injections associated with the coproduct <math|W\<uplus\>W>.
      We will use <math|v<rsub|l>> and <math|v<rsub|r>> as the shorthand for
      <math|l(v)> and <math|r(v)> respectively.
    </footnote>:<htab|5mm>

    <\itemize-dot>
      <item><with|mode|math|W<rprime|'>\<assign\>W\<uplus\>W>

      <item><math|V<rprime|'>(p)\<assign\>{v<rsub|l>,v<rsub|r><space|1spc>\|<space|1spc>v\<in\>V(p)}>

      <item><math|R<rprime|'> \<assign\> {(v<rsub|l>,u<rsub|r>),(v<rsub|r>,u<rsub|l>)<space|1spc>\|<space|1spc>v
      R u}\<cup\>{(v<rsub|l>,v<rsub|l>),(v<rsub|r>,v<rsub|r>)<space|1spc>\|<space|1spc>\<bbb-M\>,v\<vDash\>\<circlearrowleft\>}>

      <item><math|<with|math-font|cal|A><rprime|'>(v<rsub|l>)\<assign\><with|math-font|cal|A><rprime|'>(v<rsub|r>)\<assign\><with|math-font|cal|A>(v)><math|>
    </itemize-dot>

    \;

    It is straightforward to verify that <math|\<bbb-M\><rprime|'>> makes
    true the desired properties. \ Let <math|Z\<assign\>{(v,v<rsub|l>),(v,v<rsub|r>)<space|1spc>\|<space|1spc>v\<in\>W}>;
    \ then <math|Z> is a bisimulation between <math|\<bbb-M\>> and
    <math|\<bbb-M\><rprime|'>>. \ Therefore we know there is some
    <math|w\<in\>W> such that <math|\<bbb-M\><rprime|'>,w<rsub|l>\<nvDash\>\<psi\>>
    and <math|\<bbb-M\><rprime|'>,w<rsub|r>\<nvDash\>\<psi\>>.

    \;

    Finally we construct a model <math|\<bbb-M\><rprime|''>> which agrees
    with <math|\<bbb-M\><rprime|'>> for all subformulae of <math|\<psi\>>,
    which makes true <with|font-series|bold|CSQ> and
    <with|font-series|bold|SND>. \ Let <math|\<Lambda\>> be the set of
    proposition letters occuring in <math|\<psi\>>. \ We will make use
    members of <math|\<Phi\>\<backslash\>\<Lambda\>> as <em|nominals>, as per
    the tradition in hybrid logic. \ This is possible since both
    <math|W<rprime|'>> and <math|\<Lambda\>> are finite and <math|\<Phi\>> is
    infinite by hypothesis. \ Let <math|\<iota\>:W\<uplus\>W\<hookrightarrow\>\<Phi\>\<backslash\>\<Lambda\>>
    be an injection assigning a fresh nominal associated with each world in
    <math|\<bbb-M\><rprime|'>>. \ Now define
    <math|\<bbb-M\><rprime|''>\<assign\>\<langle\>W<rprime|''>,V<rprime|''>,R<rprime|''>,<with|math-font|cal|A><rprime|''>\<rangle\>>,
    where:

    \;

    <\with|par-mode|center>
      <tabular|<tformat|<table|<row|<cell|<math|\<bullet\>>>|<cell|<math|W<rprime|''>\<assign\>W<rprime|'>>>|<cell|>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-display|true|V<rprime|''>(p)\<assign\><choice|<tformat|<table|<row|<cell|V<rprime|'>(p)>|<cell|p\<in\>\<Lambda\>>>|<row|<cell|{v}>|<cell|p=\<iota\>(v)>>|<row|<cell|\<varnothing\>>|<cell|o/w>>>>>>>>>|<row|<cell|<math|\<bullet\>>>|<cell|<math|R<rprime|''>\<assign\>R<rprime|'>>>|<cell|<space|3spc>>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|A><rprime|''><rsub|v>\<assign\>{\<phi\><space|1spc>\|\<phi\>\<in\><with|math-font|cal|A><rprime|'><rsub|v>}
      \<cup\>{\<neg\>\<iota\>(u)<space|1spc>\|<space|1spc>\<neg\>v
      R<rprime|'> u}>>>>>>
    </with>

    \;

    By induction we have that for every subformula <math|\<phi\>> of
    <math|\<psi\>> that <math|\<bbb-M\><rprime|'>,v\<vDash\>\<phi\>> if and
    only if <math|\<bbb-M\><rprime|''>,v\<vDash\>\<phi\>>, hence
    <math|\<bbb-M\><rprime|''>,w<rsub|l>\<nvDash\>\<psi\>>.

    \;

    All that is left to show is that <math|\<bbb-M\><rprime|''>> makes true
    <with|font-series|bold|CSQ> and <with|font-series|bold|SND>.
    \ <math|\<bbb-M\><rprime|''>> has three further properties:

    <\enumerate-roman>
      <item><math|<with|math-font|cal|A><rprime|''><rsub|v>> is finite for
      all worlds <math|v>

      <item> <math|v R<rprime|'> u> if and only if
      <math|\<bbb-M\><rprime|''>,u\<vDash\><big|wedge><with|math-font|cal|A><rprime|''>(v)>

      <item>The logic presented in Table <reference|logic1> is sound for
      <math|\<bbb-M\><rprime|''>>
    </enumerate-roman>

    From (ii) and the fact that <math|\<bbb-M\><rprime|'>> makes true
    (3<math|<rprime|'>>), we have <with|font-series|bold|SND> for
    <math|\<bbb-M\><rprime|''>>.

    \;

    All that is left is to demonstrate <with|font-series|bold|CSQ> for some
    sound logic. \ We will use the logic in Table <reference|logic1> itself.
    \ From (i), (ii), (iii), and the <with|font-shape|italic|deduction
    theorem> for modal logic, we have the following line of reasoning:

    <\align*>
      <tformat|<table|<row|<cell|Th(\<bbb-M\><rprime|''>)\<cup\><with|math-font|cal|A><rprime|''><rsub|v>\<vdash\>\<phi\>>|<cell|\<Longleftrightarrow\>Th(\<bbb-M\><rprime|''>)\<vdash\><big|wedge><with|math-font|cal|A><rprime|''><rsub|v>\<rightarrow\>\<phi\>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><big|wedge><with|math-font|cal|A><rprime|''><rsub|v>\<rightarrow\>\<phi\>\<in\>Th(\<bbb-M\><rprime|''>)>>|<row|<cell|>|<cell|\<Longleftrightarrow\>\<bbb-M\><rprime|''>,u\<vDash\><big|wedge><with|math-font|cal|A><rprime|''><rsub|v>\<rightarrow\>\<phi\><with|mode|text|<with|mode|text|
      for all ><math|u\<in\>W<rprime|''>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<with|mode|text|
      for all ><math|u\<in\>W<rprime|''>>, if
      >\<bbb-M\><rprime|''>,u\<vDash\><with|math-font|cal|A><rprime|''><rsub|v><with|mode|text|
      then >\<bbb-M\><rprime|''>,u\<vDash\>\<phi\>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<with|mode|text|
      for all ><math|u\<in\>W<rprime|''>>, if >v R <rprime|'>u
      <with|mode|text| then >\<bbb-M\><rprime|''>,u\<vDash\>\<phi\>>>|<row|<cell|>|<cell|\<Longleftrightarrow\>\<bbb-M\><rprime|''>,v\<models\>\<box\>\<phi\>>>>>
    </align*>
  </proof>

  <subsection|Hybrid Awareness Logic>

  The method of the above completeness proof makes implicit use of concepts
  from hybrid logic<\footnote>
    Hybrid logic was first presented in <cite|prior_revised_1969> and later
    formally developed in <cite|bull_approach_1970>.
  </footnote>. \ In this section we adapt hybrid logic and show that it is a
  complete for reasoning about knowledge bases. \ We note that because of the
  increased expressive power of hybrid logic, our completeness theorem is
  simpler.

  <\definition>
    Let <math|\<Phi\>> be a set of letters and <math|\<Psi\>> a set of
    nominals, and define the language <math|<with|math-font|cal|L><rsub|H>(\<Phi\>,\<Psi\>)>
    as:

    <\equation*>
      \<phi\> <space|1spc>: :=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>i\<in\>\<Psi\><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<box\>\<phi\><space|1spc>\|<space|1spc>A:\<phi\><space|1spc>\|<space|1spc>\<forall\>\<phi\>
    </equation*>
  </definition>

  Our approach in hybrid logic is to employ a universal modality along with
  nominals. \ This framework presents a logic where the agent may reason
  about various labeled scenarios. \ Scenarios may be multiply labeled or not
  labeled at all. \ From these intuitions we have the following definition:

  <\definition>
    <label|hybridsemantics>Let a <with|font-series|bold|hybrid model>
    <math|\<bbb-M\>=\<langle\>W,V,R,<with|math-font|cal|A>,\<ell\>\<rangle\>>
    be an awareness model as in Definition <reference|awarenessmodels>, along
    with a partial labeling function <math|\<ell\>:\<Psi\>\<nrightarrow\>W>

    \;

    The semantics for <math|\<vDash\>> are the same as in Definition
    <reference|awarenessmodels>, only we have

    <\eqnarray*>
      <tformat|<table|<row|<cell|\<bbb-M\>,w\<vDash\>\<forall\>\<phi\>>|<cell|<with|mode|text|iff>>|<cell|\<forall\>v\<in\>W.\<bbb-M\>,v\<vDash\>\<phi\>>>|<row|<cell|\<bbb-M\>,w\<vDash\>i>|<cell|<with|mode|text|iff>>|<cell|\<ell\>(i)=w>>>>
    </eqnarray*>
  </definition>

  The other connectives and operators are defined as usual, although we
  employ a few special shorthands:

  <\definition>
    We employ the following special abbreviations:

    <\eqnarray>
      <tformat|<table|<row|<cell|<with|mode|text|<with|font-shape|right|@>><rsub|i>\<phi\>\<assign\>\<forall\>(i\<rightarrow\>\<phi\>)<space|2spc>>|<cell|\<exists\>\<phi\>\<assign\>\<neg\>\<forall\>\<neg\>\<phi\><space|3spc>>|<cell|\<circlearrowleft\><rsub|i>\<assign\>\<diamondsuit\>i>>>>
    </eqnarray>
  </definition>

  This gives rise to a validity reflecting one of the axioms we saw in
  Ÿ<reference|awarenesslogic>:

  <\equation*>
    \<vDash\>\<circlearrowleft\><rsub|i>\<rightarrow\>\<box\>\<phi\>\<rightarrow\><with|mode|text|<with|font-shape|right|@>><rsub|i>\<phi\>
  </equation*>

  This can be read as ``If the agent's knowledge base is sound at world
  <math|i>, then if they can deduce something from their knowledge base, what
  they deduce must be true at world <math|i>.'' \ In a way, this may be
  considered as <em|relativising> knowledge particular named situations.

  \;

  The semantics in Definition <reference|hybridsemantics> obviates the
  <with|font-series|bold|SND> principle we previously presented, since there
  is no explicit <with|mode|math|\<circlearrowleft\>> symbol in this setting.
  <with|font-series|bold|CSQ> still makes sense without modification,
  however. \ The following gives a logic for hybrid models making true
  <with|font-series|bold|CSQ>:

  <big-table|<tabular|<tformat|<cwith|8|8|1|2|cell-row-span|1>|<cwith|8|8|1|2|cell-col-span|2>|<cwith|8|8|1|1|cell-halign|c>|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|<math|\<vdash\>\<forall\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<forall\>\<phi\>\<rightarrow\>\<forall\>\<psi\>>>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>|<cell|<math|\<vdash\>\<forall\>\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|<math|\<vdash\>\<forall\>\<phi\>\<rightarrow\>\<forall\>\<forall\>\<phi\>>>>|<row|<cell|<math|\<vdash\>\<box\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<box\>\<phi\>\<rightarrow\>\<box\>\<psi\>>>|<cell|<math|\<vdash\>\<exists\>\<phi\>\<rightarrow\>\<forall\>\<exists\>\<phi\>>>>|<row|<cell|<math|\<vdash\>A:\<phi\>\<rightarrow\>\<box\>\<phi\>>>|<cell|<math|\<vdash\>\<forall\>\<phi\>\<rightarrow\>\<box\>\<phi\>>>>|<row|<cell|>|<cell|<math|\<vdash\>i\<rightarrow\>\<phi\>\<rightarrow\><with|mode|text|<with|font-shape|right|@>><rsub|i>\<phi\>>>>|<row|<cell|>|<cell|>>|<row|<cell|<tabular|<tformat|<cwith|1|1|4|4|cell-halign|c>|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|<space|6spc><with|math-display|true|<math|<frac|\<vdash\>\<phi\>|\<vdash\>\<box\>\<phi\>>>>>|<cell|<space|6spc>>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>|\<vdash\>\<forall\>\<phi\>>>>>>>>>>|<cell|>>>>>|<label|logic2>Hybrid
  Awareness Logic for <with|font-series|bold|CSQ>>

  <\theorem>
    <label|completeness2>Assuming an infinite store of nominals
    <math|\<Psi\>>, the hybrid awareness logic presented is sound and weakly
    complete for all hybrid models making true <with|font-series|bold|CSQ>.
  </theorem>

  <\proof>
    As before, soundness is trivial. \ Completeness is based on a
    modification of techniques found in <cite-detail|boolos_logic_1995|chapter
    5>. \ Assume that <math|\<nvdash\>\<psi\>> and let
    <math|\<Sigma\><rsub|0>> be the set of subformulae of <math|\<psi\>>, and
    let <math|\<Upsilon\>> be the set of nominals occuring in <math|\<psi\>>.
    \ Define:

    <\align*>
      <tformat|<table|<row|<cell|\<Sigma\><rsub|1>>|<cell|\<assign\>\<Sigma\><rsub|0>\<cup\>{\<forall\>\<phi\><space|1spc>\|<space|1spc>\<box\>\<phi\>\<in\>\<Sigma\><rsub|0>}>>|<row|<cell|\<Sigma\><rsub|2>>|<cell|\<assign\>\<Sigma\><rsub|1>\<cup\>{<with|mode|text|@><rsub|i>\<phi\><space|1spc>,i\<rightarrow\>\<phi\>\|<space|1spc>\<phi\>\<in\>\<Sigma\><rsub|1><space|1spc>&<space|1spc>i\<in\>\<Upsilon\>}>>|<row|<cell|\<Sigma\><rsub|3>>|<cell|\<assign\>\<Sigma\><rsub|2>\<cup\>{\<neg\>\<phi\><space|1spc>\|<space|1spc>\<phi\>\<in\>\<Sigma\><rsub|2>}>>>>
    </align*>

    It is easy to see that <math|\<Sigma\><rsub|3>> is finite and closed
    under subformulae and single negations. Let
    <with|mode|math|\<bbb-M\>=\<langle\>W,V,R<rsub|\<box\>>,\<sim\><rsub|\<forall\>>,<with|math-font|cal|A>\<rangle\>>
    be the finite cannonical model formed of maximally consistent subsets of
    <math|\<Sigma\><rsub|3>>, where everything is defined as usual, except
    <math|\<sim\><rsub|\<forall\>>>, which obeys the following specification:

    <\align*>
      <tformat|<table|<row|<cell|w \<sim\><rsub|\<forall\>>v>|<cell|\<Longleftrightarrow\>((\<forall\>\<phi\>)\<in\>w
      \<Longleftrightarrow\>(\<forall\>\<phi\>)\<in\>v)>>>>
    </align*>

    This model makes true the following properties:

    <\enumerate-roman>
      <item><math|\<sim\><rsub|\<forall\>>> is an equivalence relation

      <item><math|R<rsub|\<box\>>\<subseteq\>\<sim\><rsub|\<forall\>>>

      <item>In each equivalence class specified by
      <math|\<sim\><rsub|\<forall\>>>, there is at most one world making true
      <math|i> for all <math|i\<in\>\<Upsilon\>>
    </enumerate-roman>

    As in our previous construction we have that there is some world <math|w>
    where <math|\<bbb-M\>,w\<nvDash\>\<psi\>>. \ Let
    <math|\<bbb-M\><rsup|1>=\<langle\>W<rprime|'>,V<rprime|'>,R<rsub|\<box\>><rprime|'>,\<sim\><rsub|\<forall\>><rprime|'>,<with|math-font|cal|A><rprime|'>\<rangle\>>
    be the submodel generated by <math|{w}>; we have that
    <math|\<bbb-M\><rprime|'>,w\<nvDash\>\<psi\>> (see
    <cite-detail|blackburn_modal_2001|chapter 2.1> for details on generated
    submodels). \ In this model <math|\<forall\>> is a universal modality and
    either <math|<left|llbracket>i<right|rrbracket><rsup|\<bbb-M\><rprime|'>>=\<varnothing\>>
    or <math|<left|llbracket>i<right|rrbracket><rsup|\<bbb-M\><rprime|'>>={v}><\footnote>
      As per the usual convention, here <math|<left|llbracket>\<phi\><right|rrbracket><rsup|\<bbb-M\>>>
      denotes <math|{w\<in\>W<space|1spc>\|<space|1spc>\<bbb-M\>,w\<vDash\>\<phi\>}>.
      \ We will drop <math|\<bbb-M\>> where it is unambiguous.
    </footnote>. Since <math|>the store <math|\<Psi\>> of nominals is
    infinite and <math|\<Upsilon\>> is finite, we have that
    <math|\<Psi\>\<backslash\>\<Upsilon\>> is infinite, so there is some
    injection <math|\<iota\>:W<rprime|'>\<hookrightarrow\>\<Psi\>\<backslash\>\<Upsilon\>>
    which assigns a fresh nominal to every world. \ Let
    <math|\<bbb-M\><rprime|''>=\<langle\>W<rprime|''>,V<rprime|''>,R<rprime|''>,<with|math-font|cal|A><rprime|''>,\<ell\>\<rangle\>>,
    where:

    <\with|par-mode|center>
      <tabular|<tformat|<cwith|3|3|1|1|cell-row-span|1>|<cwith|3|3|1|1|cell-col-span|5>|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|<math|\<bullet\>>>|<cell|<math|W<rprime|''>\<assign\>W<rprime|'>>>|<cell|>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-display|true|V<rprime|''>(p)\<assign\>V<rprime|'>(p)>>>>|<row|<cell|<math|\<bullet\>>>|<cell|<math|R<rprime|''>\<assign\>R<rprime|'><rsub|\<box\>>>>|<cell|<space|3spc>>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|A><rprime|''>(v)\<assign\>{\<phi\><space|1spc>\|<space|1spc>\<phi\>
      \<in\><with|math-font|cal|A><rprime|'>(v)}\<cup\>{\<neg\>\<iota\>(u)<space|1spc>\|<space|1spc>\<neg\>v
      R<rprime|'> u}>>>|<row|<cell|<tabular|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-display|true|\<ell\>(i)\<assign\><choice|<tformat|<table|<row|<cell|w>|<cell|i\<in\>\<Upsilon\><space|1spc>&<space|1spc>\<bbb-M\>,w\<vDash\>i>>|<row|<cell|\<iota\><rsup|-1>(i)>|<cell|i\<in\>\<iota\>[W]>>|<row|<cell|<with|mode|text|undefined>>|<cell|<with|mode|text|o/w>>>>>>>>>>>>>>|<cell|<math|R<rprime|''>\<assign\>R<rprime|'><rsub|\<box\>>>>|<cell|>|<cell|>|<cell|>>>>>
    </with>

    The the worlds is <math|\<bbb-M\><rprime|'>> and
    <math|\<bbb-M\><rprime|''>> agree on all subformulae of <math|\<psi\>>,
    hence <math|\<bbb-M\><rprime|''>,w\<nvDash\>\<psi\>>. The same reasoning
    as in the proof of Theorem <reference|completeness1> establishes and that
    the logic in Table <reference|logic2> itself is sound for
    <math|\<bbb-M\><rprime|''>> and makes true
    <with|font-series|bold|CSQ<math|>>, establishing completeness.
  </proof>

  <section|Logics of Multiple Knowledge Bases>

  So far, we have only dealt with systems that reason over a single knowledge
  base. \ In this section, we present various logics for reasoning over
  multiple knowledge bases.

  <subsection|Simple Justification Logic>

  Justification Logic (JL) was originally developed by Artemov as the
  <with|font-shape|italic|Logic of Proofs> (LP) <cite|artemov_logic_1994>.
  \ Its original purpose was to provide a framework for reasoning about
  explicit provability in Peano Arithmetic. \ The first introduction of
  Justification Logic can be found in <cite|artemov_introducing_2005>, where
  Artemov and Nogina propose LP as a logic for reasoning about evidence. \ In
  <cite|fitting_logic_2005>, Melvin Fitting provided JL with Kripke model
  based semantics.

  \;

  The principle innovation of LP/JL is to extend awareness logic, such that
  awareness operations are now <with|font-shape|italic|proof terms>.
  \ Informally, we say that ``a proof term <math|X> witnesses proposition
  <math|\<phi\>>'', denoted ``<math|X:\<phi\>>'', whenever <math|X>
  represents a proof of <math|\<phi\>>. \ Proofs may have
  <strong|multiple-conclusions> in this system, so it is possible that
  <math|X:\<phi\>> and <math|X:\<psi\>> can be true where
  <math|\<phi\>\<neq\>\<psi\>>. \ In Fitting's Kripke semantics,
  <math|X:\<phi\>> means that <math|\<phi\>> is in awareness set
  corresponding to <math|X>. \ Proof terms are thought be operating in a
  <with|font-shape|italic|multi-conclusion> proof system, so the same proof
  term may witness many different propositions.

  \;

  The logics LP/JL include operators over proofs terms, so that new proof
  terms may be assembled. \ One operation of particular interest to us is
  <em|choice>, denoted <math|\<oplus\>>. \ The expression
  ``<math|X\<oplus\>Y:\<phi\>>'' denotes that either <math|X> or <math|Y> are
  proofs witnessing <math|\<phi\>>. \ There are other operations which
  correspond to <with|font-shape|italic|modus ponens> and
  <with|font-shape|italic|proof-theoretic reflection>, however we do not
  consider these operations here.

  \;

  In this section we consider a simplified form of JL suitable for reasoning
  over multiple knowledge bases, which we call <with|font-shape|italic|simple
  justification logic> (SJL). However, instead of thinking of terms as
  representing proofs, we use them to represent knowledge bases. This is in
  the spirit of JL as a logic of evidence: we consider each knowledge base to
  be a corpus of evidence. \ Each term ``names'' a different knowledge base
  at a particular world. \ Terms may not refer to the same knowledge base at
  different worlds, just as in how in awareness logic the agent need not be
  aware of the same formulae at different worlds. \ Finally, we will make use
  of JL's <em|choice> operator as a mechanism for forming the union of
  knowledge bases, creating new ones.

  <\definition>
    Let <math|\<Pi\>> be a set of primitive terms. \ Define
    <math|\<tau\>(\<Pi\>)> with the following grammar:

    <\equation*>
      X<space|1spc>: :=<space|1spc>t\<in\>\<Pi\><space|1spc>\|<space|1spc>X\<oplus\>Y
    </equation*>

    \;

    Let <math|\<Phi\>> be a set of letters and <math|\<Pi\>> a set of
    primitive terms, and define the language
    <math|<with|math-font|cal|L><rsub|SJL>(\<Phi\>,\<Pi\>)> as:

    <\equation*>
      \<phi\> <space|1spc>: :=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>\<circlearrowleft\><rsub|X><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<box\><rsub|X>\<phi\><space|1spc>\|<space|1spc>X:\<phi\>
    </equation*>

    where <math|X\<in\>\<tau\>(\<Pi\>)>
  </definition>

  <\definition>
    <label|justmodels>A <strong|simple justification model>
    <math|\<bbb-M\>=\<langle\>W,V,R,<with|math-font|cal|A>\<rangle\>> is a
    Kripke model with a valuation <with|mode|math|V:\<Phi\>\<cup\>{\<circlearrowleft\><rsub|X><space|1spc>\|<space|1spc>X\<in\>\<tau\>(\<Pi\>)}\<rightarrow\>2<rsup|W>>,
    an indexed relation <math|R:\<tau\>(\<Pi\>)\<rightarrow\>2<rsup|W\<times\>W>>,
    along with a modified awareness function
    <math|<with|math-font|cal|A>:W\<times\>\<tau\>(\<Pi\>)\<rightarrow\>2<rsup|<with|math-font|cal|L><rsub|SJL>(\<Phi\>,\<Pi\>)>>.
    \ In practice we will denote <math|<with|math-font|cal|A>(w,X)> by a
    curried shorthand, namely <math|<with|math-font|cal|A><rsub|w>(X)>.

    \;

    The semantics for <math|\<vDash\>> have the following modifications:

    <\eqnarray*>
      <tformat|<table|<row|<cell|\<bbb-M\>,w\<vDash\>\<box\><rsub|X>\<phi\>>|<cell|<with|mode|text|iff>>|<cell|<with|mode|text|for
      all <math|v\<in\>W> where <math|w R<rsub|X>v> we have
      <math|\<bbb-M\>,v\<vDash\>v>>>>|<row|<cell|\<bbb-M\>,w\<vDash\>X:
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|\<phi\>\<in\><with|math-font|cal|A><rsub|w>(X)>>>>
    </eqnarray*>
  </definition>

  <\definition>
    The following defines properties a simple justification model may make
    true:

    <\description-dash>
      <item*|JCSQ><math|\<bbb-M\>,w\<vDash\>\<box\><rsub|X>\<phi\><with|mode|text|
      iff > Th(\<bbb-M\>)\<cup\><with|math-font|cal|A><rsub|w>(X)\<vdash\>\<phi\>>

      <item*|JSND><math|\<bbb-M\>,w\<vDash\>\<circlearrowleft\><rsub|X><with|mode|text|
      iff <with|mode|math|\<bbb-M\>,w\<vDash\>\<phi\>> for all
      <math|\<phi\>\<in\><with|math-font|cal|A><rsub|w>(X)>>>

      <item*|CHOICE><math|<with|math-font|cal|A><rsub|w>(X\<oplus\>Y)=<with|math-font|cal|A><rsub|w>(X)\<cup\><with|math-font|cal|A><rsub|w>(Y)>
    </description-dash>

    as before, <math|\<vdash\>> is any sound logical consequence relation for
    <math|\<vDash\>> with <with|font-series|bold|modus ponens> and
    <with|font-series|bold|reflection>
  </definition>

  The above semantics are similar to the ones given in previous sections.
  \ <with|font-series|bold|JCSQ> is the same as <with|font-series|bold|CSQ>
  from Ÿ<reference|awarenesslogic>, only it is relativized to a knowledge
  base denoted by <math|X> at <math|w>. \ The awareness logic of knowledge
  bases is special case of simple justification logic where there is only one
  term.

  \;

  Simplified justification logic is given in Table <reference|logic5>. \ We
  assert without proof that this is a conservative extension of the awareness
  logic in Ÿ<reference|awarenesslogic>.

  \;

  <big-table|<tabular|<tformat|<cwith|11|11|1|2|cell-row-span|1>|<cwith|11|11|1|2|cell-col-span|2>|<cwith|11|11|1|1|cell-halign|c>|<cwith|14|14|1|1|cell-row-span|1>|<cwith|14|14|1|1|cell-col-span|2>|<cwith|14|14|1|1|cell-halign|c>|<cwith|16|16|1|1|cell-row-span|1>|<cwith|16|16|1|1|cell-col-span|2>|<cwith|16|16|1|1|cell-halign|c>|<cwith|7|7|1|1|cell-row-span|1>|<cwith|7|7|1|1|cell-col-span|2>|<cwith|7|7|1|1|cell-halign|c>|<cwith|9|9|1|1|cell-row-span|1>|<cwith|9|9|1|1|cell-col-span|2>|<cwith|9|9|1|1|cell-halign|c>|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>\<box\><rsub|X>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<box\><rsub|X>\<phi\>\<rightarrow\>\<box\><rsub|X>\<psi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>(X:\<phi\>)\<rightarrow\>\<box\><rsub|X>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>\<circlearrowleft\><rsub|X>\<rightarrow\>\<box\><rsub|X>\<phi\>\<rightarrow\>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>(X:\<phi\>)\<rightarrow\>(Y:\<phi\>)\<rightarrow\>X\<oplus\>Y:\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>(X\<oplus\>Y:\<phi\>)\<rightarrow\>X:\<phi\>>>|<cell|<math|\<vdash\>(X\<oplus\>Y:\<phi\>)\<rightarrow\>Y:\<phi\>>>>|<row|<cell|<math|\<vdash\>\<circlearrowleft\><rsub|X>\<rightarrow\>\<circlearrowleft\><rsub|Y>\<rightarrow\>\<circlearrowleft\><rsub|X\<oplus\>Y>>>|<cell|>>|<row|<cell|<math|\<vdash\>\<circlearrowleft\><rsub|X\<oplus\>Y>\<rightarrow\>\<circlearrowleft\><rsub|X>>>|<cell|<math|\<vdash\>\<circlearrowleft\><rsub|X\<oplus\>Y>\<rightarrow\>\<circlearrowleft\><rsub|Y>>>>|<row|<cell|<math|\<vdash\>\<box\><rsub|X>\<phi\>\<rightarrow\>\<box\><rsub|X\<oplus\>Y>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>\<box\><rsub|X\<oplus\>X>\<phi\>\<rightarrow\>\<box\><rsub|X>\<phi\>>>|<cell|<math|\<vdash\>\<box\><rsub|(X\<oplus\>X)\<oplus\>Y>\<phi\>\<rightarrow\>\<box\><rsub|X\<oplus\>Y>\<phi\>>
  >>|<row|<cell|<math|\<vdash\>\<box\><rsub|X\<oplus\>Y>\<phi\>\<rightarrow\>\<box\><rsub|Y\<oplus\>X>\<phi\>>>|<cell|<math|\<vdash\>\<box\><rsub|(X\<oplus\>Y)\<oplus\>Z>\<phi\>\<rightarrow\>\<box\><rsub|(Y\<oplus\>X)\<oplus\>Z>\<phi\>>>>|<row|<cell|<math|\<vdash\>\<box\><rsub|(X\<oplus\>Y)\<oplus\>Z>\<phi\>\<rightarrow\>\<box\><rsub|X\<oplus\>(Y\<oplus\>Z)>\<phi\>>>|<cell|>>|<row|<cell|>|<cell|>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|<space|6spc>>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>|\<vdash\>\<box\><rsub|X>\<phi\>>>>>>>>>>|<cell|>>>>>|<label|logic5>Simple
  Justification Logic>

  <\theorem>
    <label|completeness5>Assuming an infinite store of proposition letters
    <math|\<Phi\>>, SJL is sound and weakly complete for simple justification
    models making true <with|font-series|bold|JCSQ>,
    <with|font-series|bold|JSND> and <with|font-series|bold|CHOICE>
  </theorem>

  <\proof>
    As in the previous proofs, we only show completeness. \ Assume that
    <math|\<nvdash\>\<psi\>>. \ Let <math|\<Xi\>\<subseteq\>\<tau\>(\<Pi\>)>
    be all of the subterms occurring in <math|\<psi\>>; we assume that
    <math|\<Xi\>> is non-empty, since otherwise we may obtain the theorem via
    the usual completeness theorem for classical propositional logic. Let
    <math|\<Sigma\><rsub|0>> be the subformulae of <math|\<psi\>>. \ Define:\ 

    <\align*>
      <tformat|<table|<row|<cell|\<Sigma\><rsub|1>>|<cell|\<assign\>\<Sigma\><rsub|0>\<cup\>{\<box\><rsub|Y>\<phi\><space|1spc>\|<space|1spc>\<box\><rsub|X>\<phi\>\<in\>\<Sigma\><rsub|0><space|1spc>&<space|1spc>Y\<in\>\<Xi\>}>>|<row|<cell|\<Sigma\><rsub|2>>|<cell|\<assign\>\<Sigma\><rsub|1>\<cup\>{\<neg\>\<phi\><space|1spc>\|<space|1spc>\<phi\>\<in\>\<Sigma\><rsub|1>}>>>>
    </align*>

    As in the proof of Theorem <reference|completeness2>, it is simple to
    verify that <math|\<Sigma\><rsub|2>> is closed under subformulae and
    single negations. \ Let <with|mode|math|\<bbb-M\>\<assign\>\<langle\>W,V,R,<with|math-font|cal|A>\<rangle\>>
    be the finite cannonical model formed of maximally consistent subsets of
    <math|\<Sigma\><rsub|2>>, where <math|V> and
    <math|<with|math-font|cal|A>> are defined as usual, and
    <math|R:\<Xi\>\<rightarrow\>2<rsup|W\<times\>W>> is defined by:

    <\equation*>
      w R<rsub|X> v\<Longleftrightarrow\>{\<phi\><space|1spc>\|<space|1spc>\<box\><rsub|X>\<phi\>\<in\>w}\<subseteq\>v
    </equation*>

    As in previous constructions we may prove the usual Lindenbaum and Truth
    Lemmas an use them obtain a world <math|w\<in\>W> where
    <math|\<bbb-M\>,w\<nvDash\>\<psi\>>.

    \;

    Next, define an operator <math|\<twonotes\>:\<tau\>(\<Pi\>)\<rightarrow\>2<rsup|\<Pi\>>>
    where:

    <\equation*>
      \<twonotes\>(X)\<assign\>{t\<in\>\<Pi\><space|1spc>\|<space|1spc>t
      <with|mode|text| occurs in >X}
    </equation*>

    In other words, <math|\<twonotes\>(X)> is the set of atomic terms in
    <math|X>. \ As in our construction for Theorem <reference|completeness1>,
    <math|\<bbb-M\>> makes true certain properties, along with some new
    properties:

    <\enumerate-numeric>
      <item><label|fin><math|W> and <math|<with|math-font|cal|A><rsub|v>(X)>
      are finite, and <math|\<phi\>\<in\><with|math-font|cal|A><rsub|v>(X)>
      only if <math|\<phi\>\<in\>\<Sigma\><rsub|2>>

      <item>if <math|\<bbb-M\>,v\<vDash\>X:\<phi\>> then
      <math|\<bbb-M\>,v\<vDash\>\<box\><rsub|X>\<phi\>>

      <item><label|refl>if <math|\<bbb-M\>,v\<vDash\>\<circlearrowleft\><rsub|X>>
      then <math|v R<rsub|X> v>

      <item><label|sndness>For all <math|X\<oplus\>Y\<in\>\<Xi\>>,
      <math|\<bbb-M\>,v\<vDash\>\<circlearrowleft\><rsub|X\<oplus\>Y>> if and
      only if <math|\<bbb-M\>,v\<vDash\>\<circlearrowleft\><rsub|X>> and
      <math|\<bbb-M\>,v\<vDash\>\<circlearrowleft\><rsub|Y>>

      <item><label|union>For all <math|X\<oplus\>Y\<in\>\<Xi\>>,
      <with|mode|math|<math|<with|math-font|cal|A><rsub|v>(X\<oplus\>Y)=<with|math-font|cal|A><rsub|v>(X)\<cup\><with|math-font|cal|A><rsub|v>(Y)>>

      <item><label|sub>For all <math|X,Y\<in\>\<Xi\>>, if
      <with|mode|math|\<twonotes\>(X)\<subseteq\>\<twonotes\>(Y)> then
      <math|R<rsub|Y>\<subseteq\>R<rsub|X>>
    </enumerate-numeric>

    As in our previous constructions, it is necessary to refine this model
    using bisimulations to achieve properties which are not modally
    definable. \ In particular, we shall strengthen (<reference|refl>) to a
    biconditional and (<reference|sub>) to:

    <\with|par-mode|center>
      <tabular|<tformat|<cwith|1|1|2|2|cell-halign|c>|<table|<row|<cell|<with|font-series|bold|6<math|<rprime|'>>.>>|<cell|For
      all <math|X,Y\<in\>\<Xi\>>, <math|R<rsub|X\<oplus\>Y>=R<rsub|X>\<cap\>R<rsub|Y>>>>>>>
    </with>

    \;

    We first strengthen (<reference|refl>) by constructing
    <math|\<bbb-M\><rprime|'>\<assign\>\<langle\>W<rprime|'>,V<rprime|'>,R<rprime|'>,<with|math-font|cal|A><rprime|'>\<rangle\>>,
    just as in Theorem <reference|completeness1>:<htab|5mm>

    <\itemize-dot>
      <item><with|mode|math|W<rprime|'>\<assign\>W\<uplus\>W>

      <item><math|V<rprime|'>(p)\<assign\>{v<rsub|l>,v<rsub|r><space|1spc>\|<space|1spc>v\<in\>V(p)}>

      <item><math|R<rprime|'><rsub|X> \<assign\>
      {(v<rsub|l>,u<rsub|r>),(v<rsub|r>,u<rsub|l>)<space|1spc>\|<space|1spc>v
      R<rsub|X> u}\<cup\>{(v<rsub|l>,v<rsub|l>),(v<rsub|r>,v<rsub|r>)<space|1spc>\|<space|1spc>\<bbb-M\>,v\<vDash\>\<circlearrowleft\><rsub|X>}>

      <item><math|<with|math-font|cal|A><rprime|'>(v<rsub|l>,X)\<assign\><with|math-font|cal|A><rprime|'>(v<rsub|r>,X)\<assign\><with|math-font|cal|A>(v,X)><math|>
    </itemize-dot>

    The same bisimulation relation <math|Z> previously given suffices.

    \;

    We next make a strengthened the model where
    (<reference|sub><math|<rprime|'>>) holds. \ Define
    <math|\<bbb-M\><rprime|''>\<assign\>\<langle\>W<rprime|''>,V<rprime|''>,R<rprime|''>,<with|math-font|cal|A><rprime|''>\<rangle\>>
    such that<\footnote>
      Let <math|{i<rsub|X><space|1spc>\|<space|1spc>X\<in\>\<Xi\>}> be the
      family of canonical injections into the coproduct
      <math|<big|pluscup><rsub|\<Xi\>>W>. As per our previous convention, we
      use <math|v<rsub|X>> as shorthand for <math|i<rsub|X>(v)>.
    </footnote>:

    <\itemize-dot>
      <item><with|math-display|true|<with|mode|math|W<rprime|''>\<assign\><big|pluscup><rsub|\<Xi\>>W<rprime|'>>>

      <item><math|V<rprime|''>(p)\<assign\>{v<rsub|X><space|1spc>\|<space|1spc>X\<in\>\<Xi\><space|1spc>&<space|1spc>v\<in\>V<rprime|'>(p)}>

      <item><math|R<rprime|''><rsub|X> \<assign\>
      {(v<rsub|Y>,u<rsub|Z>)<space|1spc>\|<space|1spc>Y,Z\<in\>\<Xi\><space|1spc>&<space|1spc>v
      R<rprime|'><rsub|Z> u<space|1spc>&<space|1spc>\<twonotes\>(X)\<subseteq\>\<twonotes\>(Z)}>

      <item><math|<with|math-font|cal|A><rprime|''>(v<rsub|Y>,X)\<assign\><with|math-font|cal|A><rprime|'>(v,X)>
    </itemize-dot>

    Note that this construction makes use of the assumption that
    <math|\<Xi\>> is non-empty. \ Let <math|Z\<assign\>{(v,v<rsub|X>)<space|1spc>\|<space|1spc>X\<in\>\<Xi\><space|1spc>&<space|1spc>v\<in\>W<rprime|'>}>;
    it is straightforward to prove that <math|Z> is a bisimulation between
    <math|\<bbb-M\><rprime|'>> and <math|\<bbb-M\><rprime|''>>, for all
    relations corresponding to terms <math|X\<in\>\<Xi\>>. Hence
    <math|\<bbb-M\><rprime|''>,w<rsub|X>\<nvDash\>\<psi\>> for some
    <math|w<rsub|X>\<in\>W<rprime|''>>. \ In addition,
    <math|\<bbb-M\><rprime|''>> inherits (<reference|fin>) through
    (<reference|sub>) from <math|\<bbb-M\><rprime|'>>, as well as the
    converse of (<reference|refl>). \ Next observe, forall
    <math|X\<oplus\>Y\<in\>\<Xi\>>:

    <\eqnarray*>
      <tformat|<table|<row|<cell|<with|mode|text|<math|(v<rsub|V>,u<rsub|Z>)\<in\>R<rprime|''><rsub|X>\<cap\>R<rprime|''><rsub|Y>>>>|<cell|\<Longleftrightarrow\>>|<cell|\<exists\>Z\<in\>\<Xi\>.
      <with|mode|text|<math|v R<rprime|'><rsub|Z>
      u<space|1spc>&<space|1spc>\<twonotes\>(X)\<subseteq\>\<twonotes\>(Z)<space|1spc>&<space|1spc>\<twonotes\>(Y)\<subseteq\>\<twonotes\>(Z)>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\>>|<cell|\<exists\>Z\<in\>\<Xi\>.<with|mode|text|<math|v
      R<rprime|'><rsub|Z> u<space|1spc>&<space|1spc>\<twonotes\>(X)\<cup\>\<twonotes\>(Y)\<subseteq\>\<twonotes\>(Z)>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\>>|<cell|\<exists\>Z\<in\>\<Xi\>.<with|mode|text|<math|v
      R<rprime|'><rsub|Z> u<space|1spc>&<space|1spc>\<twonotes\>(X\<oplus\>Y)\<subseteq\>\<twonotes\>(Z)>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\>>|<cell|
      <with|mode|text|<math|(v<rsub|V>,u<rsub|Z>)\<in\>R<rprime|''><rsub|X\<oplus\>Y>>>>>>>
    </eqnarray*>

    We now turn to our final construction. As in previous constructions, let
    <math|\<iota\>:W<rprime|''>\<hookrightarrow\>\<Phi\>\<backslash\>\<Psi\>>
    be an injection assigning fresh nominals to worlds. \ Define
    <math|\<bbb-M\><rprime|'''>\<assign\>\<langle\>W<rprime|'''>,V<rprime|'''>,R<rprime|'''>,<with|math-font|cal|A><rprime|'''>\<rangle\>>
    just as in the final construction in the proof of Theorem
    <reference|completeness1>, except that <math|R<rprime|'''><rsub|X>> and
    <math|<with|math-font|cal|A><rsub|v><rprime|'''>(X)> are defined
    inductively as follows:\ 

    \;

    <\with|par-mode|center>
      <tabular|<tformat|<table|<row|<cell|<math|\<bullet\>>>|<cell|<math|R<rprime|'''><rsub|t>\<assign\><with|math-display|true|<choice|<tformat|<table|<row|<cell|R<rprime|''><rsub|t>>|<cell|t\<in\>\<Xi\>>>|<row|<cell|W<rprime|'''>\<times\>W<rprime|'''>>|<cell|o/w>>>>>>>>|<cell|>>|<row|<cell|<math|\<bullet\>>>|<cell|<with|mode|math|R<rprime|'''><rsub|X\<oplus\>Y>\<assign\>R<rprime|'''><rsub|X>\<cap\>R<rprime|'''><rsub|Y>>>|<cell|>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|A><rprime|'''><rsub|v>(t)\<assign\>{\<phi\><space|1spc>\|\<phi\>\<in\><with|math-font|cal|A><rprime|''><rsub|v>}
      \<cup\>{\<neg\>\<iota\>(u)<space|1spc>\|<space|1spc>\<neg\>v
      R<rprime|'''><rsub|t> u}>>|<cell|where
      <math|t\<in\>\<Pi\>>>>|<row|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|A><rprime|'''><rsub|v>(X\<oplus\>Y)\<assign\><with|math-font|cal|A><rprime|'''><rsub|v>(X)\<cup\><with|math-font|cal|A><rprime|'''><rsub|v>(Y)>>|<cell|>>>>>
    </with>

    \;

    \;

    Induction over complexity of subformulae <math|\<phi\>> of <math|\<psi\>>
    yields <math|\<bbb-M\><rprime|''>,w\<vDash\>\<phi\>\<Longleftrightarrow\>\<bbb-M\><rprime|'''>,w\<vDash\>\<phi\>>,
    so we know that there is some world <math|w\<in\>W<rprime|'''>> such that
    <math|\<bbb-M\><rprime|'''>,w\<nvDash\>\<psi\>>. \ All that is left is to
    illustrate that <math|\<bbb-M\><rprime|'''>> has the properties we
    desire.

    \;

    First note that by definition, <math|\<bbb-M\><rprime|'''>> makes true
    <with|font-series|bold|CHOICE>. \ Next, an induction argument on the
    complexity of a terms <math|X>, making essential use of
    (<reference|sub><math|<rprime|'>>), yields:

    <\equation*>
      u R<rsub|X><rprime|'''>v \<Longleftrightarrow\>\<bbb-M\><rprime|'''>,v\<vDash\><big|wedge><with|math-font|cal|A><rprime|'''><rsub|v>(X)
    </equation*>

    With this, <math|\<bbb-M\><rprime|'''>> makes true
    <with|font-series|bold|JSND> since it inherits (<reference|refl>).
    \ Finally, we note that we may repeat our previous arguments from Theorem
    <reference|completeness1> to prove <with|font-series|bold|JCSQ>.
  </proof>

  <subsection|Lattice Justification Logic>

  <with|color|red|NOTE: \ THIS SECTION HAS SOME SERIOUS PROBLEMS AND IT'S
  PROBABLY WRONG...>

  \;

  Implicit in our previous presentation of SJL: \ <math|\<oplus\>> behaves
  like a union operation for knowledge bases, and dually like an intersection
  operation on accessibility relations. \ It is natural to think of
  <math|\<oplus\>> as a join/meet operator over a <em|semi-lattice>. \ In
  this section we make this explicit, by increasing the expressive power of
  simple JL to express the order theory inherent in knowledge bases. \ We
  call the novel logic presented in this section
  <with|font-shape|italic|Lattice Justification Logic> (LJL)<footnote|We note
  that ``Semi-Lattice Justification Logic'' may be a more appropriate name,
  however we have decided to shorten semic-lattice to lattice in this article
  for purposes of concision.>. \ Lattice JL may be considered a novel logic
  for studying the dynamics of <with|font-shape|italic|theory change>, where
  the logic employed by the changing theories could be LJL itself.

  \;

  <\definition>
    <math|<with|math-font|cal|L><rsub|LJL>(\<Phi\>,\<Pi\>)> extends
    <math|<with|math-font|cal|L><rsub|SJL>(\<Phi\>,\<Pi\>)> to:

    <\equation*>
      \<phi\> <space|1spc>: :=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>\<circlearrowleft\><rsub|X><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<box\><rsub|X>\<phi\><space|1spc>\|<space|1spc>X:\<phi\><space|1spc>\|<space|1spc>X\<sqsubseteq\>Y
    </equation*>

    where <math|X,Y\<in\>\<tau\>(\<Pi\>)>
  </definition>

  <\definition>
    <label|justmodels>A <strong|lattice justification model>
    <math|\<bbb-M\>=\<langle\>W,V,R,<with|math-font|cal|A>,\<preccurlyeq\>\<rangle\>>
    is a simple justification model with a new relation
    <math|\<preccurlyeq\>:W\<rightarrow\>2<rsup|\<tau\>(\<Pi\>)\<times\>\<tau\>(\<Pi\>)>>
    between terms, indexed by worlds. \ The semantics of
    <math|\<sqsubseteq\>> correspond to <math|\<preccurlyeq\>> as follows:

    <\equation*>
      \<bbb-M\>,w\<vDash\>X\<sqsubseteq\>Y\<Longleftrightarrow\>X\<preccurlyeq\><rsub|w>Y
    </equation*>
  </definition>

  <\definition>
    A lattices justification model is said to make true
    <with|font-series|bold|LATTICE> if and only if:

    <\equation*>
      \<bbb-M\>,w\<vDash\>X\<sqsubseteq\>Y\<Longleftrightarrow\><with|math-font|cal|A><rsub|w>*(X)\<subseteq\><with|math-font|cal|A><rsub|w>(Y)
    </equation*>
  </definition>

  Table <reference|logic6> lists the axioms for the logic of lattice
  justification models with the properties we have been investigating:

  <big-table|<tabular|<tformat|<cwith|17|17|1|1|cell-row-span|1>|<cwith|17|17|1|1|cell-col-span|2>|<cwith|17|17|1|1|cell-halign|c>|<cwith|15|15|1|1|cell-row-span|1>|<cwith|15|15|1|1|cell-col-span|2>|<cwith|15|15|1|1|cell-halign|c>|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>\<box\><rsub|X>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<box\><rsub|X>\<phi\>\<rightarrow\>\<box\><rsub|X>\<psi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>(X:\<phi\>)\<rightarrow\>\<box\><rsub|X>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>\<circlearrowleft\><rsub|X>\<rightarrow\>\<box\><rsub|X>\<phi\>\<rightarrow\>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>(X:\<phi\>)\<rightarrow\>(Y:\<phi\>)\<rightarrow\>X\<oplus\>Y:\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>X\<sqsubseteq\>Y\<rightarrow\>(X:\<phi\>)\<rightarrow\>Y:\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>\<circlearrowleft\><rsub|X>\<rightarrow\>\<circlearrowleft\><rsub|Y>\<rightarrow\>\<circlearrowleft\><rsub|X\<oplus\>Y>>>|<cell|>>|<row|<cell|<math|\<vdash\>X\<sqsubseteq\>Y\<rightarrow\>\<circlearrowleft\><rsub|Y>\<rightarrow\>\<circlearrowleft\><rsub|X>>>|<cell|>>|<row|<cell|<math|\<vdash\>X\<sqsubseteq\>Y\<rightarrow\>\<box\><rsub|X>\<phi\>\<rightarrow\>\<box\><rsub|Y>\<phi\>>>|<cell|>>|<row|<cell|<math|\<vdash\>X\<sqsubseteq\>X>>|<cell|>>|<row|<cell|<math|\<vdash\>X\<sqsubseteq\>Y\<rightarrow\>Y\<sqsubseteq\>Z\<rightarrow\>X\<sqsubseteq\>Z>>|<cell|>>|<row|<cell|<with|mode|math|\<vdash\>X\<sqsubseteq\>Y\<rightarrow\>X\<sqsubseteq\>Z\<oplus\>Y>>|<cell|<with|mode|math|\<vdash\>X\<sqsubseteq\>Y\<rightarrow\>X\<sqsubseteq\>Y\<oplus\>Z>>>|<row|<cell|<math|\<vdash\>X\<sqsubseteq\>Z\<rightarrow\>Y\<sqsubseteq\>Z\<rightarrow\>X\<oplus\>Y\<sqsubseteq\>Z>>|<cell|>>|<row|<cell|>|<cell|>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|<space|6spc>>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>|\<vdash\>\<box\><rsub|X>\<phi\>>>>>>>>>>|<cell|>>>>>|<label|logic6>Lattice
  Justification Logic>

  <\theorem>
    <label|completeness6>Assuming an infinite store of proposition letters
    <math|\<Phi\>>, LJL is sound and weakly complete for lattice
    justification models making true <with|font-series|bold|JCSQ>,
    <with|font-series|bold|JSND>, <with|font-series|bold|CHOICE> and
    <with|font-series|bold|LATTICE>
  </theorem>

  <\proof>
    Assume <math|\<nvdash\>\<psi\>>. \ Let
    <math|\<bbb-M\>\<assign\>\<langle\>W,V,R,<with|math-font|cal|A>,\<preccurlyeq\>\<rangle\>>
    be the same as the finitary canonical model we initially constructed in
    Theorem <reference|completeness5>, only <math|\<preccurlyeq\>> is defined
    as:

    <\equation*>
      X\<preccurlyeq\><rsub|w>Y\<Longleftrightarrow\>w\<vdash\>X\<sqsubseteq\>Y
    </equation*>

    We may deduce that there is a world <math|w\<in\>W> such that
    <math|\<bbb-M\>,w\<nvDash\>\<psi\>>. \ This canonical model makes true
    properties (<reference|fin>) through (<reference|union>) we listed in
    Theorem <reference|completeness5>, as well as a certain new properties:

    <\description-compact>
      <item*|6<math|\<preccurlyeq\>>>For all <math|X,Y\<in\>\<Xi\>>, if
      <with|mode|math|X\<preccurlyeq\><rsub|v>Y> then
      <math|R<rsub|Y>[v]\<subseteq\>R<rsub|X>[v]>

      <item*|7>For all <math|X,Y\<in\>\<Xi\>>, if
      <with|mode|math|X\<preccurlyeq\><rsub|v>Y> then
      <math|<with|math-font|cal|A><rsub|v>(X)\<subseteq\><with|math-font|cal|A><rsub|v>(Y)>

      <item*|8>If <math|X\<nin\>\<Xi\>>, then <math|R<rsub|X>=W\<times\>W>
      and <math|<with|math-font|cal|A><rsub|v>(X)=\<varnothing\>> for all
      <math|v\<in\>W>

      <item*|9><math|\<langle\>\<preccurlyeq\><rsub|v>,\<oplus\>\<rangle\>>
      is a join-semilattice over <math|\<tau\>(\<Pi\>)> for all
      <math|v\<in\>W>
    </description-compact>

    As in previous constructions, completeness is achieved by through a
    series of model refinements. \ Note that property 8 has been implicitly
    true in all of our previous constructions, although we have not been
    interested in enforcing it to be inherited by model refinements
    previously.

    \;

    We first construct a model <math|\<bbb-M\><rprime|'>> which is bisimular
    to <math|\<bbb-M\>>, where (<reference|refl>) is strengthened to a
    biconditional. \ This is done exactly as we proceeded in previous
    constructions. We note that the notion of ``bisimulation'' here includes
    that two bisimular worlds <math|v> and <math|u> must have isomorphic
    semi-lattices <math|\<preccurlyeq\><rsub|v>> and
    <math|\<preccurlyeq\><rsub|w>>. \ This is achieved by enforcing that
    <math|\<preccurlyeq\><rsub|v<rsub|l>>\<assign\>\<preccurlyeq\><rsub|v<rsub|r>>\<assign\>\<preccurlyeq\><rsub|v>>.
    As before, we have that <math|\<bbb-M\><rprime|'>,w\<nvDash\>\<psi\>> for
    some world <math|w\<in\>W<rprime|'>>.

    \;

    We next strengthen (6<math|\<preccurlyeq\>>) to a biconditional. \ Define
    <math|\<bbb-M\><rprime|''>\<assign\>\<langle\>W<rprime|''>,V<rprime|''>,R<rprime|''>,<with|math-font|cal|A><rprime|''>\<rangle\>>
    such that:

    <\itemize-dot>
      <item><with|math-display|true|<with|mode|math|W<rprime|''>\<assign\><big|pluscup><rsub|\<Xi\>>W<rprime|'>>>

      <item><math|V<rprime|''>(p)\<assign\>{v<rsub|X><space|1spc>\|<space|1spc>X\<in\>\<Xi\><space|1spc>&<space|1spc>v\<in\>V<rprime|'>(p)}>

      <item><math|R<rprime|''><rsub|X> \<assign\>
      {(v<rsub|Y>,u<rsub|Z>)<space|1spc>\|<space|1spc>Y,Z\<in\>\<Xi\><space|1spc>&<space|1spc>v
      R<rprime|'><rsub|Z> u<space|1spc>&<space|1spc>X\<preccurlyeq\><rsub|v>Z}>

      <item><math|<with|math-font|cal|A><rprime|''>(v<rsub|Y>,X)\<assign\><with|math-font|cal|A><rprime|'>(v,X)>
    </itemize-dot>

    <math|\<bbb-M\><rprime|''>> is bisimular to <math|\<bbb-M\><rprime|'>> by
    the same mechanism as the previous construction. \ The important feature
    of this structure is to observe that the converse of
    (6<math|\<preccurlyeq\>>) holds:

    <\eqnarray*>
      <tformat|<table|<row|<cell|R<rsub|Y>[v]\<subseteq\>R<rsub|X>[v]>|<cell|\<Longleftrightarrow\>>|<cell|\<forall\>Z\<in\>\<Xi\>
      \<forall\>u<rsub|Z>\<in\>W<rprime|''>(v<rsub|Q>R<rprime|'><rsub|Z>u<rsub|Z>\<Longrightarrow\>v<rsub|Q>R<rsub|X><rprime|'>u<rsub|Z>)>>|<row|<cell|>|<cell|\<Longleftrightarrow\>>|<cell|\<forall\>Z\<in\>\<Xi\>
      \<forall\>u<rsub|Z>\<in\>W<rprime|''>(v
      R<rprime|'><rsub|Z>\<Longrightarrow\>v<rsub|Q>R<rsub|X>u<rsub|Z>)>>>>
    </eqnarray*>

    \;

    Our first transformation strengthens (<reference|union>),
    (6<math|\<preccurlyeq\>>a) and (6<math|\<preccurlyeq\>>b) so that they
    hold for all terms in <math|\<tau\>(\<Pi\>)>, rather than being
    restricted to <math|\<Xi\>>. \ To this end define
    <math|\<bbb-M\><rprime|'>\<assign\>\<langle\>W<rprime|'>,V<rprime|'>,R<rprime|'>,<with|math-font|cal|A><rprime|'>,\<preccurlyeq\><rprime|'>\<rangle\>>
    where <math|W<rprime|'>>, <math|R<rprime|'>> and
    <math|\<preccurlyeq\><rprime|'>> are the same as in <math|\<bbb-M\>>, but
    <math|R<rprime|'>> and <math|<with|math-font|cal|A><rprime|'>> have the
    following modifications:

    <\eqnarray>
      <tformat|<table|<row|<cell|R<rprime|'><rsub|Y>[v]>|<cell|\<assign\>>|<cell|<big|cap><rsub|X\<preccurlyeq\><rsub|v>Y>R<rsub|X>[v]>>|<row|<cell|<with|math-font|cal|A><rprime|'><rsub|v>(Y)>|<cell|\<assign\>>|<cell|<big|cup><rsub|X\<preccurlyeq\><rsub|v>Y><with|math-font|cal|A><rprime|'><rsub|v>(X)>>>>
    </eqnarray>

    \;
  </proof>

  <subsection|Neighborhood Semantics>

  Neighborhood semantics were originally developed by Dana Scott and Richard
  Montague in the early 1970s as a generalization of Kripke semantics
  \ <cite|montague_universal_2008|scott_advice_1970>. \ In
  <cite|fagin_belief_1988>, Halpern and Fagin adapted neighborhood semantics
  for reasoning about epistemic agents without logical omniscience. \ In this
  section will demonstrate how these semantics may be modified so that
  neighborhoods corresponds to the logical consequences of a different
  knowledge bases. \ This allows for using logics with neighborhood semantics
  for reasoning about multiple knowledge bases. \ A point of distinction of
  neighborhood semantics from JL is that it may be possible that two distinct
  knowledge bases cannot be merged by the agent.

  <\definition>
    Let <math|\<Phi\>> be a set of letters and <math|\<Psi\>> a set of
    nominals, and define the language <math|<with|math-font|cal|L><rsub|N>(\<Phi\>)>
    as:

    <\equation*>
      \<phi\> <space|1spc>: :=<space|1spc>p\<in\>\<Phi\><space|1spc>\|<space|1spc>\<bot\><space|1spc>\|<space|1spc>\<phi\>\<rightarrow\>\<psi\><space|1spc>\|<space|1spc>\<box\>\<phi\><space|1spc>\|<space|1spc>A:\<phi\><space|1spc>\|<space|1spc>K\<phi\>
    </equation*>
  </definition>

  Just as previous semantics, ``<math|\<box\>\<phi\>>'' is intended to mean
  that the agent has an argument for <math|\<phi\>> from some knowledge base.
  \ A novelty we present here is that ``<math|K\<phi\>>'' means that the
  agent has an argument for <math|\<phi\>> from some
  <with|font-shape|italic|sound> knowledge base.

  \;

  <\definition>
    <label|neighborhoodmodels>A <strong|neighborhood model>
    <math|\<bbb-M\>=\<langle\>W,V,<with|math-font|cal|N>,<with|math-font|cal|A>\<rangle\>>
    has a neighborhood function <math|<with|math-font|cal|N>:W\<rightarrow\>2<rsup|2<rsup|W>>>
    and a multi-awareness function <math|<with|math-font|cal|A>:W\<rightarrow\>2<rsup|2<rsup|<with|math-font|cal|L><rsub|N>(\<Phi\>)>>>

    \;

    The semantics for <math|\<vDash\>> have the following modifications:

    <\eqnarray*>
      <tformat|<table|<row|<cell|\<bbb-M\>,w\<vDash\>\<box\>
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|<with|mode|text|there exists
      a <math|U\<in\><with|math-font|cal|N><rsub|w>> where
      <math|\<bbb-M\>,v\<vDash\>\<phi\>> for all
      <math|v\<in\>U>>>>|<row|<cell|\<bbb-M\>,w\<vDash\>K
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|<with|mode|text|there exists
      a <math|U\<in\><with|math-font|cal|N><rsub|w>> where <math|w\<in\>U>
      and <math|\<bbb-M\>,v\<vDash\>\<phi\>> for all
      <math|v\<in\>U>>>>|<row|<cell|\<bbb-M\>,w\<vDash\>A:
      \<phi\>>|<cell|<with|mode|text|iff>>|<cell|\<phi\>\<in\><big|cup><with|math-font|cal|A<rsub|w>>>>>>
    </eqnarray*>
  </definition>

  Here we modify our previous notion of <with|font-series|bold|CSQ> and
  <with|font-series|bold|SND> to match how our semantics are intended for
  reasoning over multiple bases:

  <\definition>
    The following defines properties a neighborhood model may make true:

    <\description-dash>
      <item*|NCSQ><math|\<bbb-M\>,w\<vDash\>\<box\>\<phi\><with|mode|text|
      iff there exists a set <math|X\<in\><with|math-font|cal|A><rsub|w>>
      such that > Th(\<bbb-M\>)\<cup\>X\<vdash\>\<phi\>>

      <item*|NSND><math|\<bbb-M\>,w\<vDash\>K\<phi\><with|mode|text| iff
      there exists a set <math|X\<in\><with|math-font|cal|A><rsub|w>> such
      that <with|mode|math|\<bbb-M\>,w\<vDash\>X> and
      >Th(\<bbb-M\>)\<cup\>X\<vdash\>\<phi\>>
    </description-dash>

    as before, <math|\<vdash\>> is any sound logical consequence relation for
    <math|\<vDash\>> with <with|font-series|bold|modus ponens> and
    <with|font-series|bold|reflection>
  </definition>

  <big-table|<tabular|<tformat|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>K\<phi\>\<rightarrow\>\<box\>\<phi\>>>>|<row|<cell|<math|\<vdash\>K\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>A:\<phi\>\<rightarrow\>\<box\>\<phi\>>>>|<row|<cell|>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|<space|6spc><with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\>|\<vdash\>\<box\>\<phi\>\<rightarrow\>\<box\>\<psi\>>>>>|<cell|<space|6spc>>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\>|\<vdash\>K\<phi\>\<rightarrow\>K\<psi\>>>>>>>>>>>>>>|<label|logic3>A
  Neighborhood Logic for <with|font-series|bold|NCSQ> and <strong|NSND>>

  <\theorem>
    Assuming an infinite store of letters <math|\<Phi\>>, the logic in Table
    <reference|logic3> is sound and weakly complete for neighborhood
    semantics making true <with|font-series|bold|NCSQ<math|>> and
    <with|font-series|bold|NSND>.
  </theorem>

  <\proof>
    Assume that <math|\<nvdash\>\<psi\>>, and define the finitary canonical
    model <math|\<bbb-M\>=\<langle\>W,V,<with|math-font|cal|K>,<with|math-font|cal|N>,<with|math-font|cal|A>\<rangle\>>
    where:

    <\itemize-dot>
      <item><math|W\<assign\><with|mode|text|the maximally consistent sets of
      subformulae of <math|\<psi\>>, closed under single negation>>

      <item><math|V(p)\<assign\>{v\<in\>W<space|1spc>\|<space|1spc>p\<in\>v}>

      <item><with|mode|math|<with|math-font|cal|K><rsub|w>\<assign\>{S\<in\>2<rsup|W><space|1spc>\|<space|1spc>{v\<in\>W<space|1spc>\|<space|1spc>\<phi\>\<in\>v}\<subseteq\>S<space|1spc>&<space|1spc>K\<phi\>\<in\>w}>

      <item><with|mode|math|<math|<with|math-font|cal|N><rsub|w>\<assign\>{S\<in\>2<rsup|W><space|1spc>\|<space|1spc>{v\<in\>W<space|1spc>\|<space|1spc>\<phi\>\<in\>v}\<subseteq\>S<space|1spc>&<space|1spc>\<box\>\<phi\>\<in\>w}>>

      <item><with|mode|math|<math|<with|math-font|cal|A><rsub|w>\<assign\>{{\<phi\>}<space|1spc>\|<space|1spc>A:\<phi\>\<in\>w}>>
    </itemize-dot>

    Note that in this model, there are neighborhoods for both knowledge and
    belief; more work is necessary to find a model based on this one which
    conforms to the semantics in Definition <reference|neighborhoodmodels>.
    \ For now, assume that <math|K> is just another modality governed by the
    neighborhoods in <math|<with|math-font|cal|K><rsub|w>>. \ In both
    neighborhood functions, our idea is that the neighborhoods of <math|w> in
    are supersets <math|S\<supseteq\><left|llbracket>\<phi\><right|rrbracket>>
    where <math|\<box\>\<phi\>\<in\>w> or <math|K\<phi\>\<in\>w>,
    respectively.

    \;

    There are steps of the inductive proof of the Truth Lemma for this
    structure which are not obvious nor obviously documented elsewhere.
    \ Assume <math|\<bbb-M\>,w\<vDash\>\<box\>\<chi\>>, where the Truth Lemma
    has been proven to hold for <math|\<chi\>>; we must show
    <math|\<box\>\<chi\>\<in\>w>. \ By our assumption there is some
    <math|\<phi\>> and <math|S> where <math|\<box\>\<phi\>\<in\>w> and
    <math|S\<supseteq\>{v\<in\>W<space|1spc>\|<space|1spc>\<phi\>\<in\>v}>.
    \ We argue that <math|\<vdash\>\<phi\>\<rightarrow\>\<chi\>>; for if not
    then by the finitary Lindenbaum lemma there is some <math|u\<in\>W> where
    <math|\<phi\>\<in\>u> and <math|\<chi\>\<nin\>u>. \ Hence <math|u\<in\>S>
    and <math|\<bbb-M\>,u\<nvDash\>\<chi\>>, a contradiction. \ Since
    <math|\<vdash\>\<phi\>\<rightarrow\>\<chi\>> then we know that
    <math|\<vdash\>\<box\>\<phi\>\<rightarrow\>\<box\>\<chi\>> by our rules,
    which means that <math|\<box\>\<chi\>\<in\>w> by maximality.

    \;

    By the Lindenbaum Lemma we have that there is some <math|w\<in\>W> where
    <math|\<bbb-M\>,w\<nvDash\>\<psi\>>. \ <math|\<bbb-M\>> makes true a
    number of properties:

    <\enumerate-numeric>
      <item><math|W> and <math|<with|math-font|cal|A><rsub|v>> are finite for
      all <math|v\<in\>W>, and <math|\<psi\>\<in\><big|cup><with|math-font|cal|A<rsub|w>>>
      only if <math|\<psi\>> is a subformula of <math|\<phi\>>

      <item><math|<with|math-font|cal|K><rsub|w>\<subseteq\><with|math-font|cal|N><rsub|w>>

      <item>If <math|S\<in\><with|math-font|cal|K><rsub|w>> then
      <math|w\<in\>S>

      <item><math|\<bbb-M\>,v\<vDash\>A:\<phi\>\<rightarrow\>\<box\>\<phi\>>
      for all <math|v\<in\>W>

      <item><math|<with|math-font|cal|N><rsub|w>> and
      <math|<with|math-font|cal|K><rsub|w>> are closed under supersets
    </enumerate-numeric>

    \;

    As in the proof of Theorem <reference|completeness1>, we use a
    bisimulation to move to a model where property (3) is strengthened to
    (3<math|<rprime|'>>): for all <math|S\<in\><with|math-font|cal|N><rsub|w>>,
    <math|w\<in\>S> if and only if <math|S\<in\><with|math-font|cal|K><rprime|'><rsub|w>>.
    \ We defer the reader to <cite|hansen_bisimulation_2007|pauly_bisimulation_1999>
    for details regarding bisimulation in neighborhood semantics. \ Define
    <math|\<bbb-M\><rprime|'>\<assign\>\<langle\>W<rprime|'>,V<rprime|'>,<with|math-font|cal|K><rprime|'>,<with|math-font|cal|N><rprime|'>,<with|math-font|cal|A><rprime|'>\<rangle\>>
    such that:

    <\itemize-dot>
      <item><with|mode|math|W<rprime|'>\<assign\>W\<uplus\>W> where
      \ <math|l,r> its associated canonical injections and
      <math|\<theta\>(v<rsub|l>)\<assign\>\<theta\>(v<rsub|r>)\<assign\>v> is
      a left-inverse of <math|l,r>

      <item><math|V<rprime|'>(p)\<assign\>{v<rsub|l>,v<rsub|r><space|1spc>\|<space|1spc>v\<in\>V(p)}>

      <item><math|<with|math-font|cal|K><rprime|'>(v<rsub|i>)\<assign\>{S<space|1spc>\|<space|1spc>v<rsub|i>\<in\>S<space|1spc>&<space|1spc>\<theta\>[S]\<in\><with|math-font|cal|K<rsub|v>>}>
      where <math|i=l,r>

      <item><math|<with|math-font|cal|N><rprime|'>(v<rsub|i>)\<assign\><with|math-font|cal|K><rprime|'>(v<rsub|i>)\<cup\>{S<space|1spc>\|<space|1spc>v<rsub|i>\<nin\>S<space|1spc>&<space|1spc>\<theta\>[S]\<in\><with|math-font|cal|N<rsub|v>>}>
      where <math|i=l,r>

      <item><math|<with|math-font|cal|A><rprime|'>(v<rsub|l>)\<assign\><with|math-font|cal|A><rprime|'>(v<rsub|r>)\<assign\><with|math-font|cal|A>(v)><math|>
    </itemize-dot>

    \;

    If we let <math|Z\<assign\>{(v,v<rsub|r>),(v,v<rsub|l>)<space|1spc>\|<space|1spc>v\<in\>W}>,
    it is straightforward to verify that <math|Z> is a neighborhood
    bisimulation. \ Hence <math|\<bbb-M\>,w<rsub|l>\<nvDash\>\<psi\>>.
    \ Along with (3<math|<rprime|'>>), this model makes true (1), (2), (4).
    \ In fact, in light of (<math|3<rprime|'>>), we can see that this model
    does not need <math|<with|math-font|cal|K><rprime|'>>, and conforms to
    the semantics in Definition <reference|neighborhoodmodels>.<htab|5mm>

    \;

    As in previous proofs, let <math|\<Lambda\>> be the proposition letters
    occuring in <math|\<psi\>> and define an injection
    <math|\<iota\>:W<rprime|'>\<hookrightarrow\>\<Phi\>\<backslash\>\<Lambda\>>,
    assigning a nominal to every world in <math|\<bbb-M\><rprime|'>>.
    \ Define <math|\<bbb-M\><rprime|''>\<assign\>\<langle\>W<rprime|''>,
    V<rprime|''>,<with|math-font|cal|N><rprime|''>,<with|math-font|cal|A><rprime|''>\<rangle\>>
    such that:

    \;

    <\with|par-mode|center>
      <tabular|<tformat|<table|<row|<cell|<math|\<bullet\>>>|<cell|<math|W<rprime|''>\<assign\>W<rprime|'>>>|<cell|>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-display|true|V<rprime|''>(p)\<assign\><choice|<tformat|<table|<row|<cell|V<rprime|'>(p)>|<cell|p\<in\>\<Lambda\>>>|<row|<cell|{v}>|<cell|p=i(v)>>|<row|<cell|\<varnothing\>>|<cell|o/w>>>>>>>>>|<row|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|N><rprime|''><rsub|w>\<assign\><with|math-font|cal|N><rprime|'><rsub|w>>>|<cell|<space|3spc>>|<cell|<math|\<bullet\>>>|<cell|<math|<with|math-font|cal|A><rprime|''><rsub|v>\<assign\>{\<partial\><rsub|v>S<space|1spc>\|<space|1spc>S\<in\><with|math-font|cal|N><rprime|'><rsub|w>}>>>>>>
    </with>

    \;

    \;

    Where <math|\<partial\><rsub|v>S\<assign\>{\<phi\><space|1spc>\|<space|1spc>\<phi\>\<in\><big|cup><with|math-font|cal|A><rsub|v><rprime|'>,
    <with|mode|text|<math|\<phi\>> is a subformula of <math|\<psi\>>
    and><space|1spc>S\<subseteq\><left|llbracket>\<phi\><right|rrbracket><rsup|\<bbb-M\><rprime|'>>}\<cup\>{\<neg\>\<iota\>(u)<space|1spc>\|<space|1spc>u\<nin\>S}>.

    As before, this model agrees with <math|\<bbb-M\><rprime|'>> on all
    subformulae of <math|\<psi\>>, using the semantics in Definition
    <reference|neighborhoodmodels>, hence
    <math|\<bbb-M\><rprime|''>,w<rsub|l>\<nvDash\>\<phi\>>. \ 

    \;

    All that is left is to show <with|font-series|bold|NCSQ> and
    <with|font-series|bold|NSND> from three new properties:

    <\enumerate-roman>
      <item>For all words <math|v> and all
      <math|X\<in\><with|math-font|cal|A><rsub|v><rprime|''>>, <math|X> is
      finite and \ <math|X=\<partial\><rsub|v>S> for some
      <math|S\<in\><with|math-font|cal|N><rsub|v><rprime|''>>

      <item>For all <math|v> and all <math|S\<in\><with|math-font|cal|N><rsub|v>>,
      <math|u\<in\>S> if and only if <math|\<bbb-M\><rprime|''>,u\<vDash\><big|wedge>\<partial\><rsub|v>S>

      <item>The logic presented in Table <reference|logic3> is sound for
      <math|\<bbb-M\><rprime|''>>
    </enumerate-roman>

    Along with the deduction theorem for <math|\<vdash\>>, these properties
    establish <with|font-series|bold|NCSQ> for this model using the logic of
    Table <reference|logic3> itself:

    <\align*>
      <tformat|<table|<row|<cell|<with|mode|text|<math|\<exists\>X\<in\><with|math-font|cal|A<rprime|''><rsub|v>><with|mode|text|
      s.t. >Th(\<bbb-M\><rprime|''>)\<cup\>X\<vdash\>\<phi\>>>>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. >Th(\<bbb-M\><rprime|''>)\<cup\>\<partial\><rsub|v>S\<vdash\>\<phi\>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. >Th(\<bbb-M\><rprime|''>)\<vdash\><big|wedge>\<partial\><rsub|v>S\<rightarrow\>\<phi\>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. ><big|wedge>\<partial\><rsub|v>S\<rightarrow\>\<phi\>\<in\>Th(\<bbb-M\><rprime|''>)>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. ><left|llbracket><big|wedge>\<partial\><rsub|v>S<right|rrbracket>\<subseteq\><left|llbracket>\<phi\><right|rrbracket>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. <with|mode|math|\<forall\>u\<in\>W> if
      >\<bbb-M\>,u\<vDash\><big|wedge>\<partial\><rsub|v>S<with|mode|text|
      then >\<bbb-M\>,u\<vDash\>\<phi\>>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\><with|mode|text|<math|\<exists\>S\<in\><with|math-font|cal|N<rprime|''><rsub|v>><with|mode|text|
      s.t. >\<bbb-M\>,u\<vDash\>\<phi\>><with|mode|math|<with|mode|text| for
      all >u\<in\>S>>>>|<row|<cell|>|<cell|\<Longleftrightarrow\>\<bbb-M\>,v\<vDash\>\<box\>\<phi\>>>>>
    </align*>

    <with|font-series|bold|NSND> follows from <with|font-series|bold|NCSQ>
    and the semantics of Definition <reference|neighborhoodmodels>.
  </proof>

  It is not too hard to identify the fragment of this logic that governs
  knowledge alone. \ The fragment given in Table <reference|logic4> has
  special significance to us, since it governs the notion of knowledge
  presented in Ÿ<reference|quantifying>.

  <big-table|<tabular|<tformat|<table|<row|<cell|<math|\<vdash\>\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>(\<phi\>\<rightarrow\>\<psi\>\<rightarrow\>\<chi\>)\<rightarrow\>(\<phi\>\<rightarrow\>\<psi\>)\<rightarrow\>\<phi\>\<rightarrow\>\<chi\>>>>|<row|<cell|<math|\<vdash\>((\<phi\>\<rightarrow\>\<bot\>)\<rightarrow\>(\<psi\>\<rightarrow\>\<bot\>))\<rightarrow\>\<psi\>\<rightarrow\>\<phi\>>>>|<row|<cell|<math|\<vdash\>K\<phi\>\<rightarrow\>\<phi\>>>>|<row|<cell|>>|<row|<cell|<tabular|<tformat|<table|<row|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\><space|4spc>\<vdash\>\<phi\>|\<vdash\>\<psi\>>>>>|<cell|>|<cell|>|<cell|<with|math-display|true|<math|<frac|\<vdash\>\<phi\>\<rightarrow\>\<psi\>|\<vdash\>K\<phi\>\<rightarrow\>K\<psi\>>>>>>>>>>>>>>|<label|logic4>A
  knowledge-only neighborhood logic for <with|font-series|bold|NCSQ> and
  <strong|NSND>>

  <\proposition>
    The knowledge-only logic presented governs the <math|\<box\>>-free
    fragment of the logic in Table <reference|logic3>
  </proposition>

  This concludes our analysis of knowledge bases using neighborhood
  semantics.

  <\subsection>
    <label|quantifying>Using Modalities to Quantify over Knowledge Bases
  </subsection>

  \;

  <section|Conclusions & Further Research>

  The logic presented in Table <reference|logic1> is a conservative extension
  of the basic modal logic <math|K>, which means that its decision problem is
  <with|font-family|ss|PSPACE> hard (a lower bound). \ Our finitary
  completeness proof establishes that its complexity is in
  <with|font-family|ss|EXP2-TIME> (an upper bound).

  \;

  Worlds in epistemic logic might correspond to fantastic, pretend scenarios;
  however, it may be desirable for some philosophers to model knowledge about
  imaginary lands. \ After all, many children ``know'' a lot about Tolkien's
  <em|middle earth> or Rowling's <em|Hogwarts> (the school Harry Potter
  attends).

  <\bibliography|bib|plain|~/Documents/EviL/Paper/zotero.bib>
    <\bib-list|10>
      <bibitem*|1><label|bib-artemov_logic_1994>S.<nbsp>N Artemov.
      <newblock>Logic of proofs. <newblock><with|font-shape|italic|Annals of
      Pure and Applied Logic>, 67(1):29â€“60, 1994.

      <bibitem*|2><label|bib-artemov_introducing_2005>S.<nbsp>N Artemov and
      E.<nbsp>Nogina. <newblock>Introducing justification into epistemic
      logic. <newblock><with|font-shape|italic|Journal of Logic and
      Computation>, 15(6):1059, 2005.

      <bibitem*|3><label|bib-basu_revealed_1980>Kaushik Basu.
      <newblock><with|font-shape|italic|Revealed preference of government>.
      <newblock>Cambridge University Press, Cambridge; New York, 1980.

      <bibitem*|4><label|bib-blackburn_modal_2001>P.<nbsp>Blackburn,
      M.<nbsp>De Rijke, and Y.<nbsp>Venema.
      <newblock><with|font-shape|italic|Modal logic>. <newblock>Cambridge
      Univ Pr, 2001.

      <bibitem*|5><label|bib-boolos_logic_1995>George Boolos.
      <newblock><with|font-shape|italic|The logic of provability>.
      <newblock>Cambridge University Press, 1995.

      <bibitem*|6><label|bib-bull_approach_1970>R.<nbsp>A. Bull. <newblock>An
      approach to tense logic. <newblock><with|font-shape|italic|Theoria>,
      36(3):282--300, December 1970.

      <bibitem*|7><label|bib-davidson_could_1995>Donald Davidson.
      <newblock>Could there be a science of rationality?
      <newblock><with|font-shape|italic|International Journal of
      Philosophical Studies>, 3(1):1â€“16, 1995.

      <bibitem*|8><label|bib-fagin_belief_1988>R.<nbsp>Fagin and J.<nbsp>Y
      Halpern. <newblock>Belief, awareness, and limited reasoning.
      <newblock><with|font-shape|italic|Artificial Intelligence>,
      34(1):39â€“76, 1988.

      <bibitem*|9><label|bib-fitting_logic_2005>M.<nbsp>Fitting.
      <newblock>The logic of proofs, semantically.
      <newblock><with|font-shape|italic|Annals of Pure and Applied Logic>,
      132(1):1â€“25, 2005.

      <bibitem*|10><label|bib-halpern_set-theoretic_1999>Joseph<nbsp>Y.
      Halpern. <newblock>Set-theoretic completeness for epistemic and
      conditional logic. <newblock><with|font-shape|italic|Annals of
      Mathematics and Artificial Intelligence>, 26(1-4):1--27, 1999.

      <bibitem*|11><label|bib-hansen_bisimulation_2007>Helle<nbsp>Hvid
      Hansen, Clemens Kupke, and Eric Pacuit. <newblock>Bisimulation for
      neighbourhood structures. <newblock>In
      <with|font-shape|italic|Proceedings of the 2nd international conference
      on Algebra and coalgebra in computer science>, pages 279--293, Bergen,
      Norway, 2007. Springer-Verlag.

      <bibitem*|12><label|bib-hendricks_mainstream_2006>V.<nbsp>F Hendricks.
      <newblock><with|font-shape|italic|Mainstream and formal epistemology>.
      <newblock>Cambridge Univ Pr, 2006.

      <bibitem*|13><label|bib-kornblith_beyond_1980>Hilary Kornblith.
      <newblock>Beyond foundationalism and the coherence theory.
      <newblock><with|font-shape|italic|The Journal of Philosophy>,
      77(10):597--612, October 1980.

      <bibitem*|14><label|bib-montague_universal_2008>Richard Montague.
      <newblock>Universal grammar. <newblock><with|font-shape|italic|Theoria>,
      36(3):373--398, 2008.

      <bibitem*|15><label|bib-pauly_bisimulation_1999>M.<nbsp>Pauly.
      <newblock>Bisimulation for general non-normal modal logic.
      <newblock><with|font-shape|italic|Manuscript>, 1999.

      <bibitem*|16><label|bib-prior_revised_1969>Arthur<nbsp>N. Prior.
      <newblock><with|font-shape|italic|Revised and Expanded Edition of
      Arthur N. Prior: Papers on Time and Tense>. <newblock>Oxford University
      Press, 1969. <newblock>reprinted in 2003.

      <bibitem*|17><label|bib-rubinstein_modeling_1998>Ariel Rubinstein.
      <newblock><with|font-shape|italic|Modeling Bounded Rationality>.
      <newblock>MIT Press, 1998.

      <bibitem*|18><label|bib-scott_advice_1970>D.<nbsp>Scott.
      <newblock>Advice on modal logic. <newblock><with|font-shape|italic|Philosophical
      problems in Logic>, 143:74, 1970.

      <bibitem*|19><label|bib-sen_behaviour_1973>Amartya Sen.
      <newblock>Behaviour and the concept of preference.
      <newblock><with|font-shape|italic|Economica>, 40(159):241--259, August
      1973.

      <bibitem*|20><label|bib-van_benthem_inference_2009>Johan van Benthem
      and F.<nbsp>R VelÃ¡zquez-Quesada. <newblock>Inference, promotion, and
      the dynamics of awareness. <newblock><with|font-shape|italic|ILLC
      Amsterdam. To appear in Knowledge, Rationality and Action>, 2009.
    </bib-list>
  </bibliography>
</body>

<\initial>
  <\collection>
    <associate|language|american>
    <associate|page-type|letter>
    <associate|par-columns|1>
    <associate|par-first|0fn>
    <associate|par-par-sep|1fns>
    <associate|sfactor|4>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|1>>
    <associate|auto-10|<tuple|3.2|7>>
    <associate|auto-11|<tuple|4|8>>
    <associate|auto-12|<tuple|3.3|8>>
    <associate|auto-13|<tuple|5|8>>
    <associate|auto-14|<tuple|6|?>>
    <associate|auto-15|<tuple|3.4|?>>
    <associate|auto-16|<tuple|4|?>>
    <associate|auto-17|<tuple|4|?>>
    <associate|auto-2|<tuple|2|2>>
    <associate|auto-3|<tuple|2.1|2>>
    <associate|auto-4|<tuple|1|2>>
    <associate|auto-5|<tuple|2.2|4>>
    <associate|auto-6|<tuple|2|4>>
    <associate|auto-7|<tuple|3|5>>
    <associate|auto-8|<tuple|3.1|5>>
    <associate|auto-9|<tuple|3|6>>
    <associate|awarenesslogic|<tuple|2.1|2>>
    <associate|awarenessmodels|<tuple|2|2>>
    <associate|basic-modal|<tuple|2|?>>
    <associate|bib-artemov_introducing_2005|<tuple|2|8>>
    <associate|bib-artemov_logic_1994|<tuple|1|8>>
    <associate|bib-basu_revealed_1980|<tuple|3|8>>
    <associate|bib-blackburn_modal_2001|<tuple|4|8>>
    <associate|bib-boolos_logic_1995|<tuple|5|8>>
    <associate|bib-bull_approach_1970|<tuple|6|8>>
    <associate|bib-castaneda_knowing_1970|<tuple|10|?>>
    <associate|bib-davidson_could_1995|<tuple|7|8>>
    <associate|bib-fagin_belief_1987|<tuple|8|8>>
    <associate|bib-fagin_belief_1988|<tuple|8|?>>
    <associate|bib-fitting_logic_2005|<tuple|9|9>>
    <associate|bib-ginet_what_1970|<tuple|8|?>>
    <associate|bib-halpern_set-theoretic_1999|<tuple|10|9>>
    <associate|bib-hansen_bisimulation_2007|<tuple|11|?>>
    <associate|bib-hendricks_mainstream_2006|<tuple|12|9>>
    <associate|bib-kornblith_beyond_1980|<tuple|13|9>>
    <associate|bib-montague_universal_2008|<tuple|14|9>>
    <associate|bib-pauly_bisimulation_1999|<tuple|15|?>>
    <associate|bib-prior_revised_1969|<tuple|16|9>>
    <associate|bib-rubinstein_modeling_1998|<tuple|17|9>>
    <associate|bib-scott_advice_1970|<tuple|18|9>>
    <associate|bib-sen_behaviour_1973|<tuple|19|9>>
    <associate|bib-van_benthem_inference_2009|<tuple|20|9>>
    <associate|bib-van_benthem_reflectionsepistemic_1991|<tuple|11|?>>
    <associate|completeness1|<tuple|4|3>>
    <associate|completeness2|<tuple|8|?>>
    <associate|completeness5|<tuple|12|?>>
    <associate|completeness6|<tuple|16|?>>
    <associate|fin|<tuple|1|?>>
    <associate|footnote-1|<tuple|1|1>>
    <associate|footnote-10|<tuple|10|?>>
    <associate|footnote-2|<tuple|2|1>>
    <associate|footnote-3|<tuple|3|5>>
    <associate|footnote-4|<tuple|4|?>>
    <associate|footnote-5|<tuple|5|?>>
    <associate|footnote-6|<tuple|6|?>>
    <associate|footnote-7|<tuple|7|?>>
    <associate|footnote-8|<tuple|8|?>>
    <associate|footnote-9|<tuple|9|?>>
    <associate|footnr-1|<tuple|1|1>>
    <associate|footnr-10|<tuple|10|?>>
    <associate|footnr-2|<tuple|2|1>>
    <associate|footnr-3|<tuple|3|5>>
    <associate|footnr-4|<tuple|4|?>>
    <associate|footnr-5|<tuple|5|?>>
    <associate|footnr-6|<tuple|6|?>>
    <associate|footnr-7|<tuple|7|?>>
    <associate|footnr-8|<tuple|8|?>>
    <associate|footnr-9|<tuple|9|?>>
    <associate|hybridsemantics|<tuple|6|4>>
    <associate|inter|<tuple|6|?>>
    <associate|intro|<tuple|1|1>>
    <associate|justmodels|<tuple|14|6>>
    <associate|logic|<tuple|1|?>>
    <associate|logic1|<tuple|1|2>>
    <associate|logic2|<tuple|2|4>>
    <associate|logic3|<tuple|5|7>>
    <associate|logic4|<tuple|6|8>>
    <associate|logic5|<tuple|4|?>>
    <associate|logic6|<tuple|4|?>>
    <associate|neighborhoodmodels|<tuple|18|6>>
    <associate|quantifying|<tuple|3.4|8>>
    <associate|refl|<tuple|3|?>>
    <associate|semdef1|<tuple|2|?>>
    <associate|simplyjustificationmodels|<tuple|11|?>>
    <associate|sndneess|<tuple|4|?>>
    <associate|sndness|<tuple|4|?>>
    <associate|sub|<tuple|6|?>>
    <associate|theorem-theorem|<tuple|4|?>>
    <associate|union|<tuple|5|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      van_benthem_reflectionsepistemic_1991

      van_benthem_inference_2009

      artemov_introducing_2005

      halpern_set-theoretic_1999

      rubinstein_modeling_1998

      sen_behaviour_1973

      basu_revealed_1980

      davidson_could_1995

      van_benthem_reflectionsepistemic_1991

      artemov_introducing_2005

      artemov_logic_1994

      fitting_logic_2005

      van_benthem_inference_2009

      fagin_belief_1987

      hendricks_mainstream_2006

      kornblith_beyond_1980

      fagin_belief_1987

      van_benthem_inference_2009

      blackburn_modal_2001

      blackburn_modal_2001

      boolos_logic_1995

      prior_revised_1969

      bull_approach_1970

      boolos_logic_1995

      blackburn_modal_2001

      artemov_logic_1994

      artemov_introducing_2005

      fitting_logic_2005

      montague_universal_2008

      scott_advice_1970

      fagin_belief_1988

      hansen_bisimulation_2007

      pauly_bisimulation_1999
    </associate>
    <\associate|table>
      <tuple|normal|<label|logic1>Awareness Logic for
      <with|font-series|<quote|bold>|CSQ> and
      <with|font-series|<quote|bold>|SND>|<pageref|auto-4>>

      <tuple|normal|<label|logic2>Hybrid Awareness Logic for
      <with|font-series|<quote|bold>|CSQ>|<pageref|auto-6>>

      <tuple|normal|<label|logic5>Simple Justification
      Logic|<pageref|auto-9>>

      <tuple|normal|<label|logic3>A Neighborhood Logic for
      <with|font-series|<quote|bold>|NCSQ> and
      <with|font-series|<quote|bold>|math-font-series|<quote|bold>|NSND>|<pageref|auto-12>>

      <tuple|normal|<label|logic4>A knowledge-only neighborhood logic for
      <with|font-series|<quote|bold>|NCSQ> and
      <with|font-series|<quote|bold>|math-font-series|<quote|bold>|NSND>|<pageref|auto-13>>
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Introduction<label|intro>>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Basic
      Explicit Logics of Knowledge Bases>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|2.1<space|2spc>Awareness
      Logic<label|awarenesslogic> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1.5fn>|2.2<space|2spc>Hybrid Awareness Logic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Logics
      of Multiple Knowledge Bases> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|3.1<space|2spc>Simple Justification Logic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <with|par-left|<quote|1.5fn>|3.2<space|2spc>Lattice Justification Logic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <with|par-left|<quote|1.5fn>|3.3<space|2spc>Neighborhood Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <with|par-left|<quote|1.5fn>|3.4<space|2spc><label|quantifying>Using
      Modalities to Quantify over Knowledge Bases
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Conclusions
      & Further Research> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>