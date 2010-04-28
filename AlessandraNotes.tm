<TeXmacs|1.0.7.2>

<style|generic>

<\body>
  <\enumerate-numeric>
    <item>Add section for abstract completeness, and take stock. Now add a
    philosophical motivation for the translation -- \ mention that link with
    provability missing. \ And now translation.

    <item>Give an informal explanation of the <with|font-shape|italic|island>
    concept -- name surname thing

    <item>Why does <math|p> exist?

    <\itemize-dot>
      <item>It gives names to people, surnames to
      <with|font-shape|italic|islands>, which are like the families the
      people belong to.

      <item>Way we can do this (explain later).
    </itemize-dot>

    <item>Get rid of <math|\<lambda\>> in <math|\<vartheta\><rsub|2>> (use
    <math|\<vartheta\><rsub|2>(w)\<assign\><big|prod><rsub|a\<in\>A>B<rsub|a>w>)

    <item>Add explanations after 2.3.20:

    <\enumerate-alpha>
      <item><math|\<Lambda\><rsup|\<bbb-M\>>> is the set of people/families

      <item><math|p<rsub|{w}>> and <math|p<rsub|[[w]]>> are the names and
      surnames

      <item><math|\<vartheta\><rsub|1>> and <math|\<vartheta\><rsub|2>> are
      the components of the a ``translation'' map <math|\<vartheta\>> between
      states of abstract model and states of an associated concrete model.

      <item>

      <\itemize-dot>
        <item><math|\<vartheta\><rsub|1>>

        <\itemize-minus>
          <item>All the <math|p> that are related to <math|\<phi\>>

          <item>Identification of the island where <math|w> stands.

          <item>Address the issue for why only the surname and not its name.
        </itemize-minus>
      </itemize-dot>

      <item>Assymetry in <math|\<vartheta\><rsub|2>(w)> -- encodes

      <\itemize-dot>
        <item>Info on <math|R<rsub|X>[w]>

        <item>Info on <math|\<sqsupseteq\><rsub|X>[w]>
      </itemize-dot>
    </enumerate-alpha>
  </enumerate-numeric>

  \;

  Clearly for every <math|w>, <math|\<vartheta\>(w)> is a tuple consisting of
  <math|\<vartheta\><rsub|1>(w)> and <math|\<vartheta\><rsub|2>(w)>. \ We
  have

  <\itemize-dot>
    <item><math|\<vartheta\><rsub|1>:W\<rightarrow\>\<wp\>\<Phi\>>, a
    function which takes worlds to sets of proposition letters.

    <item><math|\<vartheta\><rsub|2>:W\<rightarrow\>\<wp\><with|math-font|cal|L><rsub|0>(\<Phi\>)>,
    a function which takes worlds to sets of formulae over <math|\<Phi\>>.
    \ Say that this represents the accessibility relations.
  </itemize-dot>

  My explanation --

  We need:

  <\enumerate-alpha>
    <item><math|w R<rsub|X>v> iff <math|\<vartheta\><rsub|1>(v)\<vDash\>
    <big|wedge>\<vartheta\><rsub|2>(w)<rsub|X>>

    <item><math|w\<sqsupseteq\><rsub|X>v> iff (1)
    <math|\<vartheta\><rsub|1>(w)=\<vartheta\><rsub|1>(v)> and (2)
    <math|B<rsub|X>(w)\<supseteq\>B<rsub|X>(v)>
  </enumerate-alpha>

  This is precisely because these are the features necessary for the
  inductive steps of the translation theorem.

  Negative: First explane why we shouldn't define
  <math|\<vartheta\><rsub|1>(w)> in terms of <math|p<rsub|{w}>> because of
  (b) part (1). \ This motivates the concerns raised in (d) above.

  Positive: \ Because of invariance, we don't need names <math|p<rsub|{w}>>,
  can get away with surnames <math|p<rsub|[[ w]]>>.

  Positive: \ Why is <math|\<vartheta\><rsub|2>(w)> the way it is? \ Because
  one part codes <math|R> and the other part codes <math|\<sqsupseteq\>>.

  Negative: Looks like a strange choice. \ Explain why we can't have
  <math|B<rsub|X>(w) \<assign\> {p<rsub|{v}> \| w \<sqsupseteq\>v
  }\<cup\>\<ldots\>> \ This is because we banned <math|p<rsub|[[v]]>> from
  <math|\<vartheta\><rsub|1>(v)>. \ Why we can't have \ <math|B<rsub|X>(w)
  \<assign\> {p<rsub|[[v]]> \| w R v }\<cup\>\<ldots\>>? \ Why not
  <math|\<vartheta\><rsub|2>(w)\<assign\><big|vee><rsub|v\<in\>R[w]>p<rsub|[[v]]>>
  like before? \ Because we need (b) part (2), which prohibits this. \ It
  would have to be that if <math|w\<sqsupseteq\><rsub|X>v> then\ 
</body>

<\initial>
  <\collection>
    <associate|language|american>
    <associate|page-type|letter>
    <associate|sfactor|3>
  </collection>
</initial>