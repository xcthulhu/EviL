<TeXmacs|1.0.7.2>

<style|generic>

<\body>
  <subsection|Negative Doxastic Introspection>

  As a first application of <with|font-shape|small-caps|EviL>, we shall
  investigate two <em|collapse theorems> associated with potential axiomatic
  extensions of <with|font-shape|small-caps|EviL>.

  <subsubsection|Negative Doxastic Introspection>

  Recall that <with|font-shape|italic|negative doxastic introspection> is
  characterized by axiom <with|font-series|bold|5>, which asserts:

  <\equation*>
    \<diamondsuit\>\<phi\>\<rightarrow\>\<box\>\<diamondsuit\>\<phi\>
  </equation*>

  We can observe the following

  <\lemma>
    For any <with|font-shape|small-caps|EviL> model
    <math|<with|math-font|Euler|M>> that makes true axiom
    <math|<with|math-font-series|bold|5>>, then for all pairs
    <math|(a,A)\<in\><with|math-font|Euler|M>> we have that

    <\equation*>
      <with|math-font|Euler|M>,(a,A)\<Vdash\>\<ominus\>\<circlearrowleft\>\<leftrightarrow\>\<circlearrowleft\>
    </equation*>
  </lemma>

  <\proof>
    We have to show two directions. \ We have that
    <with|mode|math|<with|math-font|Euler|M>,(a,A)\<Vdash\>\<circlearrowleft\>\<rightarrow\>\<ominus\>\<circlearrowleft\>>
    so we shall focus on the other direction.

    Assume towards a contradiction that <math|<with|math-font|Euler|M>,(a,A)\<Vdash\>\<ominus\>\<circlearrowleft\>>,
    but <math|<with|math-font|Euler|M>,(a,A)\<nVdash\>\<circlearrowleft\>>.
    \ Hence there is some <math|\<phi\>\<in\>A> where
    <math|<with|math-font|Euler|M>,(a,A)\<nVdash\>\<phi\>> but
    <math|<with|math-font|Euler|M>,(a,A)\<Vdash\>\<box\>\<phi\>>. \ Moreover
    we have that there is some <math|A<rprime|'>> where
    <math|(a,A<rprime|'>)\<in\><with|math-font|Euler|M>>, such that
    <math|<with|math-font|Euler|M>,(a,A<rprime|'>)\<Vdash\>A<rprime|'>> and
    <math|<with|math-font|Euler|>A<rprime|'>\<subseteq\>A>. \ Since
    <math|\<phi\>\<in\><with|math-font|cal|L><rsub|0>> we know that
    <math|<with|math-font|Euler|M>,(a,A<rprime|'>)\<Vdash\>\<neg\>\<phi\>>,
    hence <math|<with|math-font|Euler|M>,(a,A<rprime|'>)\<Vdash\>\<diamondsuit\>\<neg\>\<phi\>>.
    \ But from axiom <with|font-series|bold|5> we have that
    <math|<with|math-font|Euler|M>,(a,A<rprime|'>)\<Vdash\>\<box\>\<diamondsuit\>\<neg\>\<phi\>>.
    \ But notice that <math|<with|math-font|Euler|M>,(a,A)\<Vdash\>A<rprime|'>>,
    whence <with|mode|math|<with|math-font|Euler|M>,(a,A<rprime|'>)\<Vdash\>\<diamondsuit\>\<neg\>\<phi\>>.
    \ But this is a contradiction, hence it must be that if
    <math|<with|math-font|Euler|M>,(a,A)\<Vdash\>\<ominus\>\<circlearrowleft\>>
    then <math|<with|math-font|Euler|M>,(a,A)\<nVdash\>\<circlearrowleft\>>.
  </proof>

  <subsubsection|Negative Doxastic Introspection>
</body>

<\initial>
  <\collection>
    <associate|language|american>
    <associate|page-type|letter>
    <associate|sfactor|3>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|?>>
    <associate|auto-2|<tuple|1.1|?>>
    <associate|auto-3|<tuple|1.2|?>>
  </collection>
</references>