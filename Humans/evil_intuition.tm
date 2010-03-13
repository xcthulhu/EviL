<TeXmacs|1.0.7.2>

<style|generic>

<\body>
  In this section, I shall illustrate how I intuitively read the operators in
  <with|font-shape|small-caps|EviL>, and provide a number of validities.

  As per the traditional doxastic reading of <math|\<box\>\<phi\>>, I read
  this as asserting ``The <with|font-shape|small-caps|EviL> believes
  <math|\<phi\>>''. \ Because of Theorem (FIXME), the Theorem Theorem, I
  shall freely conflate this with the assertion ``The
  <with|font-shape|small-caps|EviL> agent has an argument for
  <math|\<phi\>>,'' which I take to be a proof.

  My intuition for how to read <math|\<langle\>-\<rangle\>\<phi\>> was first
  mentioned in Ÿ(FIXME) with respect to Descartes' Meditation II -- it means
  ``If the <with|font-shape|small-caps|EviL> agent were to set aside some of
  her beliefs, or cast some of her beliefs into doubt, then <math|\<phi\>>
  would hold.'' \ Dually, I tend to read <math|\<boxminus\>\<phi\>> as saying
  something like ``For all the ways that the
  <with|font-shape|small-caps|EviL> agent might use her imagination,
  <math|\<phi\>> holds.'' \ I recognize that these interpretations might seem
  inconsistent -- however, I regard casting beliefs into doubt and embracing
  one's imagination as part of the same coin. \ For, naturally, when one
  doubts more thing, more things start to appear possible. \ If I set aside,
  for a second, the belief that\ 

  <htab|5mm>the law of gravity is an exceptionless regularity of the
  universe<htab|5mm><math|(g)>

  <math|\<ldots\>>then it seems natural to imagine that

  <htab|5mm>a propulsion device exploiting this exceptions to the law of
  gravitation might be constructable.<htab|5mm><math|(p)>

  In the symbology of <with|font-shape|small-caps|EviL> formulae, I would
  code this intuition as

  <\equation*>
    \<boxminus\>(\<box\>g \<rightarrow\>\<diamondsuit\>p).
  </equation*>

  To give another example, if I pretend that it isn't the case that:

  <htab|5mm>the canals of Amsterdam are filthy<htab|5mm><math|(f)>

  I might be able to imagine a scenario where

  <htab|5mm>I am swimming comfortably in the Amstel river<htab|5mm><math|(r)>

  But not really. \ I really can't really swim comfortably in Amstel, not
  just because it has tons of garbage, but also because\ 

  <htab|5mm>I don't a bathing suit,<htab|5mm><math|(b)>

  Frankly, I am not so bold that I could go skinny dipping in Amstel without
  that being awkward. \ Hence I would say in the language of
  <with|font-shape|small-caps|EviL> that:

  <\equation*>
    \<neg\>\<boxminus\>(\<box\>f\<rightarrow\>\<diamondsuit\>r)
  </equation*>

  This is because I can cast into doubt the assumption of the filthiness of
  the canals of Amsterdam, while still retaining my belief that I don't have
  a bathingsuit, so swimming in Amstel would still be awkward for me. \ In
  symbols, I would write express this sentiment as the following expression:

  <\equation*>
    \<langle\>-\<rangle\>(\<diamondsuit\>f\<wedge\>\<box\>b\<wedge\>\<neg\>\<diamondsuit\>r)
  </equation*>

  Further, my intuition for how to read <math|\<langle\>+\<rangle\>\<phi\>>
  is ``If the <with|font-shape|small-caps|EviL> agent were to remember
  something, then <math|\<phi\>> would hold.'' \ For instance, I can think of
  an instance where I woke up and searched myself for my bike keys. \ To my
  horror, they weren't there -- in I immediately assumed that I might have
  left my keys in the lock on my bike, and figured there was a fair
  likelihood that

  <htab|5mm>my bike has been stolen because I left the keys in
  it.<htab|5mm><math|(s)>

  But once I recalled that\ 

  <htab|5mm>I had lent my bike to a friend,<htab|5mm><math|(l)>

  <math|\<ldots\>>my fear subsided. \ I would have said that prior to
  remembering, while I thought it might be possible that my bike was stolen
  due to my negligence, if I remembered what I had done then I no longer
  would have entertained that possibility. \ I would express this observation
  as:

  <\equation*>
    \<diamondsuit\>s\<wedge\>\<boxplus\>(\<box\>l\<rightarrow\>\<box\>\<neg\>s)
  </equation*>

  I consider <math|\<boxminus\>> and <math|\<boxplus\>> to be inverse
  modalities of each other, in exactly the same way that
  <with|font-shape|italic|past> and <with|font-shape|italic|future> are
  inverse modalities in temporal logic. This is perhaps a little unusual; it
  is arguably more natural to think of <with|font-shape|italic|forgetting> as
  the inverse modality of remembering, and there doesn't appear to be an
  natural inverse operation corresponding to casting into doubt. \ Following
  the idea of the <with|font-shape|italic|web of belief> due to Quine, as
  presented in Ÿ(FIXME), I would extend a position asserting that remembering
  factive data is the same as embracing as much of one's evidence as
  possible.

  In terms of the semantics outlined, <math|\<boxminus\>> corresponds to a
  subsetset relation while <math|\<boxplus\>> corresponds to a superset
  relation. \ Because of this, I sometimes read <math|\<boxminus\>\<phi\>>
  closer to the formal semantics, as saying something like ``for all subsets
  of the agent's beliefs, <math|\<phi\>> holds'' and dually for
  <math|\<boxplus\>\<phi\>>. \ This is admittedly even less natural than the
  reading of remembering as the opposite of casting into doubt. \ So be it; I
  am comfortable with <with|font-shape|small-caps|EviL> agents being at best
  twisted cartoon versions of actual people, who actually have minds and
  engage in remembering, imagining, and other similar activities. \ After
  all, according to the semantics stipulated in Ÿ(FIXME),
  <with|font-shape|small-caps|EviL> agents apparently have sets for brains,
  which makes an <with|font-shape|small-caps|EviL> agent a strange effigy for
  a person indeed -- with possible exception of set theorists.
</body>

<\initial>
  <\collection>
    <associate|language|american>
    <associate|page-type|letter>
  </collection>
</initial>