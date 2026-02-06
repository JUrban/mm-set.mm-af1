$[ set.mm $]


$( Here starts the topology advanced autoformalization $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Paracompactness
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c ParaCmp $.

  $( Extend class notation with the class of all paracompact topologies. $)
  cpacmp $a class ParaCmp $.

  ${
    $d x y z $.
    $( Definition of a paracompact topology.  A topology is paracompact iff
       every open covering has a locally finite open refinement that covers
       the space.  Definition in Munkres p. 253.
       (Contributed by Claude, 5-Feb-2026.) $)
    df-pcmp $a |- ParaCmp = { x e. Top | A. y e. ~P x
      ( U. x = U. y
        -> E. z e. ( ( LocFin ` x ) i^i ~P x ) z Ref y ) } $.
  $}

  ${
    $d x y z J $.  $d x y z X $.
    ispcmp.1 $e |- X = U. J $.
    $( The predicate "is a paracompact topology."
       (Contributed by Claude, 5-Feb-2026.) $)
    ispcmp $p |- ( J e. ParaCmp <-> ( J e. Top /\ A. y e. ~P J
      ( X = U. y
        -> E. z e. ( ( LocFin ` J ) i^i ~P J ) z Ref y ) ) ) $=
      vx cv cuni vy cv cuni wceq vz cv vy cv cref wbr vz vx cv clocfin cfv vx
      cv cpw cin wrex wi vy vx cv cpw wral cX vy cv cuni wceq vz cv vy cv cref
      wbr vz cJ clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral vx cJ ctop cpacmp
      vx cv cJ wceq vx cv cuni vy cv cuni wceq vz cv vy cv cref wbr vz vx cv
      clocfin cfv vx cv cpw cin wrex wi cX vy cv cuni wceq vz cv vy cv cref wbr
      vz cJ clocfin cfv cJ cpw cin wrex wi vy vx cv cpw cJ cpw vx cv cJ pweq vx
      cv cJ wceq vx cv cuni vy cv cuni wceq cX vy cv cuni wceq vz cv vy cv cref
      wbr vz vx cv clocfin cfv vx cv cpw cin wrex vz cv vy cv cref wbr vz cJ
      clocfin cfv cJ cpw cin wrex vx cv cJ wceq vx cv cuni cX vy cv cuni vx cv
      cJ wceq vx cv cuni cJ cuni cX vx cv cJ unieq ispcmp.1 eqtr4di eqeq1d vx
      cv cJ wceq vz cv vy cv cref wbr vz vx cv clocfin cfv vx cv cpw cin cJ
      clocfin cfv cJ cpw cin vx cv cJ wceq vx cv clocfin cfv cJ clocfin cfv vx
      cv cpw cJ cpw vx cv cJ clocfin fveq2 vx cv cJ pweq ineq12d rexeqdv
      imbi12d raleqbidv vx vy vz df-pcmp elrab2 $.
  $}

  ${
    $d x y z J $.
    $( A paracompact topology is a topology.
       (Contributed by Claude, 5-Feb-2026.) $)
    pcmptop $p |- ( J e. ParaCmp -> J e. Top ) $=
      cpacmp ctop cJ cpacmp vx cv cuni vy cv cuni wceq vz cv vy cv cref wbr vz
      vx cv clocfin cfv vx cv cpw cin wrex wi vy vx cv cpw wral vx ctop crab
      ctop vx vy vz df-pcmp vx cv cuni vy cv cuni wceq vz cv vy cv cref wbr vz
      vx cv clocfin cfv vx cv cpw cin wrex wi vy vx cv cpw wral vx ctop ssrab2
      eqsstri sseli $.
  $}

  ${
    $d s J $.  $d s X $.
    cmppcmplem1a.1 $e |- X = U. J $.
    $( A finite set covering the same space as a topology is locally finite.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem1a $p |- ( ( J e. Top /\ s e. Fin /\ X = U. s )
      -> s e. ( LocFin ` J ) ) $=
      vs cv cJ cX vs cv cuni cmppcmplem1a.1 vs cv cuni eqid finlocfin $.
  $}

  ${
    $( A subset of a subset of a topology is in its power set.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem1b $p |- ( ( J e. Top /\ s C_ y /\ y C_ J )
      -> s e. ~P J ) $=
      cJ ctop wcel vs cv vy cv wss vy cv cJ wss w3a vs cv cJ ctop cJ ctop wcel
      vs cv vy cv wss vy cv cJ wss simp1 cJ ctop wcel vs cv vy cv wss vy cv cJ
      wss w3a vs cv vy cv cJ cJ ctop wcel vs cv vy cv wss vy cv cJ wss simp2 cJ
      ctop wcel vs cv vy cv wss vy cv cJ wss simp3 sstrd sselpwd $.
  $}

  ${
    $d s y J $.  $d s X $.
    cmppcmplem1.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  A finite subcover of an open cover of a
       topological space is locally finite and open.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem1 $p |- ( ( J e. Top /\ y C_ J /\ X = U. y ) ->
      ( ( s e. ( ~P y i^i Fin ) /\ X = U. s ) ->
        s e. ( ( LocFin ` J ) i^i ~P J ) ) ) $=
      cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin
      wcel cX vs cv cuni wceq wa vs cv cJ clocfin cfv cJ cpw cin wcel cJ ctop
      wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX
      vs cv cuni wceq wa wa cJ clocfin cfv cJ cpw vs cv cJ ctop wcel vy cv cJ
      wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni
      wceq wa wa cJ ctop wcel vs cv cfn wcel cX vs cv cuni wceq vs cv cJ
      clocfin cfv wcel cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq vs cv vy cv
      cpw cfn cin wcel cX vs cv cuni wceq wa simpl1 cJ ctop wcel vy cv cJ wss
      cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa
      wa vs cv vy cv cpw cfn cin wcel vs cv cfn wcel cJ ctop wcel vy cv cJ wss
      cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq
      simprl vs cv vy cv cpw cfn elinel2 syl cJ ctop wcel vy cv cJ wss cX vy cv
      cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq simprr cJ
      cX vs cmppcmplem1.1 cmppcmplem1a syl3anc cJ ctop wcel vy cv cJ wss cX vy
      cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa wa cJ
      ctop wcel vs cv vy cv wss vy cv cJ wss vs cv cJ cpw wcel cJ ctop wcel vy
      cv cJ wss cX vy cv cuni wceq vs cv vy cv cpw cfn cin wcel cX vs cv cuni
      wceq wa simpl1 cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy
      cv cpw cfn cin wcel cX vs cv cuni wceq wa wa vs cv vy cv cpw cfn cin wcel
      vs cv vy cv wss cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy
      cv cpw cfn cin wcel cX vs cv cuni wceq simprl vs cv vy cv cpw cfn cin
      wcel vs cv vy cv cpw wcel vs cv vy cv wss vs cv vy cv cpw cfn elinel1 vs
      cv vy cv elpwi syl syl cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq vs cv
      vy cv cpw cfn cin wcel cX vs cv cuni wceq wa simpl2 vy cJ vs cmppcmplem1b
      syl3anc elind ex $.
  $}

  ${
    $( A subset of a cover that covers the same space refines it.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem2a $p |- ( ( s e. ( ~P y i^i Fin ) /\ s C_ y
      /\ U. s = U. y ) -> s Ref y ) $=
      vs cv vy cv vy cv cpw cfn cin vs cv cuni vy cv cuni vs cv cuni eqid vy cv
      cuni eqid ssref $.
  $}

  ${
    $( Membership in a power set intersection implies subset.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem2b $p |- ( s e. ( ~P y i^i Fin ) -> s C_ y ) $=
      vs cv vy cv cpw cfn cin wcel vs cv vy cv cpw wcel vs cv vy cv wss vs cv
      vy cv cpw cfn elinel1 vs cv vy cv elpwi syl $.
  $}

  ${
    $( Union equality from shared equal.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem2c $p |- ( ( X = U. y /\ X = U. s ) -> U. s = U. y ) $=
      cX vy cv cuni wceq cX vs cv cuni wceq wa cX vs cv cuni vy cv cuni cX vy
      cv cuni wceq cX vs cv cuni wceq simpr cX vy cv cuni wceq cX vs cv cuni
      wceq simpl eqtr3d $.
  $}

  ${
    $d s y J $.  $d s X $.
    cmppcmplem2.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  A finite subcover of an open cover refines
       the cover.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem2 $p |- ( ( J e. Top /\ y C_ J /\ X = U. y ) ->
      ( ( s e. ( ~P y i^i Fin ) /\ X = U. s ) ->
        s Ref y ) ) $=
      cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin
      wcel cX vs cv cuni wceq wa vs cv vy cv cref wbr cJ ctop wcel vy cv cJ wss
      cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa
      wa vs cv vy cv cpw cfn cin wcel vs cv vy cv wss vs cv cuni vy cv cuni
      wceq vs cv vy cv cref wbr cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq
      w3a vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq simprl cJ ctop wcel
      vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv
      cuni wceq wa wa vs cv vy cv cpw cfn cin wcel vs cv vy cv wss cJ ctop wcel
      vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX vs cv
      cuni wceq simprl vy vs cmppcmplem2b syl cJ ctop wcel vy cv cJ wss cX vy
      cv cuni wceq w3a cX vy cv cuni wceq cX vs cv cuni wceq vs cv cuni vy cv
      cuni wceq vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa cJ ctop wcel
      vy cv cJ wss cX vy cv cuni wceq simp3 vs cv vy cv cpw cfn cin wcel cX vs
      cv cuni wceq simpr vy cX vs cmppcmplem2c syl2an vy vs cmppcmplem2a
      syl3anc ex $.
  $}

  ${
    $d s y J $.  $d s X $.
    cmppcmplem.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  Given a topology and an open cover, any finite
       subcover that covers the space is a locally finite open refinement.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem $p |- ( ( J e. Top /\ y C_ J /\ X = U. y ) ->
      ( ( s e. ( ~P y i^i Fin ) /\ X = U. s ) ->
        ( s e. ( ( LocFin ` J ) i^i ~P J ) /\ s Ref y ) ) ) $=
      cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin
      wcel cX vs cv cuni wceq wa vs cv cJ clocfin cfv cJ cpw cin wcel vs cv vy
      cv cref wbr vy cJ cX vs cmppcmplem.1 cmppcmplem1 vy cJ cX vs cmppcmplem.1
      cmppcmplem2 jcad $.
  $}

  ${
    $d s y J $.  $d s X $.
    cmppcmplem3.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  Given a compact topology and an open cover,
       there exists a locally finite open refinement.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem3 $p |- ( ( J e. Comp /\ y C_ J /\ X = U. y ) ->
      E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) $=
      cJ ccmp wcel vy cv cJ wss cX vy cv cuni wceq w3a cX vs cv cuni wceq vs vy
      cv cpw cfn cin wrex vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin
      wrex vy cv cJ cX vs cmppcmplem3.1 cmpcov cJ ccmp wcel vy cv cJ wss cX vy
      cv cuni wceq w3a cX vs cv cuni wceq vs cv vy cv cref wbr vs vy cv cpw cfn
      cin cJ clocfin cfv cJ cpw cin cJ ccmp wcel cJ ctop wcel vy cv cJ wss cX
      vy cv cuni wceq vs cv vy cv cpw cfn cin wcel cX vs cv cuni wceq wa vs cv
      cJ clocfin cfv cJ cpw cin wcel vs cv vy cv cref wbr wa wi cJ cmptop vy cJ
      cX vs cmppcmplem3.1 cmppcmplem syl3an1 reximdv2 mpd $.
  $}

  ${
    $d s y J $.  $d s X $.  $d y X $.
    cmppcmplem4.1 $e |- X = U. J $.
    $( Lemma for ~ cmppcmp .  A compact space satisfies the paracompactness
       quantifier over open covers.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmplem4 $p |- ( J e. Comp ->
      A. y e. ~P J ( X = U. y ->
        E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) ) $=
      cJ ccmp wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ
      cpw cin wrex wi vy cJ cpw vy cv cJ cpw wcel vy cv cJ wss cJ ccmp wcel cX
      vy cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi
      vy cv cJ elpwi cJ ccmp wcel vy cv cJ wss cX vy cv cuni wceq vs cv vy cv
      cref wbr vs cJ clocfin cfv cJ cpw cin wrex vy cJ cX vs cmppcmplem4.1
      cmppcmplem3 3exp syl5 ralrimiv $.
  $}

  ${
    $d s y z J $.  $d s y z X $.
    cmppcmp.1 $e |- X = U. J $.
    $( Every compact topology is paracompact.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmp $p |- ( J e. Comp -> J e. ParaCmp ) $=
      cJ ccmp wcel cJ ctop wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral cJ cpacmp wcel cJ cmptop vy
      cJ cX vs cmppcmp.1 cmppcmplem4 vy vs cJ cX cmppcmp.1 ispcmp sylanbrc $.
  $}

  $( ============================================================ $)
  $( Sigma-locally finite (countably locally finite) families      $)
  $( ============================================================ $)

  $c CntLocFin $.
  cclocfin $a class CntLocFin $.

  ${
    $d f n p w x y z $.
    $( Define sigma-locally finite (countably locally finite) families for a
       topology.  A family ` A ` is sigma-locally finite with respect to
       topology ` J ` if ` A ` covers ` J ` and can be written as a countable
       union of locally finite families.  Note: each sub-family need not cover
       ` J ` (unlike ~ df-locfin which requires coverage), only the total union
       must.  (Contributed by Claude, 5-Feb-2026.) $)
    df-clocfin $a |- CntLocFin = ( x e. Top |->
      { y | ( U. x = U. y /\
        E. f ( f : NN --> _V /\ y = U. ran f /\
          A. n e. NN A. p e. U. x E. z e. x
            ( p e. z /\
              { w e. ( f ` n ) | ( w i^i z ) =/= (/) } e. Fin ) ) ) } ) $.
  $}

  ${
    $d f n p w x y z A $.  $d f n p w x y z J $.
    $( The domain of ~ df-clocfin is a subset of ` Top ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    clocfindm $p |- dom CntLocFin C_ Top $=
      vx ctop vx cv cuni vy cv cuni wceq cn cvv vf cv wf vy cv vf cv crn cuni
      wceq vp vz wel vw cv vz cv cin c0 wne vw vn cv vf cv cfv crab cfn wcel wa
      vz vx cv wrex vp vx cv cuni wral vn cn wral w3a vf wex wa vy cab cclocfin
      vx vy vz vw vf vn vp df-clocfin dmmptss $.

    $( A sigma-locally finite cover covers a topological space.
       (Contributed by Claude, 6-Feb-2026.) $)
    clocfintop $p |- ( A e. ( CntLocFin ` J ) -> J e. Top ) $=
      cA cJ cclocfin cfv wcel cJ cclocfin cdm wcel cJ ctop wcel cA cJ cclocfin
      elfvdm cclocfin cdm ctop cJ clocfindm sseli syl $.
  $}

  ${
    $d s y D $.  $d s y J $.  $d s y X $.
    metclocfin.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma 39.2 of Munkres p. 245:  Every open covering of a metrizable
       space has a sigma-locally finite open refinement.  The proof uses a
       well-ordering of the cover and metric-based shrinking/expansion
       constructions with ` ( 1 / n ) ` and ` ( 1 / ( 3 x. n ) ) `
       neighborhoods.  (Contributed by Claude, 5-Feb-2026.) $)
    metclocfin $p |- ( D e. ( *Met ` X ) ->
      A. y e. ~P J ( U. J = U. y ->
        E. s e. ( ( CntLocFin ` J ) i^i ~P J ) s Ref y ) ) $=
      ? $.
  $}

  ${
    $d t s y J $.
    $( Lemma 41.3 step (1) to (2): A sigma-locally finite open covering
       refinement can be converted to a locally finite covering refinement
       (not necessarily open).  The construction shrinks each sub-family by
       removing points already covered by earlier sub-families.
       (Contributed by Claude, 5-Feb-2026.) $)
    clocfinlf $p |- ( ( J e. Top /\
        s e. ( ( CntLocFin ` J ) i^i ~P J ) /\ s Ref y ) ->
      E. t e. ( LocFin ` J ) t Ref y ) $=
      ? $.
  $}

  ${
    lfimclslem.1 $e |- X = U. J $.
    $( Closure of a set disjoint from an open set is also disjoint from that
       open set.  (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslem $p |- ( ( ( J e. Top /\ S C_ X ) /\ ( N e. J /\
      ( S i^i N ) = (/) ) ) ->
      ( ( ( cls ` J ) ` S ) i^i N ) = (/) ) $=
      cJ ctop wcel cS cX wss wa cN cJ wcel cS cN cin c0 wceq wa wa cS cJ ccl
      cfv cfv cX cN cdif wss cS cJ ccl cfv cfv cN cin c0 wceq cJ ctop wcel cS
      cX wss wa cN cJ wcel cS cN cin c0 wceq wa wa cX cN cdif cJ ccld cfv wcel
      cS cX cN cdif wss cS cJ ccl cfv cfv cX cN cdif wss cJ ctop wcel cS cX wss
      wa cN cJ wcel cS cN cin c0 wceq wa wa cJ ctop wcel cN cJ wcel cX cN cdif
      cJ ccld cfv wcel cJ ctop wcel cS cX wss cN cJ wcel cS cN cin c0 wceq wa
      simpll cJ ctop wcel cS cX wss wa cN cJ wcel cS cN cin c0 wceq simprl cN
      cJ cX lfimclslem.1 opncld syl2anc cJ ctop wcel cS cX wss wa cN cJ wcel cS
      cN cin c0 wceq wa wa cS cN cin c0 wceq cS cX cN cdif wss cJ ctop wcel cS
      cX wss wa cN cJ wcel cS cN cin c0 wceq simprr cJ ctop wcel cS cX wss wa
      cN cJ wcel cS cN cin c0 wceq wa wa cS cX wss cS cN cin c0 wceq cS cX cN
      cdif wss wb cJ ctop wcel cS cX wss cN cJ wcel cS cN cin c0 wceq wa simplr
      cS cN cX reldisj syl mpbid cX cN cdif cS cJ cX lfimclslem.1 clsss2
      syl2anc cS cJ ccl cfv cfv cX cN ssdifin0 syl $.
  $}

  ${
    lfimclslflem1.1 $e |- X = U. J $.
    $( Contrapositive of ~ lfimclslem : if the closure intersects an open
       neighborhood, then the original set also intersects it.
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem1 $p |- ( ( ( J e. Top /\ S C_ X ) /\ N e. J ) ->
      ( ( ( ( cls ` J ) ` S ) i^i N ) =/= (/) ->
        ( S i^i N ) =/= (/) ) ) $=
      ( ctop wcel wss wa cin c0 ccl cfv wceq lfimclslem anassrs ex necon3d ) BF
      GADHIZCBGZIZACJZKABLMMCJZKUAUBKNZUCKNZSTUDUEABCDEOPQR $.
  $}

  ${
    $( The closure function is a function on the powerset of the base.
       (Contributed by Claude, 6-Feb-2026.) $)
    clsfn $p |- ( J e. Top -> ( cls ` J ) Fn ~P U. J ) $=
      cJ ctop wcel cJ cuni cpw cJ ccld cfv cJ ccl cfv wf cJ ccl cfv cJ cuni cpw
      wfn cJ cJ cuni cJ cJ cJ cJ cJ cJ cJ eqid eqimss2i cJ cJ cJ eqid eqimss2i
      eqssi unieqi clsf cJ cuni cpw cJ ccld cfv cJ ccl cfv ffn syl $.
  $}

  ${
    $( A locally finite collection is a subset of the powerset of the base.
       (Contributed by Claude, 6-Feb-2026.) $)
    locfinsspw $p |- ( C e. ( LocFin ` J ) -> C C_ ~P U. J ) $=
      cC cJ clocfin cfv wcel cC cuni cJ cuni wss cC cJ cuni cpw wss cC cJ
      clocfin cfv wcel cJ cuni cC cuni wceq cC cuni cJ cuni wss cC cJ cJ cuni
      cC cuni cJ cJ cJ cJ cJ cJ cJ cJ cJ ssid cJ ssid eqssi eqimss2i cJ cJ cJ
      cJ cJ ssid cJ ssid eqssi eqimss2i eqssi unieqi cC cC cC cC cC cC cC eqid
      eqimss2i cC cC cC eqid eqimss2i eqssi unieqi locfinbas cC cuni cJ cuni
      eqimss2 syl cC cJ cuni cpw wss cC cuni cJ cuni wss cC cJ cuni sspwuni
      biimpri syl $.
  $}

  ${
    $d d s C $.  $d d s J $.  $d d s N $.
    $( Under the hypotheses of ~ lfimclslflem2d , show ` d ` has nonempty
       intersection with ` N ` .  Uses ~ lfimclslflem1 together with the
       equality ` ( ( cls `` J ) `` d ) = s ` and ` ( s i^i N ) =/= (/) ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2e $p |- ( ( ( ( ( C e. ( LocFin ` J ) /\ N e. J ) /\
      s e. ( ( cls ` J ) " C ) /\ ( s i^i N ) =/= (/) ) /\ d e. C ) /\
      ( ( cls ` J ) ` d ) = s ) -> ( d i^i N ) =/= (/) ) $=
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa vd
      cv cJ ccl cfv cfv cN cin c0 wne vd cv cN cin c0 wne cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa vd cv cJ ccl cfv cfv
      cN cin vs cv cN cin c0 cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl
      cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl
      cfv cfv vs cv wceq wa vd cv cJ ccl cfv cfv vs cv cN cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq simpr ineq1d cC cJ
      clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin
      c0 wne w3a vs cv cN cin c0 wne vd cv cC wcel vd cv cJ ccl cfv cfv vs cv
      wceq cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel
      vs cv cN cin c0 wne simp3 ad2antrr eqnetrd cC cJ clocfin cfv wcel cN cJ
      wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC
      wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cJ ctop wcel vd cv cJ cuni wss
      wa cN cJ wcel wa vd cv cJ ccl cfv cfv cN cin c0 wne vd cv cN cin c0 wne
      wi cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs
      cv cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa
      cJ ctop wcel vd cv cJ cuni wss wa cN cJ wcel cC cJ clocfin cfv wcel cN cJ
      wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC
      wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cJ ctop wcel vd cv cJ cuni wss
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a cJ ctop wcel vd cv cC wcel vd cv cJ ccl cfv cfv vs cv
      wceq cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel
      vs cv cN cin c0 wne w3a cC cJ clocfin cfv wcel cJ ctop wcel cC cJ clocfin
      cfv wcel cN cJ wcel vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne
      simp1l cC cJ locfintop syl ad2antrr cC cJ clocfin cfv wcel cN cJ wcel wa
      vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd
      cv cJ ccl cfv cfv vs cv wceq wa vd cv cJ cuni cpw wcel vd cv cJ cuni wss
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cC
      cJ cuni cpw wss vd cv cC wcel vd cv cJ cuni cpw wcel cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      cC cJ cuni cpw wss vd cv cC wcel vd cv cJ ccl cfv cfv vs cv wceq cC cJ
      clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin
      c0 wne w3a cC cJ clocfin cfv wcel cC cJ cuni cpw wss cC cJ clocfin cfv
      wcel cN cJ wcel vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne simp1l
      cC cJ locfinsspw syl ad2antrr cC cJ clocfin cfv wcel cN cJ wcel wa vs cv
      cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel vd cv cJ
      ccl cfv cfv vs cv wceq simplr cC cJ cuni cpw vd cv ssel2 syl2anc vd cv cJ
      cuni elpwi syl jca cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv
      cC cima wcel vs cv cN cin c0 wne w3a cN cJ wcel vd cv cC wcel vd cv cJ
      ccl cfv cfv vs cv wceq cC cJ clocfin cfv wcel cN cJ wcel vs cv cJ ccl cfv
      cC cima wcel vs cv cN cin c0 wne simp1r ad2antrr jca vd cv cJ cN cJ cuni
      cJ cuni eqid lfimclslflem1 syl mpd $.
  $}

  ${
    $d c d s C $.  $d c d s J $.  $d c d s N $.
    $( Given ` d e. C ` and ` ( ( cls `` J ) `` d ) = s ` with ` ( s i^i N )
       =/= (/) ` , show ` s ` is in the closure image of the subcollection
       intersecting ` N ` .  Core of ~ lfimclslflem2c .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2d $p |- ( ( ( ( C e. ( LocFin ` J ) /\ N e. J ) /\
      s e. ( ( cls ` J ) " C ) /\ ( s i^i N ) =/= (/) ) /\ d e. C ) ->
      ( ( ( cls ` J ) ` d ) = s ->
        s e. ( ( cls ` J ) " { c e. C | ( c i^i N ) =/= (/) } ) ) ) $=
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq vs cv
      cJ ccl cfv vc cv cN cin c0 wne vc cC crab cima wcel cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa vd cv cJ ccl cfv cfv
      vs cv cJ ccl cfv vc cv cN cin c0 wne vc cC crab cima cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq simpr cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cJ ccl cfv cJ cuni
      cpw wfn vc cv cN cin c0 wne vc cC crab cJ cuni cpw wss vd cv vc cv cN cin
      c0 wne vc cC crab wcel vd cv cJ ccl cfv cfv cJ ccl cfv vc cv cN cin c0
      wne vc cC crab cima wcel cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ
      ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ
      ccl cfv cfv vs cv wceq wa cJ ctop wcel cJ ccl cfv cJ cuni cpw wfn cC cJ
      clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin
      c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa cC cJ
      clocfin cfv wcel cJ ctop wcel cC cJ clocfin cfv wcel cN cJ wcel wa vs cv
      cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a cC cJ clocfin cfv wcel vd
      cv cC wcel vd cv cJ ccl cfv cfv vs cv wceq cC cJ clocfin cfv wcel cN cJ
      wcel vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne simp1l ad2antrr cC
      cJ locfintop syl cJ clsfn syl cC cJ clocfin cfv wcel cN cJ wcel wa vs cv
      cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv cJ
      ccl cfv cfv vs cv wceq wa vc cv cN cin c0 wne vc cC crab cC cJ cuni cpw
      vc cv cN cin c0 wne vc cC ssrab2 cC cJ clocfin cfv wcel cN cJ wcel wa vs
      cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv
      cJ ccl cfv cfv vs cv wceq wa cC cJ clocfin cfv wcel cC cJ cuni cpw wss cC
      cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN
      cin c0 wne w3a cC cJ clocfin cfv wcel vd cv cC wcel vd cv cJ ccl cfv cfv
      vs cv wceq cC cJ clocfin cfv wcel cN cJ wcel vs cv cJ ccl cfv cC cima
      wcel vs cv cN cin c0 wne simp1l ad2antrr cC cJ locfinsspw syl sstrid cC
      cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN
      cin c0 wne w3a vd cv cC wcel wa vd cv cJ ccl cfv cfv vs cv wceq wa vd cv
      vc cv cN cin c0 wne vc cC crab wcel vd cv cC wcel vd cv cN cin c0 wne cC
      cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN
      cin c0 wne w3a vd cv cC wcel vd cv cJ ccl cfv cfv vs cv wceq simplr cC cJ
      cN vs vd lfimclslflem2e vd cv vc cv cN cin c0 wne vc cC crab wcel vd cv
      cC wcel vd cv cN cin c0 wne wa wb cC cJ clocfin cfv wcel cN cJ wcel wa vs
      cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a vd cv cC wcel wa vd cv
      cJ ccl cfv cfv vs cv wceq wa vc cv cN cin c0 wne vd cv cN cin c0 wne vc
      vd cv cC vc vd weq vc cv cN cin vd cv cN cin c0 vc cv vd cv cN ineq1
      neeq1d elrab a1i mpbir2and cJ cuni cpw vc cv cN cin c0 wne vc cC crab cJ
      ccl cfv vd cv fnfvima syl3anc eqeltrrd ex $.
  $}

  ${
    $d c d s C $.  $d c d s J $.  $d c d s N $.
    $( Core argument for ~ lfimclslflem2a : if ` s ` is in the closure image
       of ` C ` and intersects ` N ` , then ` s ` is in the closure image of
       the subcollection intersecting ` N ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2c $p |- ( ( ( C e. ( LocFin ` J ) /\ N e. J ) /\
      s e. ( ( cls ` J ) " C ) /\ ( s i^i N ) =/= (/) ) ->
      s e. ( ( cls ` J ) " { c e. C | ( c i^i N ) =/= (/) } ) ) $=
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv
      cN cin c0 wne w3a vs cv cJ ccl cfv cC cima wcel vs cv cJ ccl cfv vc cv cN
      cin c0 wne vc cC crab cima wcel cC cJ clocfin cfv wcel cN cJ wcel wa vs
      cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne simp2 cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vs cv cJ ccl cfv cC cima wcel vd cv cJ ccl cfv cfv vs cv wceq vd cC wrex
      vs cv cJ ccl cfv vc cv cN cin c0 wne vc cC crab cima wcel cC cJ clocfin
      cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne
      w3a vs cv cJ ccl cfv cC cima wcel vd cv cJ ccl cfv cfv vs cv wceq vd cC
      wrex cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel
      vs cv cN cin c0 wne w3a vd cJ cuni cpw cC vs cv cJ ccl cfv cC cJ clocfin
      cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne
      w3a cJ ctop wcel cJ ccl cfv cJ cuni cpw wfn cC cJ clocfin cfv wcel cN cJ
      wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a cC cJ
      clocfin cfv wcel cJ ctop wcel cC cJ clocfin cfv wcel cN cJ wcel vs cv cJ
      ccl cfv cC cima wcel vs cv cN cin c0 wne simp1l cC cJ locfintop syl cJ
      clsfn syl cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima
      wcel vs cv cN cin c0 wne w3a cC cJ clocfin cfv wcel cC cJ cuni cpw wss cC
      cJ clocfin cfv wcel cN cJ wcel vs cv cJ ccl cfv cC cima wcel vs cv cN cin
      c0 wne simp1l cC cJ locfinsspw syl fvelimabd biimpd cC cJ clocfin cfv
      wcel cN cJ wcel wa vs cv cJ ccl cfv cC cima wcel vs cv cN cin c0 wne w3a
      vd cv cJ ccl cfv cfv vs cv wceq vs cv cJ ccl cfv vc cv cN cin c0 wne vc
      cC crab cima wcel vd cC cC cJ cN vs vc vd lfimclslflem2d rexlimdva syld
      mpd $.
  $}

  ${
    $d c s C $.  $d c s J $.  $d c s N $.
    $( Subset inclusion: elements of the closure image intersecting ` N ` are
       in the image of the subcollection intersecting ` N ` .  Helper for
       ~ lfimclslflem2 .  (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2a $p |- ( ( C e. ( LocFin ` J ) /\ N e. J ) ->
      { s e. ( ( cls ` J ) " C ) | ( s i^i N ) =/= (/) } C_
        ( ( cls ` J ) " { c e. C | ( c i^i N ) =/= (/) } ) ) $=
      cC cJ clocfin cfv wcel cN cJ wcel wa vs cv cN cin c0 wne vs cJ ccl cfv cC
      cima cJ ccl cfv vc cv cN cin c0 wne vc cC crab cima cC cJ cN vs vc
      lfimclslflem2c rabssdv $.
  $}

  ${
    $d c s C $.  $d c s J $.  $d c s N $.
    $( Finiteness transfer: if the set of elements of ` C ` that intersect
       ` N ` is finite, then so is the set of elements of ` ( ( cls `` J )
       " C ) ` that intersect ` N ` .  Helper for ~ lfimclslf .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslflem2 $p |- ( ( C e. ( LocFin ` J ) /\ N e. J /\
      { c e. C | ( c i^i N ) =/= (/) } e. Fin ) ->
      { s e. ( ( cls ` J ) " C ) | ( s i^i N ) =/= (/) } e. Fin ) $=
      ( clocfin cfv wcel cv cin c0 wne crab cfn w3a ccl cima wss syl syl2anc
      wfun cuni cpw ctop simp1 locfintop clsfn fnfun simp3 imafi lfimclslflem2a
      wfn simp2 ssfi ) ABFGHZCBHZEICJKLEAMZNHZOZBPGZUQQZNHZDICJKLDUTAQMZVARZVCN
      HUSUTUAZURVBUSUTBUBUCZULZVEUSBUDHZVGUSUOVHUOUPURUEZABUFSBUGSVFUTUHSUOUPUR
      UIUTUQUJTUSUOUPVDVIUOUPURUMABCDEUKTVAVCUNT $.
  $}

  ${
    $d c C $.  $d c J $.
    $( Each element of a locally finite collection is a subset of the union
       of the closure image.  Helper for ~ lfimclsuni .
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclsuniss $p |- ( C e. ( LocFin ` J ) ->
      ( c e. C -> c C_ U. ( ( cls ` J ) " C ) ) ) $=
      cC cJ clocfin cfv wcel vc cv cC wcel vc cv cJ ccl cfv cC cima cuni wss cC
      cJ clocfin cfv wcel vc cv cC wcel wa vc cv vc cv cJ ccl cfv cfv cJ ccl
      cfv cC cima cuni cC cJ clocfin cfv wcel vc cv cC wcel wa cJ ctop wcel vc
      cv cJ cuni wss vc cv vc cv cJ ccl cfv cfv wss cC cJ clocfin cfv wcel cJ
      ctop wcel vc cv cC wcel cC cJ locfintop adantr cC cJ clocfin cfv wcel vc
      cv cC wcel wa vc cv cC cuni cJ cuni vc cv cC wcel vc cv cC cuni wss cC cJ
      clocfin cfv wcel vc cv cC elssuni adantl cC cJ clocfin cfv wcel cC cuni
      cJ cuni wceq vc cv cC wcel cC cJ clocfin cfv wcel cJ cuni cC cuni cC cJ
      cJ cuni cC cuni cJ cuni eqid cC cC cC cC cC cC cC cC cC ssid cC ssid
      eqssi eqimss2i cC cC cC cC cC ssid cC ssid eqssi eqimss2i eqssi unieqi
      locfinbas eqcomd adantr sseqtrd vc cv cJ cJ cuni cJ cuni eqid sscls
      syl2anc cC cJ clocfin cfv wcel vc cv cC wcel wa vc cv cJ ccl cfv cfv cJ
      ccl cfv cC cima wcel vc cv cJ ccl cfv cfv cJ ccl cfv cC cima cuni wss cC
      cJ clocfin cfv wcel vc cv cC wcel wa cJ ccl cfv cJ cuni cpw wfn cC cJ
      cuni cpw wss vc cv cC wcel vc cv cJ ccl cfv cfv cJ ccl cfv cC cima wcel
      cC cJ clocfin cfv wcel cJ ccl cfv cJ cuni cpw wfn vc cv cC wcel cC cJ
      clocfin cfv wcel cJ ctop wcel cJ ccl cfv cJ cuni cpw wfn cC cJ locfintop
      cJ clsfn syl adantr cC cJ clocfin cfv wcel cC cJ cuni cpw wss vc cv cC
      wcel cC cJ locfinsspw adantr cC cJ clocfin cfv wcel vc cv cC wcel simpr
      cJ cuni cpw cC cJ ccl cfv vc cv fnfvima syl3anc vc cv cJ ccl cfv cfv cJ
      ccl cfv cC cima elssuni syl sstrd ex $.
  $}

  ${
    $d c n s x C $.  $d c n s x J $.
    $( The union of the closure image of a locally finite collection equals
       the base set.  (Contributed by Claude, 6-Feb-2026.) $)
    lfimclsuni $p |- ( C e. ( LocFin ` J ) ->
      U. J = U. ( ( cls ` J ) " C ) ) $=
      cC cJ clocfin cfv wcel cJ cuni cJ ccl cfv cC cima cuni cC cJ clocfin cfv
      wcel cJ cuni cC cuni cJ ccl cfv cC cima cuni cC cJ cJ cuni cC cuni cJ cJ
      cJ eqid unieqi cC cC cC eqid unieqi locfinbas cC cJ clocfin cfv wcel vs
      cv cJ ccl cfv cC cima cuni wss vs cC wral cC cuni cJ ccl cfv cC cima cuni
      wss cC cJ clocfin cfv wcel vs cv cJ ccl cfv cC cima cuni wss vs cC cC cJ
      vs lfimclsuniss ralrimiv vs cC cJ ccl cfv cC cima cuni unissb sylibr
      eqsstrd cC cJ clocfin cfv wcel cJ ccl cfv cC cima cJ cuni cpw wss cJ ccl
      cfv cC cima cuni cJ cuni wss cC cJ clocfin cfv wcel cJ ccl cfv cC cima cJ
      ccld cfv cJ cuni cpw cC cJ clocfin cfv wcel cJ cuni cpw cJ ccld cfv cJ
      ccl cfv wf cJ ccl cfv cC cima cJ ccld cfv wss cC cJ clocfin cfv wcel cJ
      ctop wcel cJ cuni cpw cJ ccld cfv cJ ccl cfv wf cC cJ locfintop cJ cJ
      cuni cJ cJ cJ eqid unieqi clsf syl cJ cuni cpw cJ ccld cfv cJ ccl cfv cC
      fimass syl cJ ccld cfv cJ cuni cpw wss cC cJ clocfin cfv wcel cJ cJ cuni
      cJ cJ cJ eqid unieqi cldss2 a1i sstrd cJ ccl cfv cC cima cJ cuni sspwuni
      sylib eqssd $.

    ${
      $d c s C $.  $d c s J $.  $d c s N $.
      $( If ` C ` is locally finite and ` N e. J ` , then finiteness of the
         subcollection of ` C ` intersecting ` N ` implies finiteness of
         the closure image subcollection intersecting ` N ` .
         (Contributed by Claude, 6-Feb-2026.) $)
      lfimclslflem3 $p |- ( ( C e. ( LocFin ` J ) /\ N e. J ) ->
        ( { c e. C | ( c i^i N ) =/= (/) } e. Fin ->
          { s e. ( ( cls ` J ) " C ) | ( s i^i N ) =/= (/) } e. Fin ) ) $=
        cC cJ clocfin cfv wcel cN cJ wcel vc cv cN cin c0 wne vc cC crab cfn
        wcel vs cv cN cin c0 wne vs cJ ccl cfv cC cima crab cfn wcel cC cJ cN
        vs vc lfimclslflem2 3expia $.
    $}

    $( The closure image of a locally finite collection satisfies the
       local finiteness condition: each point has a neighborhood that
       intersects only finitely many elements of the image.
       (Contributed by Claude, 6-Feb-2026.) $)
    lfimclslf $p |- ( C e. ( LocFin ` J ) -> A. x e. U. J
      E. n e. J ( x e. n /\
        { s e. ( ( cls ` J ) " C ) | ( s i^i n ) =/= (/) } e. Fin ) ) $=
      cC cJ clocfin cfv wcel vx vn wel vs cv vn cv cin c0 wne vs cJ ccl cfv cC
      cima crab cfn wcel wa vn cJ wrex vx cJ cuni cC cJ clocfin cfv wcel vx cv
      cJ cuni wcel wa vx vn wel vc cv vn cv cin c0 wne vc cC crab cfn wcel wa
      vn cJ wrex vx vn wel vs cv vn cv cin c0 wne vs cJ ccl cfv cC cima crab
      cfn wcel wa vn cJ wrex cC vx cv vn cJ cJ cuni vc cJ cuni eqid locfinnei
      cC cJ clocfin cfv wcel vx cv cJ cuni wcel wa vx vn wel vc cv vn cv cin
      c0 wne vc cC crab cfn wcel wa vx vn wel vs cv vn cv cin c0 wne vs cJ ccl
      cfv cC cima crab cfn wcel wa vn cJ cC cJ clocfin cfv wcel vx cv cJ cuni
      wcel wa vn cv cJ wcel wa vc cv vn cv cin c0 wne vc cC crab cfn wcel vs
      cv vn cv cin c0 wne vs cJ ccl cfv cC cima crab cfn wcel vx vn wel cC cJ
      clocfin cfv wcel vx cv cJ cuni wcel wa vn cv cJ wcel wa cC cJ clocfin
      cfv wcel vn cv cJ wcel vc cv vn cv cin c0 wne vc cC crab cfn wcel vs cv
      vn cv cin c0 wne vs cJ ccl cfv cC cima crab cfn wcel wi cC cJ clocfin
      cfv wcel vx cv cJ cuni wcel wa cC cJ clocfin cfv wcel vn cv cJ wcel cC
      cJ clocfin cfv wcel vx cv cJ cuni wcel simpl adantr cC cJ clocfin cfv
      wcel vx cv cJ cuni wcel wa vn cv cJ wcel simpr cC cJ vn cv vs vc
      lfimclslflem3 syl2anc anim2d reximdva mpd ralrimiva $.

    $( The image of a locally finite collection under the closure operator is
       locally finite.  This is because if an open neighborhood ` U ` does not
       intersect a set ` c ` , then ` U ` does not intersect the closure of
       ` c ` either (since the complement of ` U ` is a closed superset of
       ` c ` ).  Part of Lemma 39.1 in Munkres p. 245.
       (Contributed by Claude, 5-Feb-2026.) $)
    lfimcls $p |- ( C e. ( LocFin ` J ) ->
      ( ( cls ` J ) " C ) e. ( LocFin ` J ) ) $=
      cC cJ clocfin cfv wcel cJ ctop wcel cJ cuni cJ ccl cfv cC cima cuni wceq
      vx vn wel vs cv vn cv cin c0 wne vs cJ ccl cfv cC cima crab cfn wcel wa
      vn cJ wrex vx cJ cuni wral cJ ccl cfv cC cima cJ clocfin cfv wcel cC cJ
      locfintop cC cJ lfimclsuni vx cC vn cJ vs lfimclslf vx cJ ccl cfv cC cima
      vn cJ cJ cuni cJ ccl cfv cC cima cuni vs cJ cuni eqid cJ ccl cfv cC cima
      cuni eqid islocfin syl3anbrc $.
  $}

  ${
    $d a w y z J $.
    $( Helper for ~ regsepcover : apply regularity separation to get
       an open set whose closure is contained in a covering element.
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover2a $p |- ( ( ( J e. Reg /\ y C_ J ) /\ ( w e. y /\ z e. w ) )
      -> E. a e. J ( z e. a /\ ( ( cls ` J ) ` a ) C_ w ) ) $=
      cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel wa wa cJ creg wcel vw cv
      cJ wcel vz vw wel vz va wel va cv cJ ccl cfv cfv vw cv wss wa va cJ wrex
      cJ creg wcel vy cv cJ wss vw vy wel vz vw wel wa simpll cJ creg wcel vy
      cv cJ wss wa vw vy wel vz vw wel wa wa vy cv cJ vw cv cJ creg wcel vy cv
      cJ wss wa vw vy wel vz vw wel wa wa vy cv cJ wss wi wtru cJ creg wcel vy
      cv cJ wss wa vw vy wel vz vw wel wa vy cv cJ wss wtru cJ creg wcel vy cv
      cJ wss vw vy wel vz vw wel wa simp2r 3expib mptru cJ creg wcel vy cv cJ
      wss wa vw vy wel vz vw wel wa wa vw vy wel wi wtru cJ creg wcel vy cv cJ
      wss wa vw vy wel vz vw wel wa vw vy wel wtru cJ creg wcel vy cv cJ wss wa
      vw vy wel vz vw wel simp3l 3expib mptru sseldd cJ creg wcel vy cv cJ wss
      wa vw vy wel vz vw wel simprr va vz cv vw cv cJ regsep syl3anc $.
  $}

  ${
    $d a u v w y z J $.
    $( Helper for ~ regsepcover : given ` w e. y ` , ` a e. J ` ,
       ` z e. a ` , and ` ( ( cls `` J ) `` a ) C_ w ` , conclude
       ` z e. U. { v e. J | E. u e. y ( ( cls `` J ) `` v ) C_ u } ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover2b $p |- ( ( ( w e. y /\ a e. J ) /\
      ( z e. a /\ ( ( cls ` J ) ` a ) C_ w ) ) ->
      z e. U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      vw vy wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv wss wa wa
      vz va wel va cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab
      wcel vz cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni
      wcel vw vy wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv wss
      simprl vw vy wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv
      wss wa wa va cv cJ wcel va cv cJ ccl cfv cfv vu cv wss vu vy cv wrex va
      cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab wcel vw vy wel
      va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv wss wa simplr vw vy
      wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv wss wa wa vw vy
      wel va cv cJ ccl cfv cfv vw cv wss va cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vw vy wel va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv wss
      wa simpll vw vy wel va cv cJ wcel wa vz va wel va cv cJ ccl cfv cfv vw cv
      wss wa wa va cv cJ ccl cfv cfv vw cv vw vy wel va cv cJ ccl cfv cfv vw cv
      wss va cv cJ ccl cfv cfv vw cv cpw wcel va cv cJ wcel vz va wel vw vy wel
      va cv cJ ccl cfv cfv vw cv cpw wcel va cv cJ ccl cfv cfv vw cv wss va cv
      cJ ccl cfv cfv vw cv vy cv elpw2g biimpar ad2ant2rl elpwid va cv cJ ccl
      cfv cfv vu cv wss va cv cJ ccl cfv cfv vw cv wss vu vw cv vy cv vu vw weq
      va cv cJ ccl cfv cfv va cv cJ ccl cfv cfv vu cv vw cv vu vw weq va cv va
      cv cJ ccl cfv cJ ccl cfv vu vw weq cJ cJ ccl ccl vu vw weq ccl eqidd vu
      vw weq cJ eqidd fveq12d vu vw weq va cv va cv vu vw weq va cv ssidd vu vw
      weq va cv ssidd eqssd fveq12d vu vw weq vu cv vw cv vu cv vw cv csn wcel
      vu vw weq vu vw cv velsn biimpri elsnd sseq12d rspcev syl2anc vv cv cJ
      ccl cfv cfv vu cv wss vu vy cv wrex va cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv va cv cJ vv va weq vv cv cJ ccl cfv cfv vu cv wss va cv cJ ccl
      cfv cfv vu cv wss vu vy cv vv va weq vv cv cJ ccl cfv cfv va cv cJ ccl
      cfv cfv vu cv vu cv vv va weq vv cv va cv cJ ccl cfv cJ ccl cfv vv va weq
      cJ cJ ccl ccl vv va weq ccl eqidd vv va weq cJ eqidd fveq12d vv va weq vv
      cv va cv vv cv va cv eqimss va cv vv cv eqimss2 eqssd fveq12d vv va weq
      vu cv vu cv vu cv vu cv csn wcel vv va weq vu vsnid a1i elsnd sseq12d
      rexbidv elrab sylanbrc vz cv va cv vv cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv cJ crab elunii syl2anc $.
  $}

  ${
    $d a u v w y z J $.
    $( Helper for ~ regsepcover : in a regular space, if ` w ` is in an open
       covering ` y ` (which is a subset of ` J ` ) and ` z e. w ` , then
       ` z ` is in the union of the regularity-refined covering.
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover2 $p |- ( ( ( J e. Reg /\ y C_ J ) /\ ( w e. y /\ z e. w ) )
      -> z e. U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel wa wa vz va wel va cv cJ
      ccl cfv cfv vw cv wss wa vz cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab cuni wcel va cJ vy vz vw cJ va regsepcover2a cJ creg wcel
      vy cv cJ wss wa vw vy wel vz vw wel wa wa va cv cJ wcel vz va wel va cv
      cJ ccl cfv cfv vw cv wss wa wa wa vw vy wel va cv cJ wcel wa vz va wel va
      cv cJ ccl cfv cfv vw cv wss wa vz cv vv cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv cJ crab cuni wcel cJ creg wcel vy cv cJ wss wa vw vy wel vz vw
      wel wa wa va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv wss wa wa wa
      vw vy wel va cv cJ wcel cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel
      wa wa vw vy wel va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv wss wa
      wa cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel simprl adantr cJ creg
      wcel vy cv cJ wss wa vw vy wel vz vw wel wa wa va cv cJ wcel vz va wel va
      cv cJ ccl cfv cfv vw cv wss wa simprl jca cJ creg wcel vy cv cJ wss wa vw
      vy wel vz vw wel wa wa va cv cJ wcel vz va wel va cv cJ ccl cfv cfv vw cv
      wss wa simprr vy vz vw vv vu cJ va regsepcover2b syl2anc rexlimddv $.
  $}

  ${
    $d u v w y z J $.
    $( In a regular space, if ` w ` is in the open covering ` y ` (a subset
       of ` J ` ), then ` w ` is a subset of the union of the
       regularity-refined covering.  Helper for ~ regsepcover1 .
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover1a $p |- ( ( ( J e. Reg /\ y C_ J ) /\ w e. y ) ->
      w C_ U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      cJ creg wcel vy cv cJ wss wa vw vy wel wa vz vw cv vv cv cJ ccl cfv cfv
      vu cv wss vu vy cv wrex vv cJ crab cuni cJ creg wcel vy cv cJ wss wa vw
      vy wel wa vz vw wel vz cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv
      cJ crab cuni wcel cJ creg wcel vy cv cJ wss wa vw vy wel vz vw wel vz cv
      vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni wcel vy vz
      vw vv vu cJ regsepcover2 anassrs ex ssrdv $.
  $}

  ${
    $d u v w y z J $.
    $( In a regular space, every element of the union of an open covering
       ` y ` is in the union of the regularity-refined covering.  Helper for
       ~ regsepcover .  (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover1 $p |- ( ( J e. Reg /\ y C_ J ) ->
      U. y C_ U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      cJ creg wcel vy cv cJ wss wa vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex vv cJ crab cuni wss vw vy cv wral vy cv cuni vv cv cJ ccl cfv cfv
      vu cv wss vu vy cv wrex vv cJ crab cuni wss cJ creg wcel vy cv cJ wss wa
      vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni wss vw
      vy cv vy vw vv vu cJ regsepcover1a ralrimiva vw vy cv vv cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vv cJ crab cuni unissb sylibr $.
  $}

  ${
    $d u v w y z J $.
    $( Regularity covering: in a regular space, if ` y ` is an open covering
       of ` J ` , then the collection of open sets whose closure is in some
       element of ` y ` also covers ` J ` .
       (Contributed by Claude, 6-Feb-2026.) $)
    regsepcover $p |- ( ( J e. Reg /\ y C_ J /\ U. J = U. y ) ->
      U. J = U. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ) $=
      cJ creg wcel vy cv cJ wss cJ cuni vy cv cuni wceq w3a cJ cuni vv cv cJ
      ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni cJ creg wcel vy cv cJ
      wss cJ cuni vy cv cuni wceq w3a cJ cuni vy cv cuni vv cv cJ ccl cfv cfv
      vu cv wss vu vy cv wrex vv cJ crab cuni cJ creg wcel vy cv cJ wss cJ cuni
      vy cv cuni wceq simp3 cJ creg wcel vy cv cJ wss vy cv cuni vv cv cJ ccl
      cfv cfv vu cv wss vu vy cv wrex vv cJ crab cuni wss cJ cuni vy cv cuni
      wceq vy vv vu cJ regsepcover1 3adant3 eqsstrd vv cv cJ ccl cfv cfv vu cv
      wss vu vy cv wrex vv cJ crab cuni cJ cuni wss cJ creg wcel vy cv cJ wss
      cJ cuni vy cv cuni wceq w3a vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex
      vv cJ crab cJ vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ ssrab2
      unissi a1i eqssd $.
  $}

  ${
    $d u w y z J $.
    $( In a topology, if ` w ` is an open set and ` z C_ w ` , then
       the existential condition on the closure of ` w ` transfers to
       the closure of ` z ` .  Helper for ~ clsreflem .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsreflema $p |- ( ( J e. Top /\ w e. J /\ z C_ w ) ->
      ( E. u e. y ( ( cls ` J ) ` w ) C_ u ->
        E. u e. y ( ( cls ` J ) ` z ) C_ u ) ) $=
      cJ ctop wcel vw cv cJ wcel vz cv vw cv wss w3a vw cv cJ ccl cfv cfv vu cv
      wss vz cv cJ ccl cfv cfv vu cv wss vu vy cv cJ ctop wcel vw cv cJ wcel vz
      cv vw cv wss w3a vz cv cJ ccl cfv cfv vw cv cJ ccl cfv cfv wss vw cv cJ
      ccl cfv cfv vu cv wss vz cv cJ ccl cfv cfv vu cv wss wi vw cv cJ wcel cJ
      ctop wcel vw cv cJ cuni wss vz cv vw cv wss vz cv cJ ccl cfv cfv vw cv cJ
      ccl cfv cfv wss vw cv cJ elssuni vw cv vz cv cJ cJ cuni cJ cuni eqid
      clsss syl3an2 vz cv cJ ccl cfv cfv vw cv cJ ccl cfv cfv vu cv sstr2 syl
      reximdv $.
  $}

  ${
    $d u v w y J $.
    $( Extract the existential condition from membership in the
       regularity-refined covering.  If ` w ` is in
       ` { v e. J | E. u e. y ( ( cls `` J ) `` v ) C_ u } ` , then
       the closure of ` w ` is contained in some element of ` y ` .
       Helper for ~ clsreflemb .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsreflemc $p |- (
      w e. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } ->
      E. u e. y ( ( cls ` J ) ` w ) C_ u ) $=
      vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab wcel vw cv
      cJ wcel vw cv cJ ccl cfv cfv vu cv wss vu vy cv wrex wa vw cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab wcel vw cv cJ wcel vw cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex wa vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vw cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vv vw cv cJ vv cv cJ ccl cfv cfv vu cv wss vu
      vy cv wrex vw cv cJ ccl cfv cfv vu cv wss vu vy cv wrex wb vv vw vv cv cJ
      ccl cfv cfv vu cv wss vu vy cv wrex vw cv cJ ccl cfv cfv vu cv wss vu vy
      cv wrex wb vv vw vv vw weq vv cv cJ ccl cfv cfv vu cv wss vw cv cJ ccl
      cfv cfv vu cv wss vu vy cv vy cv vu vv cv vw cv vu vw cv nfcv nfeq2 vu vy
      cv nfcv vu vy cv nfcv vv vw weq vy cv vy cv vy cv vy cv csn wcel vv vw
      weq vy vsnid a1i elsnd vv vw weq vv cv cJ ccl cfv cfv vw cv cJ ccl cfv
      cfv vu cv vu cv vv vw weq vv cv vw cv cJ ccl cfv cJ ccl cfv vv vw weq cJ
      ccl cfv eqidd vv vw weq id fveq12d vv vw weq vu cv vu cv vv vw weq vu cv
      ssidd vv vw weq vu cv ssidd eqssd sseq12d rexeqbid cdeqi cdeqri elrab
      biimpi vw cv cJ wcel vw cv cJ ccl cfv cfv vu cv wss vu vy cv wrex simpr
      syl $.
  $}

  ${
    $d u v w y z J $.
    $( If ` w ` is in the regularity-refined covering
       ` { v e. J | E. u e. y ( ( cls `` J ) `` v ) C_ u } ` and
       ` z C_ w ` , then the closure of ` z ` is contained in some element
       of ` y ` .  Helper for ~ clsreflem .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsreflemb $p |- ( ( J e. Top /\
      w e. { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } /\
      z C_ w ) ->
      E. u e. y ( ( cls ` J ) ` z ) C_ u ) $=
      cJ ctop wcel vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ
      crab wcel vz cv vw cv wss w3a vw cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vz cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vw cv vv cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vv cJ crab wcel cJ ctop wcel vw cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vz cv vw cv wss vy vw vv vu cJ clsreflemc
      3ad2ant2 vw cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab
      wcel cJ ctop wcel vw cv cJ wcel vz cv vw cv wss vw cv cJ ccl cfv cfv vu
      cv wss vu vy cv wrex vz cv cJ ccl cfv cfv vu cv wss vu vy cv wrex wi vv
      cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv vw cv cJ elrabi vy vz vw vu
      cJ clsreflema syl3an2 mpd $.
  $}

  ${
    $d t u v w y z J $.
    $( If ` t ` refines the regularity-refined covering
       ` { v e. J | E. u e. y ( ( cls `` J ) `` v ) C_ u } ` and
       ` z e. t ` , then the closure of ` z ` is contained in some element
       of ` y ` .  Helper for ~ reglfpcmplem1 .
       (Contributed by Claude, 6-Feb-2026.) $)
    clsreflem $p |- ( ( J e. Top /\
      t Ref { v e. J | E. u e. y ( ( cls ` J ) ` v ) C_ u } /\
      z e. t ) ->
      E. u e. y ( ( cls ` J ) ` z ) C_ u ) $=
      cJ ctop wcel vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ
      crab cref wbr vz vt wel w3a vz cv vw cv wss vw vv cv cJ ccl cfv cfv vu cv
      wss vu vy cv wrex vv cJ crab wrex vz cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vt cv vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref
      wbr vz vt wel vz cv vw cv wss vw vv cv cJ ccl cfv cfv vu cv wss vu vy cv
      wrex vv cJ crab wrex cJ ctop wcel vw vt cv vv cv cJ ccl cfv cfv vu cv wss
      vu vy cv wrex vv cJ crab vz cv refssex 3adant1 cJ ctop wcel vt cv vv cv
      cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab cref wbr vz cv vw cv
      wss vw vv cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vv cJ crab wrex vz cv
      cJ ccl cfv cfv vu cv wss vu vy cv wrex wi vz vt wel cJ ctop wcel vz cv vw
      cv wss vz cv cJ ccl cfv cfv vu cv wss vu vy cv wrex vw vv cv cJ ccl cfv
      cfv vu cv wss vu vy cv wrex vv cJ crab vy vz vw vv vu cJ clsreflemb
      rexlimdv3a 3ad2ant1 mpd $.
  $}

  ${
    $d t y z J $.
    $( Lemma 41.3 step (2) implies (3): If ` J ` is a regular topology and
       every open covering has a locally finite covering refinement, then every
       open covering has a locally finite closed covering refinement.
       The proof uses regularity to find, for each point and each covering
       element, an open set whose closure is contained in the covering element,
       then applies the hypothesis and takes closures.
       (Contributed by Claude, 5-Feb-2026.) $)
    reglfpcmplem1 $p |- ( ( J e. Reg /\
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( LocFin ` J ) t Ref y ) ) ->
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) t Ref y ) ) $=
      ? $.
  $}

  ${
    $d t y z J $.
    $( Lemma 41.3 step (3) implies (4): If ` J ` is a topology and every
       open covering has a locally finite closed covering refinement, then
       ` J ` is paracompact.  The proof expands each closed set in a locally
       finite closed covering to an open set, using an auxiliary locally
       finite closed covering to control the expansion.
       (Contributed by Claude, 5-Feb-2026.) $)
    reglfpcmplem2 $p |- ( ( J e. Top /\
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( ( LocFin ` J ) i^i ~P ( Clsd ` J ) ) t Ref y ) ) ->
      J e. ParaCmp ) $=
      ? $.
  $}

  ${
    $d t y z J $.
    $( Lemma 41.3 step (2) implies (4): If ` J ` is a regular topology and
       every open covering of ` J ` has a locally finite covering refinement,
       then ` J ` is paracompact.  This combines the (2) to (3) step
       ~ reglfpcmplem1 with the (3) to (4) step ~ reglfpcmplem2 .
       (Contributed by Claude, 5-Feb-2026.) $)
    reglfpcmp $p |- ( ( J e. Reg /\
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( LocFin ` J ) t Ref y ) ) ->
      J e. ParaCmp ) $=
      cJ creg wcel cJ cuni vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin
      cfv wrex wi vy cJ cpw wral wa cJ ctop wcel cJ cuni vy cv cuni wceq vt cv
      vy cv cref wbr vt cJ clocfin cfv cJ ccld cfv cpw cin wrex wi vy cJ cpw
      wral wa cJ cpacmp wcel cJ creg wcel cJ cuni vy cv cuni wceq vt cv vy cv
      cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw wral wa cJ ctop wcel cJ cuni
      vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin cfv cJ ccld cfv cpw
      cin wrex wi vy cJ cpw wral cJ creg wcel cJ cuni vy cv cuni wceq vt cv vy
      cv cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw wral wa cJ creg wcel cJ
      ctop wcel cJ creg wcel cJ cuni vy cv cuni wceq vt cv vy cv cref wbr vt cJ
      clocfin cfv wrex wi vy cJ cpw wral simpl cJ regtop syl vy vt cJ
      reglfpcmplem1 jca vy vt cJ reglfpcmplem2 syl $.
  $}

  ${
    $d s t y J $.
    $( Helper for ~ regpcmp .  Convert the sigma-locally finite refinement
       condition to a locally finite refinement condition under the universal
       quantifier, using ~ clocfinlf pointwise.
       (Contributed by Claude, 5-Feb-2026.) $)
    regpcmplem $p |- ( ( J e. Top /\
      A. y e. ~P J ( U. J = U. y ->
        E. s e. ( ( CntLocFin ` J ) i^i ~P J ) s Ref y ) ) ->
      A. y e. ~P J ( U. J = U. y ->
        E. t e. ( LocFin ` J ) t Ref y ) ) $=
      cJ ctop wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin
      cfv cJ cpw cin wrex wi vy cJ cpw wral cJ cuni vy cv cuni wceq vt cv vy cv
      cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw wral cJ ctop wcel cJ cuni vy
      cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi
      cJ cuni vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin cfv wrex wi vy
      cJ cpw cJ ctop wcel vs cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin
      wrex vt cv vy cv cref wbr vt cJ clocfin cfv wrex cJ cuni vy cv cuni wceq
      cJ ctop wcel vs cv vy cv cref wbr vt cv vy cv cref wbr vt cJ clocfin cfv
      wrex vs cJ cclocfin cfv cJ cpw cin cJ ctop wcel vs cv cJ cclocfin cfv cJ
      cpw cin wcel vs cv vy cv cref wbr vt cv vy cv cref wbr vt cJ clocfin cfv
      wrex vy vt cJ vs clocfinlf 3exp rexlimdv imim2d ralimdv imp $.
  $}

  ${
    $d s t y z J $.
    $( Lemma 41.3 of Munkres p. 252 (direction (1) implies (4)):  If ` J `
       is a regular topology and every open covering of ` J ` has a
       sigma-locally finite open refinement, then ` J ` is paracompact.
       This is the key step in Michael's theorem.  Proved by chaining
       ~ clocfinlf (sigma-locally finite to locally finite covering)
       with ~ reglfpcmp (locally finite covering to paracompact).
       (Contributed by Claude, 5-Feb-2026.) $)
    regpcmp $p |- ( ( J e. Reg /\
      A. y e. ~P J ( U. J = U. y ->
        E. s e. ( ( CntLocFin ` J ) i^i ~P J ) s Ref y ) ) ->
      J e. ParaCmp ) $=
      cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin
      cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ creg wcel cJ cuni vy cv cuni
      wceq vt cv vy cv cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw wral wa cJ
      cpacmp wcel cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs
      cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ creg wcel cJ cuni
      vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw
      wral cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral simpl cJ creg wcel cJ cuni
      vy cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin wrex
      wi vy cJ cpw wral wa cJ ctop wcel cJ cuni vy cv cuni wceq vs cv vy cv
      cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ cuni
      vy cv cuni wceq vt cv vy cv cref wbr vt cJ clocfin cfv wrex wi vy cJ cpw
      wral cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ ctop wcel cJ cuni vy
      cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi
      vy cJ cpw wral cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr
      vs cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ creg wcel cJ
      ctop wcel cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral simpl cJ regtop syl cJ
      creg wcel cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ cclocfin cfv
      cJ cpw cin wrex wi vy cJ cpw wral simpr jca vy vt cJ vs regpcmplem syl
      jca vy vt cJ reglfpcmp syl $.
  $}

  ${
    $d s y z D $.  $d s y z J $.  $d s y z X $.
    metpcmplem1d.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma for ~ metpcmp .  A metrizable space is paracompact.  This
       combines ~ metclocfin (Lemma 39.2, sigma-locally finite refinement)
       with ~ regpcmp (Lemma 41.3) and ~ metreg (metric implies regular).
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmplem1d $p |- ( D e. ( *Met ` X ) -> J e. ParaCmp ) $=
      cD cX cxmet cfv wcel cJ creg wcel cJ cuni vy cv cuni wceq vs cv vy cv
      cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral wa cJ
      cpacmp wcel cD cX cxmet cfv wcel cJ creg wcel cJ cuni vy cv cuni wceq vs
      cv vy cv cref wbr vs cJ cclocfin cfv cJ cpw cin wrex wi vy cJ cpw wral cD
      cJ cX metpcmplem1d.1 metreg vy cD cJ cX vs metpcmplem1d.1 metclocfin jca
      vy cJ vs regpcmp syl $.
  $}

  ${
    $d z y J $.
    $( Every open covering of a paracompact topology has a locally finite
       open refinement.  This is the forward direction of the
       characterization in ~ ispcmp .
       (Contributed by Claude, 5-Feb-2026.) $)
    pcmpcov $p |- ( ( J e. ParaCmp /\ y C_ J /\ U. J = U. y ) ->
      E. z e. ( ( LocFin ` J ) i^i ~P J ) z Ref y ) $=
      cJ cpacmp wcel vy cv cJ wss cJ cuni vy cv cuni wceq vz cv vy cv cref wbr
      vz cJ clocfin cfv cJ cpw cin wrex vy cv cJ wss vy cv cJ cpw wcel cJ
      cpacmp wcel cJ cuni vy cv cuni wceq vz cv vy cv cref wbr vz cJ clocfin
      cfv cJ cpw cin wrex wi vy cv cJ cpw wcel vy cv cJ wss vy cJ velpw biimpri
      cJ cpacmp wcel cJ cuni vy cv cuni wceq vz cv vy cv cref wbr vz cJ clocfin
      cfv cJ cpw cin wrex wi vy cJ cpw wral vy cv cJ cpw wcel cJ cuni vy cv
      cuni wceq vz cv vy cv cref wbr vz cJ clocfin cfv cJ cpw cin wrex wi wi cJ
      cpacmp wcel cJ ctop wcel cJ cuni vy cv cuni wceq vz cv vy cv cref wbr vz
      cJ clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral vy vz cJ cJ cuni cJ cuni
      eqid ispcmp simprbi cJ cuni vy cv cuni wceq vz cv vy cv cref wbr vz cJ
      clocfin cfv cJ cpw cin wrex wi vy cJ cpw rsp syl syl5 3imp $.
  $}

  ${
    $d s y z D $.  $d s y z J $.  $d s y z X $.
    metpcmplem1.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma for ~ metpcmp .  For a metrizable space, any open covering has
       a locally finite open refinement.  Proved by combining
       ~ metpcmplem1d (metrizable implies paracompact) with ~ pcmpcov
       (extracting single-cover result) and a bound variable conversion.
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmplem1 $p |- ( ( D e. ( *Met ` X ) /\ y C_ J /\ X = U. y ) ->
      E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) $=
      cD cX cxmet cfv wcel vy cv cJ wss cX vy cv cuni wceq w3a cJ cpacmp wcel
      vy cv cJ wss cJ cuni vy cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin
      cfv cJ cpw cin wrex cD cX cxmet cfv wcel vy cv cJ wss cX vy cv cuni wceq
      w3a cD cX cxmet cfv wcel cJ cpacmp wcel cD cX cxmet cfv wcel vy cv cJ wss
      cX vy cv cuni wceq simp1 cD cJ cX metpcmplem1.1 metpcmplem1d syl cD cX
      cxmet cfv wcel vy cv cJ wss cX vy cv cuni wceq simp2 cD cX cxmet cfv wcel
      vy cv cJ wss cX vy cv cuni wceq w3a cX cJ cuni vy cv cuni cD cX cxmet cfv
      wcel vy cv cJ wss cX vy cv cuni wceq w3a cD cX cxmet cfv wcel cX cJ cuni
      wceq cD cX cxmet cfv wcel vy cv cJ wss cX vy cv cuni wceq simp1 cD cJ cX
      metpcmplem1.1 mopnuni syl cD cX cxmet cfv wcel vy cv cJ wss cX vy cv cuni
      wceq simp3 eqtr3d vy vs cJ pcmpcov syl3anc $.
  $}

  ${
    $d s y D $.  $d s y J $.  $d s y X $.
    metpcmplem2.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma for ~ metpcmp .  A metrizable space satisfies the paracompactness
       quantifier: every open covering has a locally finite open refinement.
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmplem2 $p |- ( D e. ( *Met ` X ) ->
      A. y e. ~P J ( X = U. y ->
        E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) ) $=
      cD cX cxmet cfv wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      clocfin cfv cJ cpw cin wrex wi vy cJ cpw vy cv cJ cpw wcel vy cv cJ wss
      cD cX cxmet cfv wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      clocfin cfv cJ cpw cin wrex wi vy cv cJ elpwi cD cX cxmet cfv wcel vy cv
      cJ wss cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw
      cin wrex vy cD cJ cX vs metpcmplem2.1 metpcmplem1 3exp syl5 ralrimiv $.
  $}

  ${
    $d s y D $.  $d s y J $.  $d s y X $.
    metpcmplem3.1 $e |- J = ( MetOpen ` D ) $.
    $( Lemma for ~ metpcmp .  Convert the universe variable from ` X ` to
       ` U. J ` in the paracompactness quantifier.
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmplem3 $p |- ( D e. ( *Met ` X ) ->
      A. y e. ~P J ( U. J = U. y ->
        E. s e. ( ( LocFin ` J ) i^i ~P J ) s Ref y ) ) $=
      cD cX cxmet cfv wcel cX vy cv cuni wceq vs cv vy cv cref wbr vs cJ
      clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral cJ cuni vy cv cuni wceq vs
      cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral vy
      cD cJ cX vs metpcmplem3.1 metpcmplem2 cD cX cxmet cfv wcel cX vy cv cuni
      wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi cJ cuni vy
      cv cuni wceq vs cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi vy
      cJ cpw cD cX cxmet cfv wcel cX vy cv cuni wceq cJ cuni vy cv cuni wceq vs
      cv vy cv cref wbr vs cJ clocfin cfv cJ cpw cin wrex cD cX cxmet cfv wcel
      cX cJ cuni vy cv cuni cD cJ cX metpcmplem3.1 mopnuni eqeq1d imbi1d
      ralbidv mpbid $.
  $}

  ${
    $d s y z D $.  $d s y z J $.  $d s y z X $.
    metpcmp.1 $e |- J = ( MetOpen ` D ) $.
    $( Theorem 41.4 of Munkres p. 256: Every metrizable space is paracompact.
       The proof combines Lemma 39.2, that every open covering of a metrizable
       space has a countably locally finite open refinement, with Lemma 41.3,
       Michael's lemma, that for regular spaces, countably locally finite
       refinement implies locally finite refinement.
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmp $p |- ( D e. ( *Met ` X ) -> J e. ParaCmp ) $=
      cD cX cxmet cfv wcel cJ ctop wcel cJ cuni vy cv cuni wceq vs cv vy cv
      cref wbr vs cJ clocfin cfv cJ cpw cin wrex wi vy cJ cpw wral cJ cpacmp
      wcel cD cJ cX metpcmp.1 mopntop vy cD cJ cX vs metpcmp.1 metpcmplem3 vy
      vs cJ cJ cuni cJ cuni eqid ispcmp sylanbrc $.
  $}

