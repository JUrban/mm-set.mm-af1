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
      cv cref wbr ? cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy
      cv cpw cfn cin wcel cX vs cv cuni wceq wa vs cv vy cv cref wbr cJ ctop
      wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv vy cv cpw cfn cin wcel cX
      vs cv cuni wceq wa wa vs cv vy cv cpw cfn cin wcel vs cv vy cv wss ? vs
      cv vy cv cref wbr cJ ctop wcel vy cv cJ wss cX vy cv cuni wceq w3a vs cv
      vy cv cpw cfn cin wcel cX vs cv cuni wceq simprl ? ? vs cv vy cv ? vs cv
      cuni vy cv cuni vs cv cuni eqid vy cv cuni eqid ssref syl3anc ex jcad $.
  $}

  ${
    $d s y z J $.  $d s y z X $.
    cmppcmp.1 $e |- X = U. J $.
    $( Every compact topology is paracompact.
       (Contributed by Claude, 5-Feb-2026.) $)
    cmppcmp $p |- ( J e. Comp -> J e. ParaCmp ) $=
      ? $.
  $}

  ${
    metpcmp.1 $e |- J = ( MetOpen ` D ) $.
    $( Theorem 41.4 of Munkres p. 256: Every metrizable space is paracompact.
       The proof combines Lemma 39.2, that every open covering of a metrizable
       space has a countably locally finite open refinement, with Lemma 41.3,
       Michael's lemma, that for regular spaces, countably locally finite
       refinement implies locally finite refinement.
       (Contributed by Claude, 5-Feb-2026.) $)
    metpcmp $p |- ( D e. ( *Met ` X ) -> J e. ParaCmp ) $=
      ? $.
  $}

