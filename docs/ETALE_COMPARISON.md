# Étale comparison and Suslin rigidity

This work continues the 2026-10-21 Motivic source checkpoint in Colib, using
the current Mathlib and Stacks pins and Colib's existing mathematical objects.
It does not resume the separate strict A1 or Milnor development.

## Target and chosen objects

The rigidity target is the small-site origin statement of MVW, Theorem 7.20:
for a homotopy-invariant additive presheaf with transfers killed by a positive
integer invertible in the base field, prove that its actual étale
sheafification comes from the base field's small étale site. The endpoint must
identify the counit of the actual small/smooth-site adjunction as an isomorphism.
It is not enough to construct an unrelated isomorphic group or to assume a
rigidity, Picard-divisibility, or proper-comparison certificate.

The source is Colib's existing `PresheafWithTransfers`, correspondence category,
`Scheme.SmoothSite`, motivic complex and finite-coefficient cone. Ordinary
small-site étale cohomology and proper base change are the pinned Stacks objects.
Comparisons must retain the original graph actions, coefficient maps,
cohomological shifts and signs.

## Current contributions

- COL-1028 constructs the actual étale topology on Colib's smooth category and
  its refinement of the Nisnevich topology. Restriction retains literal
  presheaves and their maps.
- COL-1029 proves surjectivity of the power map on units of any module-finite
  algebra over a strictly henselian local ring. It directly reuses native
  henselian decomposition, strictness of the factors and simple-root lifting.
  Finite algebras need not be reduced, local, flat or nonzero.
- COL-1030 assembles native unconditional proper base change and the native
  effaceability criterion into bijectivity of the canonical closed-fibre
  restriction for finite-exponent abelian sheaves over a strictly henselian
  base. It does not assume the injective-fibre acyclicity criterion it uses.
- COL-1031 constructs the canonical Picard Kummer class and injection
  `Pic(X)/n → H²(X, μ_n)`, proves pullback naturality, and reflects
  `n`-divisibility of Picard classes from the proper closed fibre. A native
  representative argument then produces an actual global tensor root from
  existence of a fibre tensor root, without claiming the chosen fibre root
  extends. No vanishing of `H²(X, Gm)` is assumed.
- COL-1032 uses native semilocal triviality to obtain a frame on a module-finite
  affine boundary, then adjusts it to realize a specified trivialization of
  the tensor power. No initial frame is assumed. The tensor-power equation
  holds on the original, possibly nonreduced scheme.
- COL-1033 constructs ordinary Nisnevich-to-étale change of topology on the
  same smooth category. The adjunction retains the canonical sheafification
  unit and counit and inherits finite-limit/colimit preservation and
  additivity under the precise native coefficient hypotheses.
- COL-1034 assembles native Jacobian, representability, étaleness and point-lifting
  theorems into degree-zero Picard divisibility on a smooth proper curve over
  a separably closed field. The actual additive
  equivalence between the two Picard models transports the root equation,
  and native representatives give an invertible module and tensor-power
  isomorphism. No Jacobian theory is reimplemented.
- COL-1035 computes the degree of the literal `O(D) ⊗ O(-E)` from the full
  scheme lengths of the divisors and produces its actual tensor root.
  For section kernels, native Cartier theory and image factorization supply
  both the Cartier instances and length one. Nilpotent multiplicities are
  retained throughout.
- COL-1036 proves equality of actual affine-cylinder endpoint transfer actions
  on ordinary HI coefficients. Its torsion consumer preserves the original
  graph restrictions and an explicit signed endpoint difference. It does not
  supply the required geometric principal family or moving-divisor identity.

- COL-1037 combines an actual global tensor root, the native tensor-power
  pullback comparison and finite-boundary frame adjustment. Its higher
  endpoint obtains the root by proper Kummer specialization and retains
  the exact equation with the specified boundary trivialization.
- COL-1038 identifies the actual section-kernel divisor difference under
  arbitrary base change of a separated smooth relative curve. Section-image
  geometry supplies both Cartier conditions; the inverse-image ideals are
  identified literally, without a flatness or reducedness assumption.
- COL-1039 constructs the literal principal polynomial family, its actual
  unit open and full-boundary normalization. Properness and quasi-affineness
  prove that every nonzero native principal-cycle support is finite over
  the unchanged affine parameter base. It does not assume that finiteness.
- COL-1040 combines the actual closed-curve root, relative divisor pullback,
  proper Kummer specialization and the specified boundary trivialization
  away from the section images. It produces a global root with a compatible
  frame without an external Picard, degree, Cartier, fibre-root or frame
  certificate. The closed fibre's native IsCurve hypothesis remains explicit.

- COL-1041 proves actual component dominance of the finite principal supports
  and constructs the signed native finite correspondence from the polynomial
  cylinder. Each summand is the actual finite pushforward with its original
  order and residue degree; equal image points accumulate their coefficients.
  Neither finiteness nor dominance is passed in as a cycle certificate.

- COL-1042 produces a uniform large-twist bound for actual global-section
  surjectivity of any coherent epimorphism on native projective space.
  Coherent-kernel Serre vanishing supplies the bound, rather than appearing
  as a caller-supplied cohomology certificate. A lower boundary lemma proves
  that a section framed to one on the whole boundary has a finite whole
  zero scheme under the proper/quasi-affine-complement hypotheses.
- COL-1043 identifies full local cuts by the actual endpoint stalk kernels:
  numerator-minus-denominator lengths cancel at zero and equal the original
  native order at one. The polynomial cylinder and its actual evaluation
  sections are also identified with the existing native affine-cylinder
  maps.

- COL-1044 transports the Serre bound through actual affine pushforward and
  the closed-immersion projection formula. It produces simultaneous global
  sections with any prescribed values on the full closed boundary, and
  literal boundary-frame coordinates equal to one. The projective
  presentation is a closed embedding; COL-1046 supplies regularity and
  relative flatness of the zero schemes under the smooth-open hypotheses.
- COL-1045 constructs a regular generator of the actual polynomial endpoint
  stalk kernel and identifies weighted native endpoint-stalk Tor with the
  full cut length. Multiplicities are localized lengths of the original
  principal quotient, not of its reduction. Its signed values cancel at
  zero and recover the original order at one. The remaining graph-incidence
  and finite-pushforward coefficient comparisons are not assumed.
- COL-1046 proves that locally principal quasi-finite subschemes of smooth
  relative curves are relative Cartier divisors over arbitrary bases.
  Applying this to the actual boundary-normalized sections produces whole
  finite locally free zero schemes and actual divisor pairs. Smoothness is
  needed only on the retained open. The simultaneous pair remains
  conditional on its two full-boundary twist frames.
- COL-1048 constructs those frames compatibly with the fixed original frame
  over a module-finite boundary of a local ring. Only the auxiliary twist
  frame is chosen. The numerator is a section of the tensor product and
  the denominator is a section of the actual auxiliary twist, transported
  through the native unitor, with the corresponding exact boundary values.
- COL-1047 constructs the actual tensor quotient of regular meromorphic
  numerator and denominator sections on an integral scheme. Its positive
  native tensor powers give the literal Weil-divisor identity with correcting
  ratio c/alpha((a/b)^n), including the plus-principal sign. Local
  noetherianity is explicit. COL-1050 supplies the canonical Cartier
  difference section; its full-boundary frame comparison is separate.
- COL-1049 compares the original four-factor graph incidence Tor with
  actual endpoint-ambient and original support stalk Tor in every degree.
  The full graph pullback, point transports and scalar actions are retained;
  flatness belongs only to the ambient projection. Original multiplicity
  weights and both finite-pushforward residue-degree sums remain separate.
- COL-1050 constructs the canonical regular meromorphic section of the
  literal differenceSheaf, with full original quotient-length coefficients.
  Under global noetherianity its native Weil divisor is exactly D minus E.
  The original section-kernel specialization derives its Cartier hypotheses.
- COL-1051 identifies native Cartier Weil cycles with the whole zero-scheme
  fundamental cycles and finite-flat correspondences. It preserves actual
  source-target maps, all residue degrees and image collisions, identifies
  section kernels with their original graphs, and transports a lower Weil
  identity additively. Actual compactification-to-open restriction remains.
- COL-1052 constructs the ordinary quotient on the original denominator's
  nonvanishing open over arbitrary schemes, with literal tensor recovery.
  Under the explicit integral hypotheses its germ is the same meromorphic
  quotient. The prescribed denominator frame places the entire boundary
  in this open, and tensor recovery gives coordinate one in the original
  frame of the quotient module, including all nilpotents.
- COL-1053 produces a genuine stalk fraction for the same nonzero rational
  function and identifies its original orders with signed localized
  principal-quotient weights. COL-1056 matches the literal polynomial
  chart and proves the required endpoint germs.

- COL-1054 derives the actual section-kernel Cartier property from a smooth
  open and identifies the difference of equal specialized section morphisms
  with the unit module. The ambient compactification need not be smooth.
- COL-1055 uses this explicit unit-fibre root, proper Kummer reflection and
  finite-boundary frame correction. This high-level minimal route has now
  compiled in native CI; no Jacobian or smooth-proper compactification is
  required by this route.

- COL-1056 constructs a genuine affine fraction of the original curve
  function, proves the actual polynomial function-field identity, and
  computes both signed endpoint stalk Tor values from the same sections.
  Finite-image residue factors and collisions still need transport.

- COL-1057 constructs actual geometric affine etale neighborhood values
  as the native point fiber and proves the original colimit, refinement
  and sheafification-unit equations. Its PST tests retain the literal
  graph-transfer maps; field-value rigidity is not asserted.

- COL-1058 forms ordinary powers on the original open and proves coordinate
  one in the exact native Kummer power frame for every natural exponent.
  The original integer-power pullback comparison and root compatibility
  now compute the original target-frame coordinate on the full boundary.
  The same ordinary powers represent the positive meromorphic powers
  under the separate integral hypotheses.

- COL-1060 supplies a genuine separated finite-type basis equivalence for
  the full small etale site, including its non-quasi-compact objects.
- COL-1061 constructs the full-small/smooth adjunction and preserves its
  actual canonical unit and counit. Counit invertibility for HI torsion
  transfers is still the rigidity target.
- COL-1062 gives the actual finite full-cut coefficient projection formula
  with both original residue-degree factors and all fibre collisions,
  without support flatness. COL-1065 supplies its actual principal-image specialization.

- COL-1063 produces the actual dense common open and unit ratio from the
  original ordinary representatives. That same unit rationalizes to the
  original meromorphic ratio and pulls back to one on the full boundary.
  COL-1059 and COL-1066 provide the original canonical and root-power specialization.

- COL-1064 constructs the actual normal proper compactification from a
  finite chart over a proper Nagata target. It retains the original source,
  the full scheme-theoretic boundary pullback and both maps of its Cartesian
  square. COL-1067 supplies the finite-boundary neighborhood argument
  after shrinking the retained chart to a smaller whole-fibre smooth open.
- COL-1065 specializes finite cuts to the original principal-component
  map and native component-correspondence coefficient. Fibre coheight
  is proved, and both degree factors plus all fibre collisions are retained.
  COL-1068 identifies its section with the literal endpoint cut.

- COL-1059 proves that the original canonical difference section has
  coordinate one in the original frame on the full boundary. Its ordinary
  construction needs neither integral nor reduced schemes.
- COL-1066 produces the exact correction function c/alpha((a/b)^(k+1)),
  its literal signed Cartier/Weil identity and the same dense-open unit
  equal to one on the entire boundary. The total scheme is integral;
  the full Weil identity also assumes global Noetherianity.
- COL-1067 produces a marked base shrink making the retained-open boundary
  finite. A specified closed boundary keeps its nilpotents; the separate
  constructed complement uses its vanishing ideal.
- COL-1069 combines actual finite polynomial coordinates with native P1
  normalization and that shrink. It preserves the original coordinate maps
  and infinity pullback; finite coordinates and whole-fibre smoothness
  are supplied by COL-1073, COL-1075 and COL-1076.
- COL-1068 identifies the original image cut with the literal endpoint
  parameter and proves nonvanishing. COL-1070 identifies the actual native
  incidence Tor coefficient with its full quotient length and produces
  coheight one. COL-1071 connects the same cut with the unchanged signed
  principal component and both residue-degree factors.
- COL-1074 expands the whole endpoint-graph pairing through both actual
  finite maps, retaining all original support and image collisions.
  The local-prime/order comparison with whole endpoint cycles remains.

- COL-1072 restricts the literal framed Cartier identity to the retained
  open and its actual native finite correspondences. COL-1079 supplies the
  compatible geometric pair and all whole finite-flat zero schemes
  internally, producing the relation between the two original graphs.
  Its compatible root/frame and the polynomial endpoint comparison remain.
- COL-1073 proves the local differential criterion for the unchanged
  coordinates. COL-1075 produces one simultaneous quadratic tuple over an
  infinite field. COL-1076 proves the actual finite coordinate maps for
  this same tuple and the full prescribed closed scheme, then constructs
  the native normal proper curve and its finite retained boundary shrink.
  No finite coordinates or whole-fiber smoothness are assumed in this chain.
- COL-1077 computes the signed local support cuts. COL-1078 supplies their
  hypotheses from the original polynomial chart and proves the zero/one
  values. COL-1080 reindexes the original principal-cycle supports by the
  actual nonzero local-prime terms. COL-1081 uses normal-base going down
  to place generic points of the full endpoint fiber in the actual finite
  target, without support flatness. COL-1083 proves the actual endpoint
  generic-point/source-fiber bijection with both original residue degrees.
  Its specialization to the polynomial graph incidence and full local
  lengths, and the final assembly into COL-1074, are still unfinished.

- COL-1082 identifies the original marked affine neighborhoods with the
  native strict henselization through an actual fully faithful initial
  functor. The original structure-map and geometric-mark equations survive
  restriction and a universe-small cofiltered reindexing. Here the native
  geometric-point field is algebraically closed. Continuity of the transfer
  presheaf and descent of the particular framed curve data remain separate.

- COL-1084 supplies the original polynomial coordinates, normal base ring
  and canonical endpoint fiber square internally for the source-fiber
  reindexing. COL-1086 identifies each actual endpoint Tor cycle with
  the whole incidence fundamental cycle and its native graph-fiber finite
  pushforward. The full signed principal-support sum remains to be assembled.
- COL-1085 proves conservativity of the native geometric-point neighborhood
  family on the original smooth etale site, using all points, not only closed
  points. Its actual neighborhood-value maps detect ordinary abelian sheaf
  isomorphisms in universe u+1. It does not identify these values with field
  evaluations or compute the small/smooth counit.

These statements are separate from the final rigidity theorem. Source
correspondence, native compilation and independent mathematical review are
different checks; a source candidate or an item entry is not a completed
whole-program validation report.

- COL-1088 constructs the whole finite-flat transpose in the existing
  correspondence category and proves its actual graph-transfer degree
  identity. COL-1091 proves injectivity of finite pushforward under universal
  injectivity, then cancels the original graph to obtain the opposite
  identity. Full inseparable residue degrees are retained, without replacing
  the self-fiber product by its reduction.
- COL-1094 proves that the full radicial residue degree is a power of the
  original field's exponential characteristic and constructs the actual
  inverse of the original graph pullback on prime-to-characteristic torsion
  sections. The inverse is a native Bezout coefficient times the actual
  transpose transfer. This does not yet supply field-change equivalence.
- COL-1089 identifies the whole original endpoint graph pairing with the
  signed sum of full original source endpoint fundamental cycles. COL-1090
  derives the original curve and chart coheight from generic-fiber smooth
  dimension and the actual finite dominant endpoint support. COL-1092
  evaluates the original chart support-cut sums at zero and one; COL-1096
  transports them to the original ambient supports and original curve order.
  Their assembly into the final global endpoint correspondence identity
  remains separate.
- COL-1095 proves conservativity of the closed residue-geometric point
  subfamily over every quasi-separated Jacobson base, in particular any
  field. Actual closed specialization and open etale images construct the
  original covering sieve. This does not yet compute a rigidity stalk or
  the canonical small/smooth counit.

- COL-1087 descends an actual invertible tensor root and its specified
  power isomorphism from a qcqs inverse limit to a common finite stage.
  The canonical comparison square and finite prescribed section equations
  are retained. The full boundary-frame diagram is a further descent step.
- COL-1093 constructs actual pullback of affine neighborhood values and the
  original affine-space projection/zero-section split maps. Both formulas
  on original representatives and the native algebraic-closure origin
  markings are retained. The reverse composite remains the S1/S2 task.

- COL-1097 identifies the full signed source endpoint cycle coefficient
  at every original curve point with the original ambient support-cut sum.
  An internally chosen affine chart gives zero and the original curve order
  at coheight-one points. The remaining global equality must prove that all
  contributing supports have that codimension and preserve the outer map.

- COL-1098 constructs the original smooth relative Frobenius and its
  native twist over any positive-characteristic field. Actual finiteness,
  flatness, universal injectivity and integral twist supply COL-1094's
  hypotheses, giving the original n-torsion PST restriction isomorphism.
  This is still objectwise, not the purely inseparable field-change theorem.
- COL-1099 identifies the actual canonical counit on marked neighborhood
  values with the original Kan counit. On generators it is the unchanged
  original restriction map. Native small-site stalks on that same smooth
  object agree with these values. The stronger base-source point comparison
  and final rigidity are separate.

- COL-1100 closes the actual principal-family endpoint comparison: the
  original finite correspondence composed with its zero graph is zero;
  its one endpoint has exactly the original retained principal-divisor
  pushforward cycle. Full boundary geometry supplies every required support
  codimension, and actual outer maps retain all multiplicities and signs.
  No Chow quotient or supplied endpoint identity is used.
- COL-1102 proves canonical invariance of the original neighborhood value
  under compatible marked affine etale change of chart. Its forward map
  is literally COL-1093's pullback, and the original base-value structural
  map commutes with it. This does not yet prove henselian induction.

- COL-1101 descends the original full-boundary frame and finite power and
  section equations to one common stage. Literal base-change diagrams are
  constructed internally. The specific Kummer root witness and the
  integer/natural power comparison still need to be assembled with it.
- COL-1103 extends the actual radicial transfer inverse to all original
  smooth objects, including empty and disconnected schemes, by the genuine
  finite clopen correspondence matrix. The original relative Frobenius
  pullback is a natural isomorphism on the original underlying presheaf.
- COL-1104 computes the actual smooth-extension source stalk as the native
  small-base stalk at the original composite marking, without requiring
  the smooth object to be affine. Its coefficient naturality is proved;
  counit-map identification and marked-object naturality remain separate.
- The supporting rational-marking theorem lifts an actual marked etale
  point over a rational point of a separably closed field, preserving both
  original scheme-map equations.

## Remaining mathematical chain

The required henselian section comparison is the same-specialization case:
the two sections have the same closed-fibre morphism. Their divisor difference
restricts to the actual unit module by COL-1054, and general proper
Kummer divisibility reflection suffices. The arbitrary-section closed-curve
root route in COL-1034 and COL-1040 is stronger than this need and assumes
smoothness of the whole compactification. It must not be applied directly
to the normal proper compactification with only a smooth open supplied by
the original geometric construction. COL-1054 derives the global
section-kernel Cartier property locally on that smooth open and proves
the exact closed-fibre unit comparison. COL-1055 assembles the minimal
root route and has compiled in native CI. The stronger COL-1040 composition
retains a separate closed-fibre instance elaboration repair.

1. Complete native verification of the high cohomological and curve
   compositions. COL-1038 supplies the actual relative divisor/base-change
   identification, and COL-1040 composes the closed-curve and proper Kummer
   root constructions under their stated stronger hypotheses. For the
   required same-fibre comparison, validate the direct closed-fibre unit
   route in COL-1055. The low pullback comparisons have focused compile
   evidence; the larger high-level compositions remain separately tracked.
2. Convert the constructed framed root into finite-flat effective divisor
   data and a principal correspondence identity, preserving full scheme
   lengths, signs and the original graph maps. The boundary trivialization
   is already constructed by literal inverse-image unit ideals and native
   evaluation; it is not a remaining caller-supplied certificate. COL-1044
   supplies the actual prescribed section pair for a projective closed
   embedding, and COL-1046 produces Cartier regularity and finite local
   freeness of the whole zero schemes. COL-1048 constructs the twist frames
   compatibly with the fixed original root frame. The actual regular
   quotient and its signed Weil-divisor formula are supplied by COL-1047
   on integral locally noetherian schemes. COL-1050 identifies c with the
   canonical section difference, COL-1052 supplies the ordinary quotient
   representative, and COL-1051 supplies the actual cycle/correspondence
   transport. COL-1059 completes the original full-boundary frame coherence,
   and COL-1066 produces the exact signed identity with its same normalized
   correction unit. COL-1072 restricts this identity to the original retained open and
   its native correspondences. COL-1079 selects the geometric pair
   internally and gives the actual relation between the original graphs.
3. Complete the geometric principal-family correspondence and its actual
   Tor endpoint identities. COL-1039 supplies full-boundary normalization
   and finiteness of the native supports. COL-1041 supplies component
   dominance, residue-degree pushforward and the signed correspondence.
   COL-1043 supplies the actual local cut-length endpoint values; the native
   affine-cylinder and evaluation-map identification is also implemented.
   COL-1045 supplies the weighted actual endpoint-stalk Tor/local-length
   comparison. COL-1049 supplies the actual graph-incidence stalk comparison
   in the unchanged adjacent ambient. COL-1053 supplies original orders
   as localized principal weights. COL-1056 supplies the genuine affine
   fraction, the original polynomial chart identity and both endpoint
   germs. COL-1068 identifies the literal endpoint cuts, COL-1070 proves
   the actual incidence Tor formula and coheight one, and COL-1071 connects
   the original finite-image coefficients. COL-1074 retains every original
   support, both finite residue degrees and all outer image collisions in
   the whole pairing. COL-1077 and COL-1078 compute the original signed local weights,
   and COL-1080 reindexes the actual principal-cycle supports. COL-1089
   identifies the whole pairing with the original source endpoint cycles;
   COL-1090 supplies original chart coheight, and COL-1092 and COL-1096
   give the actual chart and ambient support-cut zero/one values. COL-1100 now assembles
   these into the final original endpoint correspondence equality. COL-1036 supplies the final
   ordinary HI/torsion action consumer once the actual family and moving
   relation are constructed. A full framed Picard group or general Picard
   pairing is not needed if this concrete identity proves section comparison.
4. COL-1057 supplies the actual filtered affine etale neighborhood value,
   common-stage equations and the canonical sheafification-unit isomorphism.
   COL-1069 supplies the native geometric consumer of finite polynomial
   coordinates and a whole-fibre smooth open. COL-1073, COL-1075 and
   COL-1076 now produce these from the same original tuple over an infinite
   field, with the full prescribed closed scheme. COL-1082 identifies
   the actual affine-neighborhood limit with native strict henselization
   and preserves the original base and marking. Descend finite
   presentation data to a common stage, prove the henselization induction
   and pass to the conservative closed geometric point family supplied by
   COL-1095. COL-1088 and COL-1091 give both actual radicial transfer
   degree identities. Complete the arbitrary-field inseparable comparison
   separately;
   do not silently retain a perfect-field assumption in the final target.
5. COL-1060 and COL-1061 supply the actual full-small/smooth ordinary
   adjunction, separately from COL-1033 on the same smooth category.
   Prove its canonical counit invertible for the original HI n-torsion
   transfer presheaf after actual etale sheafification, for every field k
   and every positive n invertible in k. This is the fixed-exponent
   MVW 7.20-type target of the attached rigidity plan. A derived or motivic
   comparison, including the finite-coefficient cone and signed motivic
   complex, is a downstream application rather than an extra completion
   condition for this rigidity theorem. The existing weight-one field
   equivalences are not themselves this small/smooth counit assertion.

The old plan's independent formal-functions/proper-base-change development is
not part of this route: the required unconditional theorem is already in the
pinned Stacks library. Likewise, existing native Kummer naturality and finite
henselian algebra results are used directly instead of being reimplemented.

## Verification boundary

The focused tests use the precise native objects and maps, independent
coefficient universes where supported, composite exponents, the exponent one,
and the zero finite algebra. Production contains no new axioms or placeholders.
The full native build, tests, declaration/text lint, generated-entry check,
production axiom audit and Library export are owned by `scripts/check.sh`
and the existing CI. Kernel replay is not part of this work.
