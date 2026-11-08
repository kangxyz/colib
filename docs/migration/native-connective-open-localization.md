# Conditional connective open localization

## Mathematical result and reading route

COL-0318 continues COL-0300's actual relative coarse fibration and COL-0315's original-map
cofinality. Read `PerfectOpenLongExactSequence`, `OpenDerivedImageCofinality`,
`PerfectOpenConnectiveLocalization`, then `PerfectOpenImagePrespectrum` in
`Colib/AlgebraicGeometry/KTheory`.

The fine boundary is the original relative boundary composed with the inverse of the proved
positive relative-restriction equivalence. Its composite with the original relative restriction
is the original boundary, and this identity determines it uniquely. The three recurring
range-equals-kernel positions retain actual fine restriction and supported inclusion. At zero,
the sequence is K1(U) to K0(support) to K0(X) to K0(U), without last-arrow surjectivity. Replacing
the last group by the actual image of K0(X) in K0(U) gives the proved surjective endpoint. Both
codomain-forgetting equations and the original relative-zero comparison are explicit.

The actual coarse S-prespectrum and its canonical rebased exact restriction to the fine open
S-prespectrum have a proved stable/K-map naturality equation. Under the two geometric inputs,
positive stable groups are isomorphic and degree zero embeds with exactly the global restriction
image. Negative stable groups vanish. This is an actual model with the restriction-image
homotopy-group profile, not a structure that assumes a desired spectrum equivalence.
The specified acyclic-to-homotopy-fiber map of the original change-of-weakness prespectrum map
is an all-integer stable equivalence, by the existing native Waldhausen theorem.

## Exact hypotheses and boundary

The geometric comparison retains exactly a chosen derived-category model on U,
`Fact (OpenDerivedImage.HasDerivedRoofs j)`, and `OpenDerivedImage.HasPerfectComplements j`.
The latter demands actual native perfect complexes R on X and C on U and a derived isomorphism
between the restriction of R and P direct-sum C. Density, binary coproducts, fine joint data,
and categorical approximation are proved upstream rather than assumed here.

Geometric discharge is separate. The intended qcqs specialization has compact X,
quasi-separated X, compact U, and an open immersion. No Noetherian, regular, separated,
or resolution-property hypothesis is introduced. Uncompiled geometric drafts are not imported.

COL-0318 specializes the native fiber theorem with the acyclic category as source. Its exact
equivalence with the original supported category is already used at the group boundary. In
this integrated topic COL-0319 separately constructs the coherent supported-prespectrum fiber
transport, with the original projection, nullhomotopy, structure maps and level-one K-map.
Comparison to a separately prescribed K-zero-image-cover spectrum, global open-pair pullback
naturality and supported-open refinements remain subsequent work. No extra naturality premise
is inserted to simulate their proofs.

## Literature and source correspondence

The group boundary, exact positions and uniqueness adapt
[Quillen GlobalLocalization, lines 39–152](https://github.com/kangxyz/quillen-k-theory/blob/c561118b7795eb9780be9ed391c3251d6a4d0afd/Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalization.lean#L39-L152).
Unlike that source's geometric application, the native roof and complement existence inputs
remain explicit. The zero-image endpoint uses the actual subgroup from
[Quillen OpenKZeroImage, lines 38–65](https://github.com/kangxyz/quillen-k-theory/blob/c561118b7795eb9780be9ed391c3251d6a4d0afd/Quillen/AlgebraicGeometry/PerfectComplexes/OpenKZeroImage.lean#L38-L65).

The actual stable-map comparison uses the native migration of Quillen's
`Waldhausen/SConstruction/Iterated/StableFunctoriality.lean` and the actual fiber comparison
uses `Waldhausen/Fibration/SpectrumComparison.lean`. Waldhausen's Theorem 1.6.4, pages 350–352,
is the structural fiber theorem. TT Sections 1.5.3–1.5.4, pages 260–261, supply the cited
connective spectrum background. The degree-zero correction belongs to the connective scope
of [TT Section 5.1, printed pages 337–338](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Thomason-Trobaugh.pdf).
Section 5.2.2 describes the K-zero extension obstruction. TT Section 7.4, printed page 365,
is the later nonconnective localization theorem and is not proved here. Its support term is
K-theory on X supported away from U, not the K-theory of the closed complement itself. Integer grading of a connective spectrum does not make it Bass nonconnective.

`OpenDerivedImage/KZeroCover` concerns image-membership reflection for a covering pair.
Its use of the word cover is not a construction of a spectrum with a prescribed K-zero image.
The original relative and signed-cone boundary conventions are unchanged; this does not
identify the separate T-first Bass forward class with a different sign convention.

## Reader's crosswalk

- Original `qcqsPerfectConnectingHom`: `perfectOpenFineConnectingHom`, with explicit geometry.
- Original boundary composite and uniqueness: the corresponding `comp_relative` and `unique`
  lemmas on that boundary.
- Original three recurring positions and K-zero tail:
  `perfectOpenFine_positiveLongExactSequence` and `perfectOpenFine_zeroTail`.
- Honest terminal image: `perfectKZeroToOpenImage`,
  `relativeKZeroImageEquiv_comp_perfectOpenKMap`, and `perfectOpenFine_zeroImageTail`.
- Actual spectrum restriction: `perfectOpenRestrictPrespectrumMap` and its `naturality` lemma.
- Stable target profile: `perfectOpenRestrictPrespectrumMap_succ_bijective`,
  `perfectOpenStableZeroImageEquiv`, its `coe` equation, zero injectivity, and negative vanishing.
- Actual relative fiber theorem:
  `perfectOpen_canonicalFiberPrespectrumMap_isStableEquivalence`.

The in-package consumer `ColibTest.PerfectOpenConnectiveLocalization` records full signatures
with the native universe, degree-zero subgroup and original maps. Local compilation, literature
correspondence and independent review are separate facts. Shared registration and remote checks
belong to integration; this document does not assert that those later stages have completed.
