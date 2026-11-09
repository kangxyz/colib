# Supported connective image cover (COL-0335)

The mathematical source is Thomason–Trobaugh, Theorem 5.1.2 and proof 5.2,
pp. 337–338, in the fixed-pair compact-union setting. This is distinct from the
ordinary open localization of Theorem 5.1.1. Existing bibliography entries
`ThomasonTrobaugh1990`, `Waldhausen1985`, and `quillen` retain their identities.

Let V be perfect complexes on X acyclic on T, C its coarse Waldhausen structure
whose weak equivalences become quasi-isomorphisms on U, and B perfect complexes
on U acyclic on the inverse image of T. Their original S-prespectra define the
actual maps q : K(V) → K(C) and r : K(C) → K(B). The exact supported restriction
f : K(V) → K(B) satisfies q;r ~ f by canonical chosen-zero normalization and
exact-functor composition coherence. The actual original K-maps are retained.

The source of the fiber comparison is perfect complexes on X acyclic on
T union image(j). Literal exact flattening identifies it with the acyclic
category of V → C, preserving the inherited zero. Precomposition of the whole
canonical acyclic nullhomotopy yields the specified fiber path. Its structure
square uses independent parameters s and t, at every n including n = 0.
The comparison is the actual homotopy-fiber lift; it and its canonical rebase
into the same fiber are stable equivalences in every integer degree. The
level-one homeomorphism and induced piMap recover `perfectSupportedUnionFiberKMap`.

COL-0334's fine supported comparison supplies positive bijectivity and exact
zero image. The strong hypothesis is qcqs X and compact image(j) union T,
not compact U alone. COL-0333 supplies the geometry. No abstract spectrum
profile, roof, density or complement field is assumed by the endpoint.

## Source correspondence

The frozen original Quillen source revision is
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

- `PerfectComplexes/SupportedOpen/Fibration.lean`, `Support.lean`, and
  `Restriction.lean`: actual supported coarse objects, flattening and restriction,
  already owned by COL-0331.
- `PerfectComplexes/SupportedOpen/GlobalCofinality.lean:40–96` and
  `KZeroImage.lean`: the actual fine image/profile owned by COL-0334, transported
  here through the original stable K-equivalences.
- `PerfectComplexes/SupportedOpen/GlobalLocalization.lean:40–164`: the retained
  fine boundary and K1-to-K0 sequence; reused, not redefined.
- `Waldhausen/Fibration/Prespectrum.lean` and `SpectrumComparison.lean`: the
  native canonical fiber/nullhomotopy infrastructure specialized to the actual
  supported nested weak equivalences. The literal prespectrum transport follows
  COL-0319's native implementation pattern with a different ambient category.

## Limits

The later support-forgetting boundary and inverse-comparison naturality in
`GlobalLocalization.lean` are not proved here. Neither arbitrary global open-pair
naturality, general two-piece supported gluing, nor Bass nonconnective TT 7.4
is claimed. Ambient perfect complexes acyclic on an open are not replaced by
perfect complexes on a closed subscheme. This topic does not identify a signed
stable connecting homomorphism with the fine group boundary.
