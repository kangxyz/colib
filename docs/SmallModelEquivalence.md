# Exact equivalences of native small Waldhausen models

COL-0357 is generic native theory. Its input is a genuine categorical equivalence,
structural exactness in both directions, and strict preservation of the forward chosen
zero. The source and target are Mathlib wide-subcategory objects over Colib's bundled
small Waldhausen category. No Aglib or legacy Model adapter occurs.

## Mathematical route

The forward arrow remains the supplied functor. Only its actual inverse is canonically
rebased at the chosen zero. Whiskering the inverse normalization isomorphism with the
original equivalence unit and counit supplies genuine weak natural transformations.
The existing native prespectrum transformation construction realizes both complete
inverse homotopies. Endpoint casts use functoriality; they do not discard level maps.
All levels, including the zeroth loop space, preserve endpoints, the whole basepoint
line, and structure maps with independent homotopy and loop coordinates. Consequently
each forward level map is an actual homotopy equivalence, and the whole forward map is
a stable equivalence. The stable conclusion is not used to infer the level conclusion.

The categorical up/down isomorphism proves the direct-small/AsSmall bridge. Its
functorial square is proved before realization; differently presented spectra are never
assumed equal. The direct-small K-to-stable comparison omits just the initial AsSmall
factor of the native original-universe construction. Its naturality and the zero-space
formula use the existing canonical K-map, for arbitrary strict exact model arrows.
For an actual equivalence to an AsSmall target, composing the all-degree canonical
K-equivalence with the inverse AsSmall K-equivalence gives the exact original target
formula. The raw mixed-universe KMap is neither formed nor generalized.

## Sources and boundaries

Implementation blueprint: Quillen/Waldhausen/SConstruction/Iterated/ExactModelEquivalence.lean
at c561118b7795eb9780be9ed391c3251d6a4d0afd, adapted to the actual native wide subcategory.
The source input is the independently reviewed section-bass-foundations-union tree
at a2d889d15ec114a6d65820ba703e9ba4b9d8a01e. Native prespectrum homotopies, canonical maps,
AsSmall transport and stable groups are reused rather than assumed or reimplemented.
Waldhausen (1985), Section 1.3, Proposition 1.3.1, supplies weak-transformation invariance
background; Thomason–Trobaugh (1990), Sections 1.5.3–1.5.4, supplies exact-functor
K-theory background. Neither reference is cited as an affine evaluation theorem here.

The consumer has two distinct objects in an indiscrete category. Both are zero objects;
the inverse functor is constant at the second, while the chosen zero is the first. Its
normalization therefore changes an actual object. This checks rebasing rather than
only the identity equivalence. No nonzero K-group claim follows from this example.
Compilation, exact provider binding, source correspondence and independent review
are separate validation facts and are recorded separately in delivery receipts.
