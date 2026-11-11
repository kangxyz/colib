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

These statements are separate from the final rigidity theorem. Source
correspondence, native compilation and independent mathematical review are
different checks; a source candidate or an item entry is not a completed
whole-program validation report.

## Remaining mathematical chain

1. Construct the actual section-divisor difference and prove it has a tensor
   root on the closed curve. COL-1031 then supplies an ordinary global line
   bundle root with its tensor-power isomorphism. The closed-curve root producer
   and the connection to the actual section divisors remain to be built.
2. Construct the prescribed trivialization on the actual finite boundary and
   identify the pullback of the root's tensor power with the tensor power of
   its actual pullback. COL-1032 then supplies the exact compatible frame,
   including on the original nonreduced boundary.
3. Convert that framed root into finite-flat effective divisor data and a
   principal correspondence identity. Preserve scheme-length multiplicities,
   signs and the original graph maps. Evaluate the identity using additivity,
   annihilation by `n` and actual homotopy-invariant principal nullity.
   A full framed Picard group or general Picard pairing is not a prerequisite
   if this concrete identity supplies the needed section comparison.
4. Define values on geometric henselian bases by the actual filtered
   neighborhood colimit. Descend the finite presentation data to a common
   stage, prove the henselization induction and pass to conservative étale
   stalks. Handle the arbitrary-field inseparable comparison separately;
   do not silently retain a perfect-field assumption in the final target.
5. Use COL-1033 to extend ordinary change of topology to the required
   transfer and derived constructions, preserve its canonical unit and the
   finite-coefficient cone, and connect the existing signed motivic complex
   to the native small-site coefficients. The integral and finite weight-one
   field equivalences already in Colib are not themselves this comparison.

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
