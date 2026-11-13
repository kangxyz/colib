# Étale comparison and Suslin rigidity

## Completed rigidity endpoint

COL-1222 registers
`AlgebraicGeometry.PresheafWithTransfers.isIso_fullSmallEtale_sheafification_counit_of_A1Invariant`
in `Colib.AlgebraicGeometry.PresheavesWithTransfers.EtaleRigidityCounit`.

Let `K` be any field and `P : PresheafWithTransfers K` the original additive
presheaf with transfers. Assume ordinary A¹-invariance, and fix `n : ℕ` such
that `(n + 1)` annihilates every original section and is invertible in `K`.
For the actual smooth-site étale sheafification `F` of its graph restriction,
the canonical counit `(fullSmallEtaleAdjunction ...).counit.app F` is an
isomorphism. This is the fixed-exponent MVW, Lecture 7, Theorem 7.20-type
small-site origin statement. It does not require `K` to be perfect.

The exponent can be composite; `n = 0` includes exponent one. The coefficient
universe is the existing `u + 1` over a field in universe `u`. The theorem
does not replace `P` by presheaves over extension fields, assume a completed
rigidity certificate, or assert an unrelated isomorphic group.

## Completed proof route

1. COL-1114 reduces invertibility of the actual counit to the original
   structural marked-neighborhood restriction at closed separable residues.
   COL-1108 identifies that map with the canonical counit. COL-1111 transports
   the same counit through actual relative Frobenius in positive characteristic;
   characteristic-zero closed residue fields are already separable.
2. The same-stage geometric construction retains the original normal proper
   curve, root, full-boundary frame, section pair, marked point and coefficient
   field through a genuine finite-type étale stage. COL-1112 and COL-1113
   supply the relevant descent interfaces. The strict henselization is not
   treated as an object of the smooth finite-type site.
3. The actual pair feeds COL-1105's general-base action theorem. The rational
   integral positive step in `RationalIntegralPositivePreimage` retains its
   original chart; `IntegralEtalePositivePreimage` reflects the preimage to
   the original étale coordinate chart. `ActualPolynomialNeighborhoodPreimage`
   supplies the corresponding original polynomial-neighborhood preimage.
4. `QuadraticIncidence.InfinityChart.polynomialTailIsomorphisms_all_dimensions`
   in `PolynomialTailSimultaneousInduction` discharges the lower-dimensional
   hypotheses by natural-number induction, simultaneously over finite
   separable coefficient fields. Structural monomorphisms and these preimages
   give isomorphisms, not just pointwise surjectivity.
5. `counit_separable_condition_of_polynomial_tails` transports the resulting
   polynomial-tail maps to the exact original affine structural-neighborhood
   condition. The final theorem applies the algebraically closed form of the
   canonical counit reduction and discharges that condition.

These are now components of the assembled theorem, not outstanding tasks.
The retained étale chart and the distinct whole-fibre smooth open stay separate.
The same-specialization root argument uses proper Kummer divisibility and the
actual unit restriction of the divisor difference. It does not silently apply
smooth-proper-curve hypotheses to a merely normal compactification.

## Library reading map and permanent IDs

Concurrent main work already owned the original numerical IDs. The rigidity
items retain their mathematical identities under the following new IDs; the
old numbers must not be used for these items:

| Earlier rigidity draft ID | Current ID | Contribution |
| --- | --- | --- |
| COL-1028 | COL-1203 | Smooth-site étale topology |
| COL-1029 | COL-1204 | Powers of units in finite henselian algebras |
| COL-1030 | COL-1205 | Proper closed-fibre étale restriction |
| COL-1031 | COL-1206 | Picard Kummer specialization |
| COL-1032 | COL-1207 | Tensor-compatible finite-boundary frames |
| COL-1033 | COL-1208 | Nisnevich-to-étale change of topology |
| COL-1034 | COL-1209 | Closed-curve tensor roots |
| COL-1035 | COL-1210 | Closed-curve divisor-difference roots |
| COL-1036 | COL-1211 | Homotopy endpoint transfer actions |
| COL-1037 | COL-1212 | Compatible finite-boundary roots |
| COL-1038 | COL-1213 | Section-kernel difference under pullback |
| COL-1039 | COL-1214 | Finiteness of principal-family support |
| COL-1040 | COL-1215 | Relative section-divisor roots |
| COL-1041 | COL-1216 | Principal polynomial correspondences |
| COL-1042 | COL-1217 | Serre lifting of sections |
| COL-1043 | COL-1218 | Principal-family endpoint orders |
| COL-1044 | COL-1219 | Closed-embedding section lifting |
| COL-1045 | COL-1220 | Weighted endpoint Tor cuts |
| COL-1046 | COL-1221 | Boundary-prescribed finite flat section pairs |

Later component IDs, including COL-1067, COL-1069, COL-1076, COL-1105 and
COL-1108 through COL-1114, are unchanged. COL-1222 is the new final endpoint,
not a replacement for the reductions or geometric input items. The Library
entries retain their individual hypotheses, source comparisons and scopes.

## Verification and publication boundary

The mathematical integration was merged at
`967b3ab00883bc3021d194d45ffb770a7ac77e11`. Its branch CI run
[43419997103](https://github.com/kangxyz/colib/actions/runs/43419997103)
passed. On main at that same revision, Build and Test/Lint/axiom checks passed;
the subsequent cache-publication checkpoint failed at the 2 GiB limit. That
publication failure is distinct from the mathematical checks. The present
Library registration is based on main
`832bf3d5cbab7bb4c9197eb5fba2e83e36a44b3a`; the endpoint source is unchanged
from the checked integration apart from this registration and documentation.
This note does not claim that the later registration already passed remote CI.

Production verification uses the existing `scripts/check.sh` and native CI
build, tests, declaration/text lint, generated-entry check, production axiom
audit and Library export. No kernel replay or independent mathematical review
is claimed by these compilation and CI results. Cache/CI configuration is
maintained separately and is not changed by this registration.

## Scope beyond this endpoint

A derived or motivic étale comparison, including the finite-coefficient cone,
roots-of-unity tensor powers and the signed motivic complex, is a downstream
application. COL-1222 does not assert those comparisons, strict A¹-invariance,
or the norm-residue or Beilinson–Lichtenbaum isomorphism theorem. The existing
weight-one equivalences are not substitutes for the canonical counit theorem.

Native proper base change, Kummer naturality and finite henselian algebra
results are reused from the pinned libraries. Their independent reimplementation
is not part of this route.
