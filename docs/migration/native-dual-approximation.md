# Native compatible duality and dual approximation

## Mathematical scope

COL-0308 is a general categorical theorem. Compatible dual Waldhausen structures
have weak classes related by the literal opposite morphism and zero-corner
cofiber squares related to actual fiber squares. No S-comparison or K-equivalence
is an input to this compatibility.

Reversal changes all three coordinates of the original quotient grid. The two
reversals are inverse on the actual diagrams, conjugate every simplex operator,
and give a simplicial-set isomorphism. The existing native realization of
opposite simplicial sets then gives the actual homeomorphism. Its whole
naturality square transfers weakness of the opposite exact-functor S-map to
the original S-map, without choosing a homotopy inverse.

Strict incoming factorization is ordinary App2 for the actual opposite functor.
Dual approximation therefore gives a weak homotopy equivalence of the original
delooping and bijectivity of its canonical KMap in every nonnegative degree,
including K-zero. The induced group equivalence has exactly that KMap as its
forward homomorphism. The existing canonical image-zero rebasing remains in
use; no strict preservation of the chosen zero is added.

For exact functors F : C → D and G : D → E, the inverse-image weak classes
are tested on the literal maps G(F(f)) and G(g). The same F is exact between
these two structures. Fine incoming lifts preserve their strict equation after
enlarging the weak classes. Reflection in the enlarged classes is definitional,
so no reflection of the fine weak class is assumed in the final lifting theorem.
Only the final target weak class must satisfy two-out-of-three.

The dual source still requires genuine fine exact joint-cylinder data. The
categorical JointRetarget owner first embeds its fine-weak projection in the
nested weak class, then invokes the proved COL-0306 coarse construction.
Coarse exactness is derived by actual endpoint coproduct gluing and projection
naturality with two-out-of-three. It is not inferred from fine exactness alone.
The original joint arrow, both endpoints and projection remain unchanged.

## Source crosswalk

Original revision: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.

| Original source | Native owner | Retained result |
| --- | --- | --- |
| Waldhausen/Duality/Basic.lean | CategoryTheory/Waldhausen/Duality/Basic.lean | Literal structural compatibility |
| Waldhausen/Duality/SConstruction.lean | CategoryTheory/Waldhausen/Duality/SConstruction.lean | All grid reversals, simplex naturality, actual comparison and weak-map transfer |
| Waldhausen/Duality/InverseImageWeak.lean | CategoryTheory/Waldhausen/Duality/InverseImageWeak.lean | Compatibility for genuine inverse-image weak classes |
| Waldhausen/Approximation/Dual.lean, structural part | CategoryTheory/Waldhausen/Approximation/Dual.lean | Dual App1/App2, opposite ordinary approximation and saturation |
| Waldhausen/Approximation/Dual.lean, K-theoretic part | KTheory/Waldhausen/Approximation/Dual.lean | Original delooping weakness, KMap bijectivity and group equivalence |
| Waldhausen/Fibration/Rows/JointRetarget.lean | CategoryTheory/Waldhausen/Fibration/Rows/JointRetarget.lean | Fine-to-nested-to-coarse joint data with literal maps |
| Waldhausen/Approximation/DualInverseImage.lean, structural part | CategoryTheory/Waldhausen/Approximation/DualInverseImage.lean | Original inverse-image exact functor and dual approximation |
| Waldhausen/Approximation/DualInverseImage.lean, K-theoretic part | KTheory/Waldhausen/Approximation/DualInverseImage.lean | Original relative KMap bijectivity |
| Waldhausen/Approximation/DualInverseImageLift.lean, structural part | CategoryTheory/Waldhausen/Approximation/DualInverseImageLift.lean | Coarse dual approximation from strict fine incoming lifts alone |
| Waldhausen/Approximation/DualInverseImageLift.lean, K-theoretic part | KTheory/Waldhausen/Approximation/DualInverseImageLift.lean | KMap bijectivity from fine incoming lifts without fine reflection |

All native paths begin with Colib/. The structural and K-theoretic parts of
Dual.lean and the inverse-image modules are separated by their mathematical owners. Original mathematical
statements and proof bodies are retained; imports and namespaces use native
Colib, Mathlib and Stacks dependencies. No production Quillen or Aglib import
is introduced. Source attribution is separate from a claim about literature.
The ordinary approximation input is COL-0256, with its documented adaptation
of Waldhausen, *Algebraic K-theory of spaces* (1985), Theorem 1.6.7.

Object and morphism universe bounds remain independent. The categorical
incoming-factorization construction also permits different source and target
bounds. The original S-map comparison and K-theoretic conclusions retain their
shared source/target bounds; this migration does not silently generalize them.

## Scope boundaries and verification

This is not a geometric fine-localization theorem. No compatible duality for
native perfect complexes, geometric incoming-lift construction, qcqs extension
or density result, fine open K-zero surjectivity, or nonconnective localization
is asserted. Duality/ExactCategory and Duality/ComplexSubcategory, and the separate
WeakArrow development, are outside this contribution.

The in-package tests WaldhausenDuality and WaldhausenDualApproximation check
whole simplex naturality, the literal S-map square, dual App2 in independent
universes, inverse-image predicates, the unchanged KMap in all degrees and
K-zero separately, and the fine-lift endpoint without fine reflection or
intermediate-target saturation. They also check literal coarse joint maps.
Local compilation, exact source/artifact verification, independent mathematical
review and remote native lint/axiom audit are distinct verification stages.
