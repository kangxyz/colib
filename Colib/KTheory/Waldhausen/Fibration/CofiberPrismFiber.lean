/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberObjectSquare
public import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberPrismComposition
public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectIdentitySquare

/-!
# The actual quotient face of the cofiber prism in the canonical fiber

The coarse weak equivalence of the original zero-to-quotient arrow follows from gluing.
Its actual continuous square is the reversed fiber coordinate of the unchanged canonical
fiber map. This preserves both original parameters and does not identify a localization boundary.
-/
/-! Implementation provenance: Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
All three declarations from `Quillen/Waldhausen/Fibration/CofiberPrismFiber.lean:33-70`.
The displayed quotient, gluing certificate and both original independent times are retained.
Independent category universes and all original hypotheses are preserved.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology Convexity unitInterval
open CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {V : Structure C}
  (N : NestedWeakEquivalences V) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : N.coarse.cof i) (hwi : N.coarse.weq i)
  (hQ : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q))

/-- The original quotient becomes an actual relative-acyclic object by the displayed pushout. -/
def cofiberPrismAcyclicQuotient : AcyclicCategory N :=
  ⟨Q, by
    have hz : N.coarse.isZero.to_ Q = (0 : N.coarse.zero ⟶ Q) :=
      N.coarse.isZero.eq_of_src _ _
    change N.coarse.weq (N.coarse.isZero.to_ Q)
    rw [hz]
    exact cofiberTwo_quotient_weak N.coarse i q hi hwi hQ⟩

/-- The entire original quotient face is the canonical fiber coordinate with reversed time. -/
theorem cofiberPrismRealization_quotient_fiber (t s : unitInterval) :
    N.coarse.cofiberPrismRealization i q hi hwi hQ
        ((StdSimplex.homeomorphI.symm t).map (SimplexCategory.δ 0), unitInterval.symm s) =
      (canonicalFiberObjectLoop N (cofiberPrismAcyclicQuotient N i q hi hwi hQ) t).val.2 s := by
  rw [N.coarse.cofiberPrismRealization_quotient_face, canonicalFiberObjectLoop_path_square]
  have hz : ((zeroToAcyclicInclusion N).app
      (cofiberPrismAcyclicQuotient N i q hi hwi hQ)) = (0 : N.coarse.zero ⟶ Q) :=
    N.coarse.isZero.eq_of_src _ _
  simp only [hz]

/-- The translated quotient face retains the actual source object prefix and reversed fiber path.
-/
theorem cofiberPrismCompositionCube_zero_fiber (t s : unitInterval) :
    N.coarse.cofiberPrismCompositionCube i q hi hwi hQ (0, unitInterval.symm s, t) =
      if h : (t : ℝ) ≤ 1 / 2 then
        N.coarse.kZeroObjectLoop A
          ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else
        (canonicalFiberObjectLoop N (cofiberPrismAcyclicQuotient N i q hi hwi hQ)
          ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩).val.2 s := by
  rw [N.coarse.cofiberPrismCompositionCube_comparison_zero]
  split_ifs with h
  · exact N.coarse.weakObjectIdentitySquare_realization A _ _
  · rw [canonicalFiberObjectLoop_path_square]
    have hz : ((zeroToAcyclicInclusion N).app
        (cofiberPrismAcyclicQuotient N i q hi hwi hQ)) = (0 : N.coarse.zero ⟶ Q) :=
      N.coarse.isZero.eq_of_src _ _
    simp only [hz]

attribute [colib_tag "COL-0297"] cofiberPrismRealization_quotient_fiber
  cofiberPrismCompositionCube_zero_fiber

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/CofiberPrismFiber.lean:33-70" "adaptation"
  "The literal quotient made acyclic by gluing, its complete realized quotient face and
    source-loop prefix in the canonical fiber; only fiber time is reversed and loop time
    remains independent, with no fibration or canonical-comparison weakness premise"]
  cofiberPrismAcyclicQuotient cofiberPrismRealization_quotient_fiber
  cofiberPrismCompositionCube_zero_fiber

end CategoryTheory.Waldhausen.Fibration
