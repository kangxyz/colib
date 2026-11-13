/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.AffineLineFiberComponentCoefficient
import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-!
# Colength of a finite closed cut over a source face

Base changing a finite closed cut along a Cartesian source face gives a
finite scheme over the new source. At a point over the generic source
the double cut thus has finite colength in the original ambient stalk.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Scheme.AffineLineFiber

variable {k : Type u} [Field k] {P E X Y : Scheme.{u}} [IsNoetherian P]

/-- At a generic source point of the face, the actual double-cut ideal of
a finite closed cut has finite colength in the original stalk. -/
theorem doubleCut_length_ne_top_of_finite
    (f : P ⟶ Spec (.of (Polynomial k))) (a : k) (j : E ⟶ P) [IsClosedImmersion j]
    (p : P ⟶ Y) (φ : X ⟶ Y) (v : fiber f a ⟶ X)
    (hv : IsPullback v (inclusion f a) φ p) [IsFinite (j ≫ p)]
    (x : fiber f a) (hx : v x ∈ genericPoints X) :
    Module.length (P.presheaf.stalk (inclusion f a x))
      (P.presheaf.stalk (inclusion f a x) ⧸
        (Ideal.span {scalar f a (inclusion f a x)} ⊔
          IdealSheafData.stalk j.ker (inclusion f a x))) ≠ ⊤ := by
  let i := inclusion f a
  let d := fiberMap f a j
  let : IsNoetherian (fiber (j ≫ f) a) := isNoetherian_of_finiteType (d ≫ i)
  let : IsFinite (d ≫ v) :=
    MorphismProperty.of_isPullback ((fiberMap_isPullback f a j).paste_horiz hv).flip
      (inferInstance : IsFinite (j ≫ p))
  have hfin := closedImmersionQuotientStalkLength_ne_top v d x hx
  have hlen : closedImmersionQuotientStalkLength (d ≫ i) (i x) =
      closedImmersionQuotientStalkLength d x := by
    by_cases hd : x ∈ Set.range d
    · obtain ⟨y, rfl⟩ := hd
      change closedImmersionQuotientStalkLength (d ≫ i) ((d ≫ i) y) =
        closedImmersionQuotientStalkLength d (d y)
      rw [closedImmersionQuotientStalkLength_image, closedImmersionQuotientStalkLength_image]
    · have hi : i x ∉ Set.range (d ≫ i) := by
        rintro ⟨y, hy⟩
        exact hd ⟨y, i.isClosedEmbedding.injective hy⟩
      rw [closedImmersionQuotientStalkLength_eq_zero_of_notMem_range _ _ hi,
        closedImmersionQuotientStalkLength_eq_zero_of_notMem_range _ _ hd]
  have hc := hlen.trans_ne hfin
  unfold closedImmersionQuotientStalkLength at hc
  rw [show d ≫ i = fiberMap f a j ≫ inclusion f a from rfl, fiberMap_composite_stalk] at hc
  exact hc

end AlgebraicGeometry.Scheme.AffineLineFiber
