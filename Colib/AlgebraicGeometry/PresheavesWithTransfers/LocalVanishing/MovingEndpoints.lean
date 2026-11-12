/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.HomotopyActions

/-!
# Vanishing along a correspondence homotopy

If a correspondence homotopy joins a graph to a correspondence factoring through
an open immersion, an A¹-invariant transfer presheaf takes the two
endpoints to the same restriction of sections.

Adapted from `Motivic/Cohomology/A1/Moving/OneSided.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `7eefe9c662f450a09c220c8f2ee92299cbbe0712`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- The transfer action of the graph factors through the given endpoint correspondence. -/
theorem restriction_factor_of_moving_endpoints
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    {S X V : SmoothSite (Spec (.of k))} (f : S ⟶ X) (j : V ⟶ X)
    (β : Cor.mk S ⟶ Cor.mk V)
    (α : Cor.mk (SmoothSite.Contraction.affineLineCylinder.obj S) ⟶ Cor.mk X)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.Contraction.nativeAffineSection (.of k) S 0) ≫ α =
      (Cor.graphFunctor k).map f)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.Contraction.nativeAffineSection (.of k) S 1) ≫ α =
      β ≫ (Cor.graphFunctor k).map j) :
    transfer P ((Cor.graphFunctor k).map f) =
      transfer P ((Cor.graphFunctor k).map j) ≫ transfer P β := by
  have h := transfer_homotopy_endpoints P hP S (Cor.mk X) α 0 1
  erw [h₀, h₁, transfer_comp] at h
  exact h

/-- A section whose restriction along the second endpoint factors through a zero
restriction also vanishes along the first endpoint. -/
theorem section_zero_of_moving_endpoints
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    {S X V : SmoothSite (Spec (.of k))} (f : S ⟶ X) (j : V ⟶ X)
    (β : Cor.mk S ⟶ Cor.mk V)
    (α : Cor.mk (SmoothSite.Contraction.affineLineCylinder.obj S) ⟶ Cor.mk X)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.Contraction.nativeAffineSection (.of k) S 0) ≫ α =
      (Cor.graphFunctor k).map f)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.Contraction.nativeAffineSection (.of k) S 1) ≫ α =
      β ≫ (Cor.graphFunctor k).map j)
    (s : sections P (Cor.mk X)) (hs : transfer P ((Cor.graphFunctor k).map j) s = 0) :
    transfer P ((Cor.graphFunctor k).map f) s = 0 := by
  have h := ConcreteCategory.congr_hom
    (restriction_factor_of_moving_endpoints P hP f j β α h₀ h₁) s
  change transfer P ((Cor.graphFunctor k).map f) s =
    transfer P β (transfer P ((Cor.graphFunctor k).map j) s) at h
  simpa only [hs, map_zero] using h

end AlgebraicGeometry.PresheafWithTransfers
