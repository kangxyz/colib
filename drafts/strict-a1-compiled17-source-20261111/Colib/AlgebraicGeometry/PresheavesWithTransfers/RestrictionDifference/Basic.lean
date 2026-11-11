/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.HomotopyActions

/-! # Signed lifts of restrictions of original sections -/

/-!
Adapted from `Motivic/Cohomology/A1/LocalVanishing/RelativeCurve/LocalLifting.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `014bf5e8babecf146b479bbf0f1ebb51ad2fb7ec`. Original signs, coefficient actions and full
markings are retained. Geometric pencil production is not asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
open Scheme

/-- Literal lifting of restrictions of original sections, not all new sections. -/
def HasRestrictionDifferenceLifting {k : Type u} [Field k]
    (P : PresheafWithTransfers.{u + 1} k)
    {X Y T V : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) (β : X ⟶ V) (α : X ⟶ T) : Prop :=
  ∀ d : sections P (Cor.mk Y), ∃ a : sections P (Cor.mk V), ∃ c : sections P (Cor.mk T),
    ((toPresheaf k).obj P).map β.op a - ((toPresheaf k).obj P).map α.op c =
      ((toPresheaf k).obj P).map φ.op d


/-- The actual signed cylinder endpoints produce the original lifting relation.
This lemma consumes a geometric homotopy, not a cohomological conclusion. -/
theorem hasRestrictionDifferenceLifting_of_homotopy {k : Type u} [Field k]
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {X Y T V : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) (β : X ⟶ V) (α : X ⟶ T)
    (lam : Cor.mk T ⟶ Cor.mk Y) (psi : Cor.mk V ⟶ Cor.mk Y)
    (δ : Cor.mk (SmoothSite.Contraction.affineLineCylinder.obj X) ⟶ Cor.mk Y)
    (h₀ : (Cor.graphFunctor k).map
      (SmoothSite.Contraction.nativeAffineSection (.of k) X 0) ≫ δ =
        (Cor.graphFunctor k).map φ)
    (h₁ : (Cor.graphFunctor k).map
      (SmoothSite.Contraction.nativeAffineSection (.of k) X 1) ≫ δ =
        (Cor.graphFunctor k).map α ≫ lam - (Cor.graphFunctor k).map β ≫ psi) :
    HasRestrictionDifferenceLifting P φ β α := by
  intro d
  exact ⟨-transfer P psi d, -transfer P lam d,
    restriction_difference_eq_restriction_of_homotopy P hP φ β α lam psi δ h₀ h₁ d⟩

end AlgebraicGeometry.PresheafWithTransfers
