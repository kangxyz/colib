/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.EnoughProjectives
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Projective transfer presheaves and representable sums

The defining projective presentation uses the direct sum indexed by
the actual sections of a coefficient. For a projective coefficient
its identity lifts through that presentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local instance projectiveRepresentable_hasColimitsOfShapeDiscrete (I : Type (u + 1)) :
    HasColimitsOfShape (Discrete I) (PresheafWithTransfers.{u + 1} k) := by
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u + 1} := AddCommGrpCat.hasColimitsOfShape
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I)
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})

/-- The original projective presentation makes a projective transfer
presheaf a retract of the representables indexed by its sections. -/
@[no_expose]
def retractRepresentableLargeCoproduct (P : PresheafWithTransfers.{u + 1} k) [Projective P] :
    Retract P (∐ fun i : Σ X : Cor k, sections P X => (representableLarge k).obj i.1) := by
  let I : Type (u + 1) := Σ X : Cor k, sections P X
  let R := fun i : I => (representableLarge k).obj i.1
  let π : (∐ R) ⟶ P := Sigma.desc (fun i => sectionHomLarge P i.1 i.2)
  let U : PresheafWithTransfers.{u + 1} k ⥤ (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} := forget
  have hπ (X : Cor k) : Function.Surjective (π.hom.app (op X)) := by
    intro x
    let i : I := ⟨X, x⟩
    let a := (Sigma.ι R i).hom.app (op X) (ULift.up (𝟙 X))
    refine ⟨a, ?_⟩
    have hi : Sigma.ι R i ≫ π = sectionHomLarge P X x := Sigma.ι_comp_desc _ _
    exact (congrArg (fun f : R i ⟶ P => f.hom.app (op X) (ULift.up (𝟙 X))) hi).trans
      ((yonedaLargeAddEquiv P X).apply_symm_apply x)
  have hu : Epi (U.map π) := (NatTrans.epi_iff_epi_app _).2
    (fun X => (AddCommGrpCat.epi_iff_surjective _).2 (hπ X.unop))
  let : Epi π := U.epi_of_epi_map hu
  exact ⟨Projective.factorThru (𝟙 P) π, π, Projective.factorThru_comp _ _⟩

end AlgebraicGeometry.PresheafWithTransfers
