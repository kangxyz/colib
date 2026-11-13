/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalReflector
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Adjunctions on the interval homotopy category

A stalkwise adjunction whose right adjoint preserves interval-local objects
restricts to the chosen interval homotopy category. Its left functor is the
specified descent of the stalkwise left adjoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (I : Cᵒᵖ ⥤ SSet.{w})

local notation "Q" => stalkwiseToIntervalHomotopyCategory C J I

variable (h : ∀ Y : IntervalHomotopyCategory C J I,
  ∃ X : StalkwiseHomotopyCategory.{w} C J,
    IsIntervalLocal C J I X ∧ Nonempty ((stalkwiseToIntervalHomotopyCategory C J I).obj X ≅ Y))

local notation "ι" => intervalLocalInclusion J I h
local notation "ρ" => intervalReflectorAdjunction J I h

variable {F G : StalkwiseHomotopyCategory.{w} C J ⥤ StalkwiseHomotopyCategory.{w} C J}
  (adj : F ⊣ G)
  {F' : IntervalHomotopyCategory C J I ⥤ IntervalHomotopyCategory C J I}
  (comparison : stalkwiseToIntervalHomotopyCategory C J I ⋙ F' ≅
    F ⋙ stalkwiseToIntervalHomotopyCategory C J I)
  (hG : ∀ {X}, IsIntervalLocal C J I X → IsIntervalLocal C J I (G.obj X))

private def descendedLeftComparison : (ι) ⋙ F ⋙ (Q) ≅ F' ⋙ 𝟭 _ :=
  isoWhiskerLeft (ι) comparison.symm ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (asIso (ρ).counit) F' ≪≫ (leftUnitor F') ≪≫ (rightUnitor F').symm

private def descendedRightComparison :
    𝟭 _ ⋙ ((ι) ⋙ G) ≅ (((ι) ⋙ G) ⋙ (Q)) ⋙ (ι) := by
  let η := whiskerLeft ((ι) ⋙ G) (ρ).unit
  have hη : IsIso η := (NatTrans.isIso_iff_isIso_app η).2 fun Y ↦
    isIso_intervalReflectorAdjunction_unit_app J I h (G.obj ((ι).obj Y))
      (hG (isIntervalLocal_intervalLocalInclusion_obj J I h Y))
  exact leftUnitor _ ≪≫ @asIso _ _ _ _ η hη ≪≫ (associator _ _ _).symm

/-- The right adjoint of a descended left functor applies the original right
adjoint to the local model and then takes its interval localization. -/
@[no_expose]
def intervalLocalizedAdjunction : F' ⊣ ((ι) ⋙ G) ⋙ (Q) :=
  (adj.comp (ρ)).restrictFullyFaithful
    (intervalLocalInclusionFullyFaithful J I h) (FullyFaithful.ofFullyFaithful (𝟭 _))
    (descendedLeftComparison J I h comparison) (descendedRightComparison J I h hG)

end CategoryTheory.PointedSimplicialPresheaf
