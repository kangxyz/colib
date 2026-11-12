/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Finiteness after an actual open-chart base change

This is the finite morphism leaf from OriginalEtaleMap at motivic revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`. It does not depend on retained
compactifications, normalizations or presentation data.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme
/-- Finiteness over the original good chart survives the actual Cartesian target change. -/
theorem finite_pullback_on_original_chart {X Y X' : Scheme.{u}}
    (p : Y ⟶ X) (a : X' ⟶ X) (U : X.Opens) [IsFinite (p ∣_ U)] :
    IsFinite ((pullback.snd p a) ∣_ a ⁻¹ᵁ U) := by
  let H := IsPullback.of_hasPullback p a
  have hUY : (pullback.snd p a) ⁻¹ᵁ (a ⁻¹ᵁ U) =
      (pullback.fst p a) ⁻¹ᵁ (p ⁻¹ᵁ U) ⊓
        (pullback.snd p a) ⁻¹ᵁ (a ⁻¹ᵁ U) := by
    simp only [← Scheme.Hom.comp_preimage, H.w, inf_idem]
  have H' := Scheme.Hom.isPullback_resLE H (US := U) (UT := a ⁻¹ᵁ U)
    (UX := p ⁻¹ᵁ U) le_rfl le_rfl hUY
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at H'
  exact MorphismProperty.of_isPullback H' (inferInstance : IsFinite (p ∣_ U))

end AlgebraicGeometry.Scheme
