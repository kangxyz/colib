/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Complements

/-!
# Literal flattening of the native honest image

Forgetting the redundant perfect-object wrapper is an equivalence on unchanged actual
complexes and chain maps. Its inclusion is literally the original full inclusion.
The exactness and K-theory applications have their separate K-theory owner.

Adapted from
Quillen `SupportedOpenDerivedImage/Complements.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules]

/-- Forget only the redundant native-supported-perfect wrapper. -/
def flatten : (objects j T).FullSubcategory ⥤ Obj j T where
  obj A := ⟨A.obj.obj, A.property⟩
  map f := (complexObjects j T).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the proved native supported perfectness of the very same original complex. -/
def nest : Obj j T ⥤ (objects j T).FullSubcategory where
  obj A := ⟨⟨A.obj, perfectSupported_of_mem j T A.property⟩, A.property⟩
  map f := (objects j T).homMk (ObjectProperty.homMk f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem flatten_comp_nest : flatten j T ⋙ nest j T = 𝟭 _ := rfl
@[simp] theorem nest_comp_flatten : nest j T ⋙ flatten j T = 𝟭 _ := rfl

/-- Actual equivalence without replacing any original chain object or chain map. -/
def flattenEquivalence : (objects j T).FullSubcategory ≌ Obj j T where
  functor := flatten j T
  inverse := nest j T
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by intros; simp only [Iso.refl_hom]; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by intros; simp only [Iso.refl_hom]; rfl)

/-- Flattening retains the original native supported perfect inclusion literally. -/
@[simp] theorem flatten_comp_inclusion : flatten j T ⋙ inclusion j T = (objects j T).ι := rfl

/-- Nesting retains that same inclusion literally. -/
@[simp] theorem nest_comp_inclusion : nest j T ⋙ (objects j T).ι = inclusion j T := rfl

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/SupportedOpenDerivedImage/\
  Complements.lean:100-130"
  "adaptation" "Literal wrapper equivalence retains native complexes, chain maps and inclusion"]
  AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage.flattenEquivalence
  AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage.flatten_comp_inclusion
