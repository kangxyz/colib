/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.BaseOpenCover

/-! # Naturality of the projective line over the intersection -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) (T : X.Opens)

local notation "P" Z => projectiveSpaceOver 1 Z
local notation "π" Z => (projectiveSpaceOver 1 Z ↘ Z)
local notation "J" => projectiveSpaceOverMap 1 j

/-- The literal restriction along the intersection agrees with projective base change,
after identifying the intersection in the two ways. -/
theorem projectiveLineBaseOpenOverlap_square :
    let A := (π X) ⁻¹ᵁ T
    let U := j ⁻¹ᵁ T
    let B := J ⁻¹ᵁ A
    let E := (π V) ⁻¹ᵁ U
    let e : E = B := (projectiveLine_preimage_preimage j T).symm
    (projectiveLineOpenBaseChangeIso V U).hom ≫
        (eqToHom (congrArg Scheme.Opens.toScheme e)) ≫
        (projectiveSpaceOverMap 1 j).resLE A B le_rfl =
      projectiveSpaceOverMap 1 (j.resLE T U le_rfl) ≫
        (projectiveLineOpenBaseChangeIso X T).hom := by
  dsimp only
  apply (cancel_mono (((π X) ⁻¹ᵁ T).ι)).1
  have hEq {A B : (P V).Opens} (h : A = B) :
      eqToHom (congrArg Scheme.Opens.toScheme h) ≫ B.ι ≫ J = A.ι ≫ J := by
    subst B
    simp
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
    projectiveLineOpenBaseChangeIso_hom_ι]
  rw [hEq (projectiveLine_preimage_preimage j T).symm]
  rw [projectiveLineOpenBaseChangeIso_hom_ι_assoc,
    projectiveSpaceOverMap_comp, projectiveSpaceOverMap_comp,
    Scheme.Hom.resLE_comp_ι]

end AlgebraicGeometry.Scheme
