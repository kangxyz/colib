/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic

/-! # Projective lines over open subschemes

The canonical projective line over an open subscheme identifies with the literal
inverse-image open in the ambient projective line. The isomorphism retains both
projection maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (U : X.Opens)

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)

/-- The native base-change isomorphism for the actual inverse-image open. -/
def projectiveLineOpenBaseChangeIso :
    projectiveSpaceOver 1 U.toScheme ≅ (π ⁻¹ᵁ U).toScheme :=
  (isPullback_projectiveSpaceOverMap 1 U.ι).isoPullback ≪≫
    pullbackRestrictIsoRestrict π U

/-- The open-base-change isomorphism retains the actual map into the ambient projective line. -/
@[reassoc]
theorem projectiveLineOpenBaseChangeIso_hom_ι :
    (projectiveLineOpenBaseChangeIso X U).hom ≫ (π ⁻¹ᵁ U).ι =
      projectiveSpaceOverMap 1 U.ι := by
  let e : projectiveSpaceOver 1 U.toScheme ≅ pullback π U.ι :=
    (isPullback_projectiveSpaceOverMap 1 U.ι).isoPullback
  let d := pullbackRestrictIsoRestrict π U
  change (e.hom ≫ d.hom) ≫ (π ⁻¹ᵁ U).ι = _
  rw [Category.assoc]
  calc
    _ = e.hom ≫ pullback.fst π U.ι :=
      congrArg (fun g => e.hom ≫ g) (pullbackRestrictIsoRestrict_hom_ι π U)
    _ = _ := (isPullback_projectiveSpaceOverMap 1 U.ι).isoPullback_hom_fst

/-- The same isomorphism is over the open base, with the native restricted projection. -/
@[reassoc]
theorem projectiveLineOpenBaseChangeIso_hom_morphismRestrict :
    (projectiveLineOpenBaseChangeIso X U).hom ≫ π ∣_ U =
      (projectiveSpaceOver 1 U.toScheme ↘ U.toScheme) := by
  let e : projectiveSpaceOver 1 U.toScheme ≅ pullback π U.ι :=
    (isPullback_projectiveSpaceOverMap 1 U.ι).isoPullback
  let d := pullbackRestrictIsoRestrict π U
  change (e.hom ≫ d.hom) ≫ π ∣_ U = _
  rw [Category.assoc]
  calc
    _ = e.hom ≫ pullback.snd π U.ι :=
      congrArg (fun g => e.hom ≫ g) (pullbackRestrictIsoRestrict_hom_morphismRestrict π U)
    _ = _ := (isPullback_projectiveSpaceOverMap 1 U.ι).isoPullback_hom_snd

end AlgebraicGeometry.Scheme
