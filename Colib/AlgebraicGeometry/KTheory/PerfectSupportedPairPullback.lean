/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenPullback
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.QuasiCompact

/-!
# Original geometric perfect K-pullback

Selected literal inclusion transports of the original geometric bounded-flat pullback.
Only the declarations below are included; no new K-zero model or localization result is defined.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

variable {A B C : Scheme.QuasiCompactOpenPairs.{u}}

/-- Original supported K-pullback through the literal bounded-flat inclusion. -/
@[colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/PairPullback.lean:34"
  "adaptation" "Original geometric pullback through the literal inclusion comparison."]
def perfectSupportedKPullback (f : A ⟶ B) (n : ℕ) :
    PerfectSupportedK B.obj.hom n →* PerfectSupportedK A.obj.hom n :=
  (boundedAboveFlatPerfectSupportedKEquiv A.obj.hom n).toMonoidHom.comp
    ((boundedAboveFlatPerfectSupportedKPullback f.hom n).comp
      (boundedAboveFlatPerfectSupportedKEquiv
      B.obj.hom n).symm.toMonoidHom)

/-- The supported pullback retains the original bounded-flat comparison square. -/
@[colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/PairPullback.lean:40"
  "adaptation" "Original geometric pullback through the literal inclusion comparison."]
theorem perfectSupportedKPullback_comp_boundedFlat (f : A ⟶ B) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (boundedAboveFlatPerfectSupportedToPerfectKMap
      B.obj.hom n) =
      (boundedAboveFlatPerfectSupportedToPerfectKMap A.obj.hom n).comp
        (boundedAboveFlatPerfectSupportedKPullback f.hom n) := by
  ext x
  change boundedAboveFlatPerfectSupportedKEquiv A.obj.hom n
    (boundedAboveFlatPerfectSupportedKPullback f.hom n ((boundedAboveFlatPerfectSupportedKEquiv
      B.obj.hom
      n).symm
      (boundedAboveFlatPerfectSupportedKEquiv B.obj.hom n x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The literal inclusion comparison determines the supported pullback uniquely. -/
@[colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/PairPullback.lean:53"
  "adaptation" "Original geometric pullback through the literal inclusion comparison."]
theorem perfectSupportedKPullback_unique (f : A ⟶ B) (n : ℕ)
    (k : PerfectSupportedK B.obj.hom n →* PerfectSupportedK A.obj.hom n)
    (hk : k.comp (boundedAboveFlatPerfectSupportedToPerfectKMap B.obj.hom n) =
      (boundedAboveFlatPerfectSupportedToPerfectKMap A.obj.hom n).comp
        (boundedAboveFlatPerfectSupportedKPullback f.hom n)) :
    k = perfectSupportedKPullback f n := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedAboveFlatPerfectSupportedToPerfectKMap_bijective B.obj.hom
    n).surjective x
  exact DFunLike.congr_fun (hk.trans (perfectSupportedKPullback_comp_boundedFlat f n).symm) y

/-- The original supported pullback preserves identity maps. -/
@[simp, colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/PairPullback.lean:64"
  "adaptation" "Original geometric pullback through the literal inclusion comparison."]
theorem perfectSupportedKPullback_id (A :
  AlgebraicGeometry.Scheme.QuasiCompactOpenPairs.{u}) (n : ℕ)
  :
    perfectSupportedKPullback (𝟙 A) n = MonoidHom.id _ := by
  symm
  apply perfectSupportedKPullback_unique
  change (MonoidHom.id _).comp (boundedAboveFlatPerfectSupportedToPerfectKMap A.obj.hom n) =
    (boundedAboveFlatPerfectSupportedToPerfectKMap A.obj.hom n).comp
      (boundedAboveFlatPerfectSupportedKPullback (𝟙 A.obj) n)
  simp only [boundedAboveFlatPerfectSupportedKPullback_id, MonoidHom.id_comp, MonoidHom.comp_id]

/-- The original supported pullback has contravariant composition order. -/
@[simp, colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/PairPullback.lean:75"
  "adaptation" "Original geometric pullback through the literal inclusion comparison."]
theorem perfectSupportedKPullback_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    perfectSupportedKPullback (f ≫ g) n = (perfectSupportedKPullback f n).comp
      (perfectSupportedKPullback g n) := by
  symm
  apply perfectSupportedKPullback_unique
  rw [MonoidHom.comp_assoc, perfectSupportedKPullback_comp_boundedFlat,
    ← MonoidHom.comp_assoc, perfectSupportedKPullback_comp_boundedFlat, MonoidHom.comp_assoc]
  change _ = (boundedAboveFlatPerfectSupportedToPerfectKMap A.obj.hom n).comp
    (boundedAboveFlatPerfectSupportedKPullback (f.hom ≫ g.hom) n)
  rw [boundedAboveFlatPerfectSupportedKPullback_comp]

end AlgebraicGeometry.Scheme.Modules
