/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PointMaps

/-! # The actual pointed-puncture zero-section argument on filtered colimits

The punctured projection comparison remains an explicit geometric input.
This file does not establish bounded punctured descent.
-/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Puncture/PointColimit.lean`, blob
`f31367ed49b4f88299b139cbc308984e22512ebe`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (R : CommRingCat.{u}) {X U : SmoothSite (Spec R)} (j : U ⟶ X)
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The actual original restrictions and zero sections commute after the existing point colimit. -/
theorem pointedCylinderRestriction_zeroSection_colimit :
    colim.map (pointedCylinderRestriction R j Φ P) ≫
        colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ)) =
      colim.map (pointedZeroSection R Φ P (pointedBase R Φ)) ≫
        colim.map (pointedRestriction R j Φ P) := by
  rw [← CategoryTheory.Functor.map_comp, pointedCylinderRestriction_zeroSection]
  erw [CategoryTheory.Functor.map_comp]

/-- A punctured projection comparison and vanishing of the base germ force the original
cylinder restriction to vanish. The punctured comparison is not proved here. -/
theorem pointedCylinderRestriction_colimit_eq_zero
    (hbase : IsZero (colimit (pointedBaseValues R Φ P)))
    [IsIso (colim.map (pointedProjection R Φ P (pointedPuncture R j Φ)))] :
    colim.map (pointedCylinderRestriction R j Φ P) = 0 := by
  have hs : colim.map (pointedProjection R Φ P (pointedPuncture R j Φ)) ≫
      colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ)) = 𝟙 _ := by
    rw [← Functor.map_comp, pointedProjection_zeroSection, CategoryTheory.Functor.map_id]
  let zero := colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ))
  let : IsIso zero := by
    change IsIso (colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ)))
    rw [IsIso.eq_inv_of_hom_inv_id hs]
    infer_instance
  apply (Iso.cancel_iso_hom_right _ _ (asIso zero)).mp
  change _ ≫ colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ)) =
    _ ≫ colim.map (pointedZeroSection R Φ P (pointedPuncture R j Φ))
  rw [Limits.zero_comp, pointedCylinderRestriction_zeroSection_colimit]
  rw [hbase.eq_of_tgt (colim.map (pointedZeroSection R Φ P (pointedBase R Φ))) 0,
    Limits.zero_comp]

/-- If the actual puncture restriction is also injective, its original cylinder germ is zero. -/
theorem pointedCylinder_colimit_isZero
    (hbase : IsZero (colimit (pointedBaseValues R Φ P)))
    [IsIso (colim.map (pointedProjection R Φ P (pointedPuncture R j Φ)))]
    [Mono (colim.map (pointedCylinderRestriction R j Φ P))] :
    IsZero (colimit (pointedCylinderValues R Φ P (pointedBase R Φ))) := by
  have h := pointedCylinderRestriction_colimit_eq_zero R j Φ P hbase
  exact (IsZero.iff_id_eq_zero _).mpr ((cancel_mono
    (colim.map (pointedCylinderRestriction R j Φ P))).mp (by
      simpa only [Category.id_comp, Limits.zero_comp] using h))

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
