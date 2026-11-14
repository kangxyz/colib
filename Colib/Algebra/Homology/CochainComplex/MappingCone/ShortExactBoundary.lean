/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.MappingCone.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# The original extension boundary under the canonical cone comparison
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex.mappingCone

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The actual rotated cone comparison carries the original SES boundary to cone inclusion. -/
lemma triangleOfSESδ_fromShortComplexShift {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) :
    DerivedCategory.triangleOfSESδ hS ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app S.X₁ ≫
        DerivedCategory.Q.map (fromShortComplexShift S) =
      DerivedCategory.Q.map (inr S.g) := by
  have := quasiIso_descShortComplex hS
  apply (cancel_epi (DerivedCategory.Q.map (descShortComplex S))).mp
  simp only [DerivedCategory.descShortComplex_triangleOfSESδ_assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← DerivedCategory.Q.map_comp]
  have h := DerivedCategory.Q_map_eq_of_homotopy C
    ((rotateHomotopyEquivComm₂Homotopy S.f).compRight (shortComplexConeMap S))
  rw [Category.assoc] at h
  change DerivedCategory.Q.map ((triangle S.f).mor₃ ≫ fromShortComplexShift S) = _ at h
  rw [h]
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  exact (triangleMap (inr S.f) S.g (𝟙 S.X₂) (descShortComplex S) (by simp)).comm₂

/-- The canonical unshifted cone comparison of an actual short exact sequence. -/
def shortComplexShiftIso {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) :
    DerivedCategory.Q.obj (S.X₁⟦(1 : ℤ)⟧) ≅ DerivedCategory.Q.obj (mappingCone S.g) := by
  have := quasiIso_fromShortComplexShift hS
  exact asIso (DerivedCategory.Q.map (fromShortComplexShift S))

/-- Cone inclusion followed by the canonical inverse is precisely the original SES boundary. -/
lemma triangleOfSESδ_eq_coneInclusion {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) :
    DerivedCategory.triangleOfSESδ hS =
      DerivedCategory.Q.map (inr S.g) ≫ (shortComplexShiftIso hS).inv ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  have := quasiIso_fromShortComplexShift hS
  rw [← triangleOfSESδ_fromShortComplexShift hS]
  simp [shortComplexShiftIso, Category.assoc]

/-- The actual extension class is cone inclusion followed by this same canonical inverse. -/
lemma extClass_hom_eq_coneInclusion [HasExt C] {S : ShortComplex C}
    (hS : S.ShortExact) :
    hS.extClass.hom =
      DerivedCategory.Q.map (inr (S.map (HomologicalComplex.single C (.up ℤ) 0)).g) ≫
        (shortComplexShiftIso (hS.map_of_exact
          (HomologicalComplex.single C (.up ℤ) 0))).inv ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((HomologicalComplex.single C (.up ℤ) 0).obj S.X₁) := by
  rw [hS.extClass_hom]
  exact triangleOfSESδ_eq_coneInclusion _

omit [HasDerivedCategory C] in
/-- Shifting a cone inclusion uses the actual signed cone-shift isomorphism. -/
lemma inr_shiftIso_hom {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (inr f)⟦n⟧' ≫ (shiftIso f n).hom = inr (f⟦n⟧') := by
  apply (cancel_mono (shiftIso f n).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp [shiftIso]

/-- The shifted canonical cone inverse retains the original SES boundary and its sign. -/
lemma inr_shiftedConeIso {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    DerivedCategory.Q.map (inr (S.g⟦(-1 : ℤ)⟧')) ≫ (shiftedConeIso hS).hom =
      (DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app S.X₃ ≫
        (DerivedCategory.triangleOfSESδ hS)⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (DerivedCategory C) (1 : ℤ) (-1) (by simp)).hom.app
          (DerivedCategory.Q.obj S.X₁) := by
  have := quasiIso_fromShortComplex hS
  apply (cancel_mono (DerivedCategory.Q.map (fromShortComplex S))).mp
  simp only [shiftedConeIso, Iso.symm_hom, asIso_inv, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]
  simp only [fromShortComplex, Functor.map_comp,
    Functor.map_shiftFunctorCompIsoId_inv_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← Functor.commShiftIso_inv_naturality_assoc]
  rw [← Functor.map_comp_assoc]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc, triangleOfSESδ_fromShortComplexShift hS]
  rw [← Functor.commShiftIso_hom_naturality_assoc,
    Iso.hom_inv_id_app_assoc, ← DerivedCategory.Q.map_comp,
    inr_shiftIso_hom]

end CochainComplex.mappingCone
