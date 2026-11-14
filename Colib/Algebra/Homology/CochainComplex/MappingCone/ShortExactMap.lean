/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.MappingCone.ShortExactBoundary
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Additive functors preserve the canonical short-exact cone comparison -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.mappingCone
open HomComplex
universe v u v' u'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original rotated comparison commutes with the native functor/cone and shift isos. -/
lemma fromShortComplexShift_map (S : ShortComplex (CochainComplex C ℤ)) :
    (F.mapHomologicalComplex (.up ℤ)).map (fromShortComplexShift S) ≫
      (mapHomologicalComplexIso S.g F).hom =
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app S.X₁ ≫
      fromShortComplexShift (S.map (F.mapHomologicalComplex (.up ℤ))) := by
  ext i
  apply (ext_to_iff _ i (i + 1) rfl _ _).mpr
  constructor
  · simpa [mapHomologicalComplexIso, mapHomologicalComplexXIso,
      mapHomologicalComplexXIso', ← F.map_comp, fromShortComplexShift_fst] using
      (fromShortComplexShift_fst (S.map (F.mapHomologicalComplex (.up ℤ))) i).symm
  · simpa [mapHomologicalComplexIso, mapHomologicalComplexXIso,
      mapHomologicalComplexXIso', ← F.map_comp, fromShortComplexShift_snd] using
      (fromShortComplexShift_snd (S.map (F.mapHomologicalComplex (.up ℤ))) i).symm

/-- Native functor comparison for the shifted cone, retaining both signed shift isos. -/
def mapShiftedConeIso {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).obj (mappingCone (g⟦(-1 : ℤ)⟧')) ≅
      mappingCone (((F.mapHomologicalComplex (.up ℤ)).map g)⟦(-1 : ℤ)⟧') :=
  (F.mapHomologicalComplex (.up ℤ)).mapIso (shiftIso g (-1)).symm ≪≫
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (-1)).app (mappingCone g) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso (mapHomologicalComplexIso g F) ≪≫
    shiftIso ((F.mapHomologicalComplex (.up ℤ)).map g) (-1)

/-- The original signed short-exact comparison is preserved under an additive functor. -/
lemma fromShortComplex_map (S : ShortComplex (CochainComplex C ℤ)) :
    (F.mapHomologicalComplex (.up ℤ)).map (fromShortComplex S) ≫
      (mapShiftedConeIso F S.g).hom =
      fromShortComplex (S.map (F.mapHomologicalComplex (.up ℤ))) := by
  dsimp only [fromShortComplex, mapShiftedConeIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (F.mapHomologicalComplex (.up ℤ)).map_comp_assoc
    (shiftIso S.g (-1)).hom (shiftIso S.g (-1)).inv]
  rw [Iso.hom_inv_id, (F.mapHomologicalComplex (.up ℤ)).map_id]
  simp only [Category.id_comp]
  erw [Functor.commShiftIso_hom_naturality_assoc]
  erw [← Functor.map_comp_assoc, fromShortComplexShift_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.map_shiftFunctorCompIsoId_inv_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
  rfl


variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [HasDerivedCategory C] [HasDerivedCategory D]

/-- Exact functors preserve the actual derived inverse of the canonical signed cone map. -/
lemma shiftedConeIso_map {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    DerivedCategory.Q.map (mapShiftedConeIso F S.g).hom ≫
      (shiftedConeIso (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ)))).hom =
    (F.mapDerivedCategoryFactors.app (mappingCone (S.g⟦(-1 : ℤ)⟧'))).inv ≫
      F.mapDerivedCategory.map (shiftedConeIso hS).hom ≫
      (F.mapDerivedCategoryFactors.app S.X₁).hom := by
  have := quasiIso_fromShortComplex hS
  have := quasiIso_fromShortComplex (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ)))
  apply (cancel_epi (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map (fromShortComplex S)))).mp
  rw [← DerivedCategory.Q.map_comp_assoc, fromShortComplex_map]
  simp only [shiftedConeIso, Iso.symm_hom, asIso_inv]
  rw [IsIso.hom_inv_id]
  erw [F.mapDerivedCategoryFactors.inv.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, IsIso.hom_inv_id]
  rw [F.mapDerivedCategory.map_id, Category.id_comp]
  exact (F.mapDerivedCategoryFactors.app S.X₁).inv_hom_id.symm

end CochainComplex.mappingCone
