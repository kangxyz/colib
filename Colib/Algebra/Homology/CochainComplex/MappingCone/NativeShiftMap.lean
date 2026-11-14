/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.MappingCone.ShortExactMap

/-! # Native cone and shift comparisons commute -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.mappingCone
open HomComplex
universe v u v' u'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The native functor/cone iso preserves the first projection. -/
@[reassoc]
lemma mapHomologicalComplexIso_hom_fst {K L : CochainComplex C ℤ}
    (g : K ⟶ L) (i j : ℤ) (h : i + 1 = j) :
    (mapHomologicalComplexIso g F).hom.f i ≫
      (fst ((F.mapHomologicalComplex (.up ℤ)).map g)).1.v i j h =
      F.map ((fst g).1.v i j h) := by
  subst j
  simp [mapHomologicalComplexIso, mapHomologicalComplexXIso,
    mapHomologicalComplexXIso']

/-- The native functor/cone iso preserves the second projection. -/
@[reassoc]
lemma mapHomologicalComplexIso_hom_snd {K L : CochainComplex C ℤ}
    (g : K ⟶ L) (i : ℤ) :
    (mapHomologicalComplexIso g F).hom.f i ≫
      (snd ((F.mapHomologicalComplex (.up ℤ)).map g)).v i i (add_zero i) =
      F.map ((snd g).v i i (add_zero i)) := by
  simp [mapHomologicalComplexIso, mapHomologicalComplexXIso,
    mapHomologicalComplexXIso']

/-- The signed shift transport equals the original functor/cone map followed by shift naturality. -/
lemma mapShiftedConeIso_hom {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    (mapShiftedConeIso F g).hom =
    (mapHomologicalComplexIso (g⟦(-1 : ℤ)⟧') F).hom ≫
      map ((F.mapHomologicalComplex (.up ℤ)).map (g⟦(-1 : ℤ)⟧'))
        (((F.mapHomologicalComplex (.up ℤ)).map g)⟦(-1 : ℤ)⟧')
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (-1)).hom.app K)
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (-1)).hom.app L)
        ((F.mapHomologicalComplex (.up ℤ)).commShiftIso_hom_naturality g (-1)) := by
  apply (cancel_epi ((F.mapHomologicalComplex (.up ℤ)).map (shiftIso g (-1)).hom)).mp
  dsimp only [mapShiftedConeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← (F.mapHomologicalComplex (.up ℤ)).map_comp_assoc,
    Iso.hom_inv_id, (F.mapHomologicalComplex (.up ℤ)).map_id, Category.id_comp]
  ext i
  apply (ext_to_iff _ i (i + 1) rfl _ _).mpr
  constructor
  · simp [shiftIso, map_f_fst, Cochain.shift_v',
      mapHomologicalComplexIso_hom_fst, ← F.map_comp]
  · simp [shiftIso, map_f_snd, Cochain.shift_v',
      mapHomologicalComplexIso_hom_snd, ← F.map_comp]

end CochainComplex.mappingCone
