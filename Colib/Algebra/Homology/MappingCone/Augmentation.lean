/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.MappingCone.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.Single

/-! # Augmenting a mapped cone in degree zero -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCone

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- The augmentation after a cone comparison restricts to the right endpoint map. -/
theorem coneAugmentation_inr (A : Arrow (CochainComplex C ℤ))
    (B : ShortComplex (CochainComplex D ℤ))
    (d : (F.mapHomologicalComplex (.up ℤ)).mapArrow.obj A ⟶ Arrow.mk B.f) :
    let L := F.mapHomologicalComplex (.up ℤ)
    let P := mappingConeNatTransFunctor (Arrow.leftToRight (C := CochainComplex D ℤ))
    L.map (mappingCone.inr A.hom) ≫ (mappingCone.mapHomologicalComplexIso A.hom F).hom ≫
      P.map d ≫ mappingCone.descShortComplex B = d.right ≫ B.g := by
  intro L P
  have hi : mappingCone.inr (L.map A.hom) ≫ P.map d =
      d.right ≫ mappingCone.inr B.f := by
    change _ ≫ mappingCone.map (L.map A.hom) B.f d.left d.right d.w.symm = _
    simp only [mappingCone.map, mappingCone.inr_desc]
  rw [← Category.assoc (L.map (mappingCone.inr A.hom)), mappingCone.map_inr,
    ← Category.assoc, hi, Category.assoc, mappingCone.inr_descShortComplex]

/-- For a degree-zero target, the right inclusion detects maps from a termwise mapped cone
whose left endpoint vanishes in degree one. -/
theorem hom_ext_mapCone_to_single {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : IsZero (K.X 1)) (B : D)
    {u v : (F.mapHomologicalComplex (.up ℤ)).obj (mappingCone f) ⟶
      (HomologicalComplex.single D (.up ℤ) (0 : ℤ)).obj B}
    (h : (F.mapHomologicalComplex (.up ℤ)).map (mappingCone.inr f) ≫ u =
      (F.mapHomologicalComplex (.up ℤ)).map (mappingCone.inr f) ≫ v) :
    u = v := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    let q := (mappingCone.snd f).v 0 0 (add_zero 0)
    have hz : (mappingCone.fst f).1.v 0 1 rfl = 0 := hK.eq_of_tgt _ _
    have hs : q ≫ (mappingCone.inr f).f 0 = 𝟙 _ := by
      simpa only [hz, zero_comp, zero_add] using mappingCone.id_X f 0 1 rfl
    let i := ((F.mapHomologicalComplex (.up ℤ)).map (mappingCone.inr f)).f 0
    have hi : F.map q ≫ i = 𝟙 _ := by
      change F.map q ≫ F.map ((mappingCone.inr f).f 0) = _
      rw [← F.map_comp, hs, F.map_id]
    have he : i ≫ u.f 0 = i ≫ v.f 0 := congrArg (fun t => t.f 0) h
    calc
      _ = (F.map q ≫ i) ≫ u.f 0 := by rw [hi, Category.id_comp]
      _ = (F.map q ≫ i) ≫ v.f 0 := by simp only [Category.assoc, he]
      _ = _ := by rw [hi, Category.id_comp]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 B n hn).eq_of_tgt _ _

end CochainComplex.mappingCone
