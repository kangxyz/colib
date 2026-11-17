/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Comparing biproduct maps by projections -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Category

namespace CategoryTheory.Limits.biprod

/-- A comparison after a functor's biproduct isomorphism is determined by the
two projections of its specified component isomorphisms. -/
theorem comp_mapBiprod_hom_eq_of_projections {C N D E : Type*}
    [Category* C] [Category* N] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms N] [HasZeroMorphisms E]
    [HasBinaryBiproducts C] [HasBinaryBiproducts N] [HasBinaryBiproducts E]
    (q : C ⥤ E) (H : E ⥤ E) (s : N ⥤ D) (r : D ⥤ E)
    [q.PreservesZeroMorphisms] [H.PreservesZeroMorphisms] [(s ⋙ r).PreservesZeroMorphisms]
    [PreservesBinaryBiproducts q] [PreservesBinaryBiproducts H] [PreservesBinaryBiproducts (s ⋙ r)]
    {X₂ X₃ : C} {Q₂ Q₃ : N} {Y₂ Y₃ : E}
    (l₂ : q.obj X₂ ≅ Y₂) (l₃ : q.obj X₃ ≅ Y₃)
    (v₂ : H.obj Y₂ ≅ (s ⋙ r).obj Q₂) (v₃ : H.obj Y₃ ≅ (s ⋙ r).obj Q₃)
    (z : H.obj (q.obj (X₂ ⊞ X₃)) ⟶ (s ⋙ r).obj (Q₂ ⊞ Q₃))
    (h₂ : z ≫ r.map (s.map (biprod.fst : Q₂ ⊞ Q₃ ⟶ Q₂)) =
      H.map (q.map (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ l₂.hom) ≫ v₂.hom)
    (h₃ : z ≫ r.map (s.map (biprod.snd : Q₂ ⊞ Q₃ ⟶ Q₃)) =
      H.map (q.map (biprod.snd : X₂ ⊞ X₃ ⟶ X₃) ≫ l₃.hom) ≫ v₃.hom) :
    z ≫ ((s ⋙ r).mapBiprod Q₂ Q₃).hom =
      H.map (q.mapBiprod X₂ X₃ ≪≫ biprod.mapIso l₂ l₃).hom ≫
        (H.mapBiprod Y₂ Y₃ ≪≫ biprod.mapIso v₂ v₃).hom := by
  let e := q.mapBiprod X₂ X₃
  let L := biprod.mapIso l₂ l₃
  have hL : L.hom = biprod.map l₂.hom l₃.hom := biprod.mapIso_hom l₂ l₃
  have hw : (q.mapBiprod X₂ X₃ ≪≫ biprod.mapIso l₂ l₃).hom =
      (q.mapBiprod X₂ X₃).hom ≫ biprod.map l₂.hom l₃.hom :=
    (Iso.trans_hom e L).trans (congrArg (e.hom ≫ ·) hL)
  let t := H.mapBiprod Y₂ Y₃
  let G := biprod.mapIso v₂ v₃
  have hG : G.hom = biprod.map v₂.hom v₃.hom := biprod.mapIso_hom v₂ v₃
  have hg : (H.mapBiprod Y₂ Y₃ ≪≫ biprod.mapIso v₂ v₃).hom =
      (H.mapBiprod Y₂ Y₃).hom ≫ biprod.map v₂.hom v₃.hom :=
    (Iso.trans_hom t G).trans (congrArg (t.hom ≫ ·) hG)
  have hc₂ := Functor.comp_map s r (biprod.fst : Q₂ ⊞ Q₃ ⟶ Q₂)
  have hc₃ := Functor.comp_map s r (biprod.snd : Q₂ ⊞ Q₃ ⟶ Q₃)
  have h₂' := (congrArg (z ≫ ·) hc₂).trans h₂
  have h₃' := (congrArg (z ≫ ·) hc₃).trans h₃
  rw [hw, hg]
  apply biprod.hom_ext
  · simpa only [Category.assoc, Functor.mapBiprod_hom, biprod.map_fst, biprod.lift_fst_assoc,
      biprod.lift_fst, ← H.map_comp_assoc] using h₂'
  · simpa only [Category.assoc, Functor.mapBiprod_hom, biprod.map_snd, biprod.lift_snd_assoc,
      biprod.lift_snd, ← H.map_comp_assoc] using h₃'

end CategoryTheory.Limits.biprod
