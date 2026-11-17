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

/-- Paste two functorial projection squares with a natural transformation before
comparing the biproducts by their component isomorphisms. -/
theorem comp_mapBiprod_hom_eq_of_map_projections {C N D E : Type*}
    [Category* C] [Category* N] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms N] [HasZeroMorphisms E]
    [HasBinaryBiproducts C] [HasBinaryBiproducts N] [HasBinaryBiproducts E]
    (q : C ⥤ E) (H : E ⥤ E) (F : C ⥤ D) (s : N ⥤ D) (r : D ⥤ E)
    [q.PreservesZeroMorphisms] [H.PreservesZeroMorphisms] [(s ⋙ r).PreservesZeroMorphisms]
    [PreservesBinaryBiproducts q] [PreservesBinaryBiproducts H] [PreservesBinaryBiproducts (s ⋙ r)]
    (a : q ⋙ H ⟶ F ⋙ r)
    {X₂ X₃ : C} {Q₂ Q₃ : N} {Y₂ Y₃ : E}
    (l₂ : q.obj X₂ ≅ Y₂) (l₃ : q.obj X₃ ≅ Y₃)
    (v₂ : H.obj Y₂ ≅ (s ⋙ r).obj Q₂) (v₃ : H.obj Y₃ ≅ (s ⋙ r).obj Q₃)
    (m : F.obj (X₂ ⊞ X₃) ⟶ s.obj (Q₂ ⊞ Q₃))
    (d₂ : F.obj X₂ ⟶ s.obj Q₂) (d₃ : F.obj X₃ ⟶ s.obj Q₃)
    (hm₂ : m ≫ s.map (biprod.fst : Q₂ ⊞ Q₃ ⟶ Q₂) =
      F.map (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ d₂)
    (hm₃ : m ≫ s.map (biprod.snd : Q₂ ⊞ Q₃ ⟶ Q₃) =
      F.map (biprod.snd : X₂ ⊞ X₃ ⟶ X₃) ≫ d₃)
    (hd₂ : a.app X₂ ≫ r.map d₂ = H.map l₂.hom ≫ v₂.hom)
    (hd₃ : a.app X₃ ≫ r.map d₃ = H.map l₃.hom ≫ v₃.hom) :
    let z := a.app (X₂ ⊞ X₃) ≫ r.map m
    z ≫ ((s ⋙ r).mapBiprod Q₂ Q₃).hom =
      H.map (q.mapBiprod X₂ X₃ ≪≫ biprod.mapIso l₂ l₃).hom ≫
        (H.mapBiprod Y₂ Y₃ ≪≫ biprod.mapIso v₂ v₃).hom := by
  intro z
  have hp {X : C} {Q : N} {Y : E} (f : X₂ ⊞ X₃ ⟶ X) (g : Q₂ ⊞ Q₃ ⟶ Q)
      (d : F.obj X ⟶ s.obj Q) (l : q.obj X ⟶ Y) (v : H.obj Y ⟶ r.obj (s.obj Q))
      (hm : m ≫ s.map g = F.map f ≫ d) (hd : a.app X ≫ r.map d = H.map l ≫ v) :
      z ≫ r.map (s.map g) = H.map (q.map f ≫ l) ≫ v := by
    let b := a.app (X₂ ⊞ X₃)
    let t := H.map (q.map f)
    have hn : t ≫ a.app X = b ≫ r.map (F.map f) := a.naturality f
    calc
      z ≫ r.map (s.map g) = b ≫ r.map (m ≫ s.map g) :=
        (Category.assoc b _ _).trans (congrArg (b ≫ ·) (r.map_comp m (s.map g)).symm)
      _ = b ≫ r.map (F.map f ≫ d) := congrArg (fun x => b ≫ r.map x) hm
      _ = b ≫ r.map (F.map f) ≫ r.map d := congrArg (b ≫ ·) (r.map_comp (F.map f) d)
      _ = t ≫ a.app X ≫ r.map d :=
        (Category.assoc b _ _).symm.trans
          ((congrArg (· ≫ r.map d) hn.symm).trans (Category.assoc t _ _))
      _ = t ≫ H.map l ≫ v := congrArg (t ≫ ·) hd
      _ = H.map (q.map f ≫ l) ≫ v := (H.map_comp_assoc _ _ _).symm
  exact comp_mapBiprod_hom_eq_of_projections q H s r l₂ l₃ v₂ v₃ z
    (hp (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) (biprod.fst : Q₂ ⊞ Q₃ ⟶ Q₂) d₂ l₂.hom v₂.hom hm₂ hd₂)
    (hp (biprod.snd : X₂ ⊞ X₃ ⟶ X₃) (biprod.snd : Q₂ ⊞ Q₃ ⟶ Q₃) d₃ l₃.hom v₃.hom hm₃ hd₃)

end CategoryTheory.Limits.biprod
