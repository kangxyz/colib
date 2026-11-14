/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GodementRepresentative

/-! # Functoriality of the native Godement representative

The map of Godement double complexes applies the Godement functor at each bidegree.
Its totalization commutes with the canonical augmentation, which is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.GodementResolution
open HomologicalComplex RingedSpaceModuleAdjunction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

universe u

variable {X : Scheme.{u}}

/-- The actual map between the Godement rows, before extension to integer degrees. -/
def godementRowsMap {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    godementRows X.toRingedSpace K ⟶ godementRows X.toRingedSpace L where
  f p :=
    { f q := ((godementComplex X.toRingedSpace).map (f.f q)).f p
      comm' q q' _ := by
        have h := congrArg
          (fun m => ((godementComplex X.toRingedSpace).map m).f p) (f.comm q q')
        change ((godementComplex X.toRingedSpace).map (f.f q)).f p ≫
            ((godementComplex X.toRingedSpace).map (L.d q q')).f p =
          ((godementComplex X.toRingedSpace).map (K.d q q')).f p ≫
            ((godementComplex X.toRingedSpace).map (f.f q')).f p
        simpa only [Functor.map_comp, HomologicalComplex.comp_f] using h }
  comm' p p' _ := by
    apply HomologicalComplex.hom_ext
    intro q
    exact ((godementComplex X.toRingedSpace).map (f.f q)).comm p p'

/-- Godement totalization on the same full subcategory of bounded below perfect complexes. -/
def godementTotal (X : Scheme.{u}) : Obj X ⥤ Obj X where
  obj K := ⟨_, godementTotal_mem K⟩
  map f := ObjectProperty.homMk
    (HomologicalComplex₂.total.map
      (extendMap (godementRowsMap f.hom) ComplexShape.embeddingUpNat) (ComplexShape.up ℤ))
  map_id K := by
    have h : godementRowsMap (𝟙 K.obj) = 𝟙 (godementRows X.toRingedSpace K.obj) := by
      apply HomologicalComplex.hom_ext
      intro p
      apply HomologicalComplex.hom_ext
      intro q
      simp [godementRowsMap]
      rfl
    apply ObjectProperty.hom_ext
    simp [h, HomologicalComplex₂.total.map_id]
  map_comp f g := by
    have h : godementRowsMap (f.hom ≫ g.hom) =
        godementRowsMap f.hom ≫ godementRowsMap g.hom := by
      apply HomologicalComplex.hom_ext
      intro p
      apply HomologicalComplex.hom_ext
      intro q
      simp [godementRowsMap]
    apply ObjectProperty.hom_ext
    simp [h, HomologicalComplex₂.total.map_comp]

private theorem rowZero_naturality {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) (q : ℤ) :
    f.f q ≫ (godementRowZeroAugmentation X.toRingedSpace L).f q =
      (godementRowZeroAugmentation X.toRingedSpace K).f q ≫ ((godementRowsMap f).f 0).f q := by
  have h := congrArg (fun m => m.f 0)
    ((godementAugmentation X.toRingedSpace).naturality (f.f q))
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.single_map_f_self] at h
  dsimp [godementRowZeroAugmentation, godementRowsMap]
  simpa [Category.assoc] using
    congrArg (fun m =>
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.X q)).inv ≫ m) h

/-- The augmentation of the actual Godement resolution. -/
def godementUnit (X : Scheme.{u}) : 𝟭 (Obj X) ⟶ godementTotal X where
  app K := by
    let a := K.property.2.choose
    let : K.obj.IsStrictlyGE a := K.property.2.choose_spec
    exact ObjectProperty.homMk (godementComparisonMap X.toRingedSpace K.obj a)
  naturality {K L} f := by
    let a := K.property.2.choose
    let b := L.property.2.choose
    let : K.obj.IsStrictlyGE a := K.property.2.choose_spec
    let : L.obj.IsStrictlyGE b := L.property.2.choose_spec
    apply ObjectProperty.hom_ext
    change f.hom ≫ godementComparisonMap X.toRingedSpace L.obj b =
      godementComparisonMap X.toRingedSpace K.obj a ≫
        HomologicalComplex₂.total.map
          (extendMap (godementRowsMap f.hom) ComplexShape.embeddingUpNat) (ComplexShape.up ℤ)
    apply HomologicalComplex.hom_ext
    intro q
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, godementComparisonMap_f,
      godementComparisonMap_f, Category.assoc, HomologicalComplex₂.ιTotal_map]
    have h0 : ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) := rfl
    rw [HomologicalComplex.extendMap_f _ _ h0]
    simp only [godementRowAugmentation, HomologicalComplex.comp_f, Category.assoc]
    rw [← Category.assoc (f.hom.f q), rowZero_naturality, Category.assoc]
    let e := (godementRows X.toRingedSpace K.obj).extendXIso ComplexShape.embeddingUpNat h0
    let e' := (godementRows X.toRingedSpace L.obj).extendXIso ComplexShape.embeddingUpNat h0
    let r := (godementRowZeroAugmentation X.toRingedSpace K.obj).f q
    let t := ((godementRowsMap f.hom).f 0).f q
    let j := (godementDoubleComplex X.toRingedSpace L.obj).ιTotal
      (ComplexShape.up ℤ) 0 q q (by simp)
    change r ≫ t ≫ e'.inv.f q ≫ j =
      r ≫ e.inv.f q ≫ e.hom.f q ≫ t ≫ e'.inv.f q ≫ j
    have he := congrArg (fun m => m.f q) e.inv_hom_id
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at he
    rw [← Category.assoc (e.inv.f q), he, Category.id_comp]

/-- The actual augmentation is a quasi-isomorphism on every bounded below perfect complex. -/
theorem godementUnit_quasiIso (K : Obj X) : QuasiIso ((godementUnit X).app K).hom := by
  let a := K.property.2.choose
  let : K.obj.IsStrictlyGE a := K.property.2.choose_spec
  exact AlgebraicGeometry.GodementResolution.quasiIso_godementComparisonMap X.toRingedSpace K.obj a

/-- Native Godement totalization preserves quasi-isomorphisms. -/
theorem godementTotal_map_quasiIso {K L : Obj X} (f : K ⟶ L) (hf : QuasiIso f.hom) :
    QuasiIso ((godementTotal X).map f).hom := by
  let := hf
  let := godementUnit_quasiIso K
  let := godementUnit_quasiIso L
  have h := congrArg (fun m => m.hom) ((godementUnit X).naturality f)
  change f.hom ≫ ((godementUnit X).app L).hom =
    ((godementUnit X).app K).hom ≫ ((godementTotal X).map f).hom at h
  apply (quasiIso_iff_comp_left ((godementUnit X).app K).hom _).1
  rw [← h]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect
