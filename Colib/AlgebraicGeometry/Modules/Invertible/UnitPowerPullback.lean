/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.PullbackPowerComparison

/-!
# Pullback preserves the canonical powers of the structure sheaf

The structure-sheaf pullback isomorphism, the original pullback-power comparison and the
canonical trivialization of a power of the structure sheaf commute. This is an equality of
actual isomorphisms, used to retain the original unit normalization in boundary-root descent.

The native strict-monoidal right unitor is first compared with the original explicit
sheafification right unitor. Its native pullback coherence then supplies the unit-multiplication
square. Tensor naturality and the original successor definitions prove the power comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules
attribute [local implicit_reducible] TopCat.Sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.unitModule
private theorem replace_unit_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {P Q : D} {a a' : A ⟶ B} {t : F.obj A ⟶ P} {k k' : P ⟶ Q}
    {r r' : Q ⟶ F.obj B} (ha : a = a') (hk : k = k') (hr : r = r')
    (h : F.map a = t ≫ k ≫ r) : F.map a' = t ≫ k' ≫ r' := by
  simpa only [← ha, ← hk, ← hr] using h

/-- The native tensor-pullback comparison preserves the original explicit right unitor. -/
theorem pullbackTensorProductRightUnitor_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Y.Modules) :
    (pullback f).map (tensorProductRightUnitor Y.presheaf Y.ringCatIsSheaf A).hom =
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A
        (SheafOfModules.unit Y.ringCatSheaf)).hom ≫
        ((tensorBifunctor X).obj ((pullback f).obj A)).map (pullbackUnitIso f).hom ≫
          (tensorProductRightUnitor X.presheaf X.ringCatIsSheaf ((pullback f).obj A)).hom := by
  have h := Stacks.PullbackTensorCoherence.pullbackTensorComparison_rightUnitor
    f.toLRSHom.toShHom A
  have hy := Stacks.SheafOfModules.Strict_rightUnitor_eq Y.presheaf Y.ringCatIsSheaf A
  have hx := Stacks.SheafOfModules.Strict_rightUnitor_eq X.presheaf X.ringCatIsSheaf
    ((pullback f).obj A)
  have hk := Stacks.SheafOfModules.whiskerLeft_eq_sheafify_map X.presheaf X.ringCatIsSheaf
    ((pullback f).obj A) (pullbackUnitIso f).hom
  exact replace_unit_eq (pullback f) (congrArg Iso.hom hy) hk (congrArg Iso.hom hx) h
private theorem unit_mul_aux {D : Type*} [Category D] [MonoidalCategory D]
    {A P : D} (t : P ⟶ A ⊗ A) (u : A ⟶ 𝟙_ D) (r : P ⟶ A)
    (h : r = t ≫ (A ◁ u) ≫ (ρ_ A).hom) :
    t ≫ (u ⊗ₘ u) ≫ (ρ_ (𝟙_ D)).hom = r ≫ u := by
  rw [h, tensorHom_def', Category.assoc, Category.assoc,
    MonoidalCategory.rightUnitor_naturality]
  simp only [Category.assoc]

private theorem replace_mul_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {P Q R : D} {t : F.obj A ⟶ P} {b b' : P ⟶ Q} {c c' : Q ⟶ R}
    {r r' : A ⟶ B} {u : F.obj B ⟶ R} (hb : b = b') (hc : c = c') (hr : r = r')
    (h : t ≫ b ≫ c = F.map r ≫ u) : t ≫ b' ≫ c' = F.map r' ≫ u := by
  simpa only [← hb, ← hc, ← hr] using h

/-- Pullback preserves multiplication on the structure sheaf through its original
unit comparison. -/
theorem pullbackUnitIso_tensorProductRightUnitor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) ≪≫
      tensorProductIso X.presheaf X.ringCatIsSheaf (pullbackUnitIso f) (pullbackUnitIso f) ≪≫
        tensorProductRightUnitor X.presheaf X.ringCatIsSheaf (SheafOfModules.unit X.ringCatSheaf) =
    (pullback f).mapIso (tensorProductRightUnitor Y.presheaf Y.ringCatIsSheaf
      (SheafOfModules.unit Y.ringCatSheaf)) ≪≫ pullbackUnitIso f := by
  let : MonoidalCategory X.Modules :=
    Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace
  have h := Stacks.PullbackTensorCoherence.pullbackTensorComparison_rightUnitor
    f.toLRSHom.toShHom (SheafOfModules.unit Y.ringCatSheaf)
  have hm := unit_mul_aux _ (pullbackUnitIso f).hom _ h
  have ht := Stacks.SheafOfModules.tensorSheafMapIso_hom_eq X.presheaf X.ringCatIsSheaf
    (pullbackUnitIso f) (pullbackUnitIso f)
  have hx := Stacks.SheafOfModules.Strict_rightUnitor_eq X.presheaf X.ringCatIsSheaf
    (SheafOfModules.unit X.ringCatSheaf)
  have hy := Stacks.SheafOfModules.Strict_rightUnitor_eq Y.presheaf Y.ringCatIsSheaf
    (SheafOfModules.unit Y.ringCatSheaf)
  exact Iso.ext (replace_mul_eq (pullback f) ht.symm
    (congrArg Iso.hom hx) (congrArg Iso.hom hy) hm)

private theorem tensor_iso_trans {D : Type*} [Category D] (T : D × D ⥤ D)
    {A B C P Q R : D} (a : A ≅ B) (b : B ≅ C) (p : P ≅ Q) (q : Q ≅ R) :
    T.mapIso (Iso.prod a p) ≪≫ T.mapIso (Iso.prod b q) =
      T.mapIso (Iso.prod (a ≪≫ b) (p ≪≫ q)) :=
  Iso.ext (T.map_comp (Iso.prod a p).hom (Iso.prod b q).hom).symm

private theorem power_unit_step {D : Type*} [Category D] (T : D × D ⥤ D)
    {Z W P P' Q U V PN QN : D} (a : Z ≅ W) (t : W ≅ T.obj (P, U))
    (p : P ≅ P')
    (sp : T.obj (P', U) ≅ PN) (e : P' ≅ Q) (u : U ≅ V)
    (sq : T.obj (Q, V) ≅ QN) (q : Q ≅ V) (r : T.obj (V, V) ≅ V) :
    (a ≪≫ t ≪≫ T.mapIso (Iso.prod p (Iso.refl U)) ≪≫ sp) ≪≫
        (sp.symm ≪≫ T.mapIso (Iso.prod e u) ≪≫ sq) ≪≫
        (sq.symm ≪≫ T.mapIso (Iso.prod q (Iso.refl V)) ≪≫ r) =
      a ≪≫ t ≪≫ T.mapIso (Iso.prod (p ≪≫ e ≪≫ q) u) ≪≫ r := by
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [← Iso.trans_assoc (T.mapIso _), tensor_iso_trans]
  rw [← Iso.trans_assoc (T.mapIso _), tensor_iso_trans]
  simp only [Iso.refl_trans, Iso.trans_refl, Iso.trans_assoc]

private theorem replace_natural_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {P Q : D} {a a' : A ⟶ B} {t : F.obj B ⟶ Q} {s : F.obj A ⟶ P}
    {b b' : P ⟶ Q} (ha : a = a') (hb : b = b') (h : F.map a ≫ t = s ≫ b) :
    F.map a' ≫ t = s ≫ b' := by
  simpa only [← ha, ← hb] using h

/-- The tensor-pullback comparison is natural for the original tensor-product isomorphisms. -/
theorem pullbackTensorIso_tensorProductIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B C D : Y.Modules} (e : A ≅ B) (g : C ≅ D) :
    (pullback f).mapIso (tensorProductIso Y.presheaf Y.ringCatIsSheaf e g) ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f B D =
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A C ≪≫
        tensorProductIso X.presheaf X.ringCatIsSheaf
          ((pullback f).mapIso e) ((pullback f).mapIso g) := by
  have hy := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
      (forget₂ CommRingCat RingCat) Y.ringCatIsSheaf⟩ e.hom g.hom
  have hx := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
      (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩
        ((pullback f).mapIso e).hom ((pullback f).mapIso g).hom
  exact Iso.ext (replace_natural_eq (pullback f) hy hx
    ((Stacks.RingedSpace.comparisonNatTrans f.toLRSHom.toShHom).naturality (Iso.prod e g).hom))

private theorem power_unit_core {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : D × D ⥤ D) {P U W WU : C} {V : D}
    (q : P ≅ U) (u : F.obj U ≅ V) (tP : F.obj W ≅ T.obj (F.obj P, F.obj U))
    (tU : F.obj WU ≅ T.obj (F.obj U, F.obj U)) (y : W ≅ WU) (rY : WU ≅ U)
    (r : T.obj (V, V) ≅ V) (z : F.obj P ≅ V)
    (hnat : F.mapIso y ≪≫ tU = tP ≪≫ T.mapIso (Iso.prod (F.mapIso q) (Iso.refl _)))
    (hunit : tU ≪≫ T.mapIso (Iso.prod u u) ≪≫ r = F.mapIso rY ≪≫ u)
    (hz : z = F.mapIso q ≪≫ u) :
    tP ≪≫ T.mapIso (Iso.prod z u) ≪≫ r = F.mapIso (y ≪≫ rY) ≪≫ u := by
  rw [hz]
  have ht := tensor_iso_trans T (F.mapIso q) u (Iso.refl (F.obj U)) u
  simp only [Iso.refl_trans] at ht
  rw [← ht]
  simp only [← Iso.trans_assoc] at hnat ⊢
  rw [← hnat]
  simp only [Iso.trans_assoc]
  rw [hunit, F.mapIso_trans]
  simp only [Iso.trans_assoc]

local instance (X : Scheme.{u}) :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.isInvertible_unit _ _

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf ((pullback f).obj M) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj f.toLRSHom.toShHom M

local instance (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X) M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((pullback f).obj Y.unitModule) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj f.toLRSHom.toShHom
      (SheafOfModules.unit Y.ringCatSheaf))

private theorem unit_power_succ (X : Scheme.{u}) (n : ℕ) :
    structureSheafTensorPowerIso X (n + 1) =
      (tensorPowerSuccIso X.presheaf X.ringCatIsSheaf
        (SheafOfModules.unit X.ringCatSheaf) (n : ℤ)).symm ≪≫
        tensorProductIso X.presheaf X.ringCatIsSheaf (structureSheafTensorPowerIso X n)
          (Iso.refl (SheafOfModules.unit X.ringCatSheaf)) ≪≫
        tensorProductRightUnitor X.presheaf X.ringCatIsSheaf
          (SheafOfModules.unit X.ringCatSheaf) := by
  exact Iso.refl_trans _

private theorem map_iso_left {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' : C} {E : D} (a : A ≅ B) (b : B ≅ C') (u : F.obj C' ≅ E) :
    F.mapIso a ≪≫ F.mapIso b ≪≫ u = F.mapIso (a ≪≫ b) ≪≫ u := by
  rw [F.mapIso_trans, Iso.trans_assoc]

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X) X.unitModule :=
  AlgebraicGeometry.isInvertible_unit X

private theorem unit_power_zero {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U : C} {V : D} (u : F.obj U ≅ V) :
    u ≪≫ Iso.refl V ≪≫ Iso.refl V = F.mapIso (Iso.refl U) ≪≫ u := by
  simp

/-- The Kummer tensor-power map of the original unit comparison preserves the canonical
unit powers. -/
theorem pullbackTensorPowerIso_tensorPowerMap_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorPowerIso f (SheafOfModules.unit Y.ringCatSheaf) n ≪≫
      tensorPowerMap X (pullbackUnitIso f) n ≪≫ structureSheafTensorPowerIso X n =
    (pullback f).mapIso (structureSheafTensorPowerIso Y n) ≪≫ pullbackUnitIso f := by
  induction n with
  | zero => exact unit_power_zero (pullback f) (pullbackUnitIso f)
  | succ n ih =>
    let U := SheafOfModules.unit Y.ringCatSheaf
    let V := SheafOfModules.unit X.ringCatSheaf
    let P := tensorPower Y.presheaf Y.ringCatIsSheaf U (n : ℤ)
    let F := pullback f
    let T := tensorProductBifunctor X.presheaf X.ringCatIsSheaf
    let sY := tensorPowerSuccIso Y.presheaf Y.ringCatIsSheaf U (n : ℤ)
    let sP := tensorPowerSuccIso X.presheaf X.ringCatIsSheaf (F.obj U) (n : ℤ)
    let sV := tensorPowerSuccIso X.presheaf X.ringCatIsSheaf V (n : ℤ)
    let p := pullbackTensorPowerIso f U n
    let e := tensorPowerMap X (pullbackUnitIso f) n
    let q := structureSheafTensorPowerIso X n
    let r := tensorProductRightUnitor X.presheaf X.ringCatIsSheaf V
    let tP := Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f P U
    have hs := power_unit_step T (F.mapIso sY.symm) tP p sP e
      (pullbackUnitIso f) sV q r
    have hnat := pullbackTensorIso_tensorProductIso f
      (structureSheafTensorPowerIso Y n) (Iso.refl U)
    have hnat' := hnat.trans (congrArg (fun z => tP ≪≫
      tensorProductIso X.presheaf X.ringCatIsSheaf
        (F.mapIso (structureSheafTensorPowerIso Y n)) z) (F.mapIso_refl U))
    have hc := power_unit_core F T (structureSheafTensorPowerIso Y n) (pullbackUnitIso f)
      tP (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f U U)
      (tensorProductIso Y.presheaf Y.ringCatIsSheaf (structureSheafTensorPowerIso Y n)
        (Iso.refl U))
      (tensorProductRightUnitor Y.presheaf Y.ringCatIsSheaf U) r (p ≪≫ e ≪≫ q)
      hnat' (pullbackUnitIso_tensorProductRightUnitor f) ih
    have hh := hs.trans (congrArg (fun z => F.mapIso sY.symm ≪≫ z) hc)
    have hsrc := congrArg (fun z => pullbackTensorPowerIso f U (n + 1) ≪≫
      tensorPowerMap X (pullbackUnitIso f) (n + 1) ≪≫ z) (unit_power_succ X n)
    have htgt := congrArg (fun z => F.mapIso z ≪≫ pullbackUnitIso f) (unit_power_succ Y n)
    exact hsrc.trans (hh.trans ((map_iso_left F _ _ _).trans htgt.symm))

/-- The native nonnegative pullback-power comparison preserves the canonical trivialization
of the powers of the structure sheaf, with the original unit-pullback isomorphism. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "Algebra/Category/ModuleCat/Sheaf/PullbackTensorCoherence.lean:473-485" "ingredient"
  "Native right-unitor coherence, iterated using the original unit-power successor maps"]
theorem pullbackTensorPowerIso_structureSheaf {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorPowerIso f (SheafOfModules.unit Y.ringCatSheaf) n ≪≫
      tensorPowerCongr X.presheaf (ringSheafCond X) _ _ (pullbackUnitIso f) n ≪≫
        structureSheafTensorPowerIso X n =
    (pullback f).mapIso (structureSheafTensorPowerIso Y n) ≪≫ pullbackUnitIso f := by
  have h := congrArg (fun z => pullbackTensorPowerIso f
    (SheafOfModules.unit Y.ringCatSheaf) n ≪≫ z ≪≫ structureSheafTensorPowerIso X n)
      (tensorPowerMap_eq_tensorPowerCongr X (pullbackUnitIso f) n)
  exact h.symm.trans (pullbackTensorPowerIso_tensorPowerMap_unit f n)

end AlgebraicGeometry.Scheme.Modules
