/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryRoot
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.PullbackComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMapSuccessor

/-!
# Comparing the native integral and nonnegative pullback powers

The Kummer frame and inverse-limit root constructions use two native comparisons for
pullback of a tensor power. They agree in every nonnegative degree, as isomorphisms of the
actual modules. The proof identifies the unit comparisons and uses their common successor
square; it does not replace equality of morphisms by agreement on residue-field points.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local implicit_reducible] TopCat.Sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.instCategory AlgebraicGeometry.Scheme.unitModule

local instance (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf
      ((pullback f).obj M) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj f.toLRSHom.toShHom M

local instance (X : Scheme.{u}) (M : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).flip.obj M).IsEquivalence :=
  Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _

/-- The integral and scheme-module unit-pullback comparisons are the same isomorphism. -/
theorem pullbackUnitSheafIso_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Stacks.TensorPowerPullback.pullbackUnitSheafIso f.toLRSHom.toShHom =
      pullbackUnitIso f := by
  apply Iso.ext
  rfl

private theorem powNatSuccIso_eq {C : Type*} [Category C] (e : C ≌ C) :
    ∀ (n : ℕ) (M : C), powNatSuccIso e n M = Stacks.Equivalence.powNatSuccIso e n M
  | 0, _ => rfl
  | 1, _ => rfl
  | n + 2, M => powNatSuccIso_eq e (n + 1) (e.functor.obj M)

private theorem tensorPowerSuccIso_nat_eq (X : Scheme.{u}) (M : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] (n : ℕ) :
    Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso X.presheaf X.ringCatIsSheaf M
      (n : ℤ) = tensorPowerSuccIso X.presheaf X.ringCatIsSheaf M (n : ℤ) :=
  (powNatSuccIso_eq _ n _).symm

private theorem successor_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {P Q R : D} (s : A ≅ B) (t : F.obj A ≅ P) (e : P ≅ Q)
    (v : Q ≅ R) (z : F.obj B ≅ R)
    (h : F.map s.hom ≫ z.hom = t.hom ≫ e.hom ≫ v.hom) :
    z = F.mapIso s.symm ≪≫ t ≪≫ e ≪≫ v := by
  apply Iso.ext
  apply (cancel_epi (F.map s.hom)).mp
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_map_assoc] using h

/-- Pullback of a natural tensor power uses the same original isomorphism in the integral
Kummer convention and the nonnegative inverse-limit convention. -/
@[colib_tag "COL-1109", colib_ref "axiom_stacks_5ed82d14"
  "Algebra/Category/ModuleCat/Sheaf/TensorPowerMapSuccessor.lean:82-101" "ingredient"
  "The integral pullback comparison satisfies the same successor square as the natural one"]
theorem pullbackIntegerTensorPowerIso_nat_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M) (n : ℕ) :
    let := hM
    pullbackIntegerTensorPowerIso f M hM (n : ℤ) = pullbackTensorPowerIso f M n := by
  let := hM
  induction n with
  | zero =>
    exact pullbackUnitSheafIso_eq f
  | succ n ih =>
    let P := tensorPower Y.presheaf Y.ringCatIsSheaf M (n : ℤ)
    let Q := (pullback f).obj M
    let T := Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f P M
    let F := (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).flip.obj Q
    have h := Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_tensorPowerSuccIso
      Y.presheaf Y.ringCatIsSheaf X.presheaf X.ringCatIsSheaf (pullback f) M
      (Stacks.TensorPowerPullback.tensorFactorComparison f.toLRSHom.toShHom M)
      (Stacks.TensorPowerPullback.pullbackUnitSheafIso f.toLRSHom.toShHom) (n : ℤ)
    rw [tensorPowerSuccIso_nat_eq, tensorPowerSuccIso_nat_eq] at h
    have hz := successor_eq (pullback f) (tensorPowerSuccIso Y.presheaf Y.ringCatIsSheaf M
      (n : ℤ)) T (F.mapIso (pullbackIntegerTensorPowerIso f M hM (n : ℤ)))
      (tensorPowerSuccIso X.presheaf X.ringCatIsSheaf Q (n : ℤ))
      (pullbackIntegerTensorPowerIso f M hM ((n : ℤ) + 1)) h
    change pullbackIntegerTensorPowerIso f M hM ((n : ℤ) + 1) = _
    rw [hz]
    change (pullback f).mapIso (tensorPowerSuccIso Y.presheaf Y.ringCatIsSheaf M
      (n : ℤ)).symm ≪≫ T ≪≫ F.mapIso (pullbackIntegerTensorPowerIso f M hM (n : ℤ)) ≪≫
      tensorPowerSuccIso X.presheaf X.ringCatIsSheaf Q (n : ℤ) = _
    rw [ih]
    rfl

private theorem tensorProductIso_eq (X : Scheme.{u}) {A B C D : X.Modules}
    (e : A ≅ B) (f : C ≅ D) :
    tensorProductIso X.presheaf X.ringCatIsSheaf e f =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).flip.obj C).mapIso e ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).obj B).mapIso f := by
  apply Iso.ext
  exact (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
      (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩ e.hom f.hom).symm

private theorem iso_congr_middle {C : Type*} [Category C] {A B D E G : C}
    (s : A ≅ B) (e : B ≅ D) (f : D ≅ E) (t : E ≅ G) (z : B ≅ E)
    (h : z = e ≪≫ f) : s ≪≫ z ≪≫ t = s ≪≫ e ≪≫ f ≪≫ t := by
  simp only [h, Iso.trans_assoc]

/-- The Kummer map on natural tensor powers is the original natural-power isomorphism. -/
@[colib_tag "COL-1109"]
theorem tensorPowerMap_eq_tensorPowerCongr (X : Scheme.{u}) {M L : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X) M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X) L]
    (e : M ≅ L) (n : ℕ) :
    tensorPowerMap X e n = tensorPowerCongr X.presheaf (ringSheafCond X) M L e n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tensorPowerMap, tensorPowerCongr, ih]
    exact iso_congr_middle _ _ _ _ _ (tensorProductIso_eq X
      (tensorPowerCongr X.presheaf (ringSheafCond X) M L e n) e)

end AlgebraicGeometry.Scheme.Modules
