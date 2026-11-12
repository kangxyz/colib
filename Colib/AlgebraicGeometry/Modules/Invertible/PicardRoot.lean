/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# Actual tensor roots from Picard divisibility

A divisible Picard class supplies an invertible module and an isomorphism from its tensor
power to the specified module. No cohomology or properness hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Kummer

/-- Divisibility of the class of an invertible module supplies an actual invertible module
and an isomorphism from its tensor power, not merely another Picard class. -/
theorem exists_schemeTensorPower_iso_of_picard_nsmul (X : Scheme.{u}) (n : ℕ)
    (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
    (h : ∃ c : Picard.ofScheme X, n • c = X.picardClass L hL) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅ L) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨M, hM, hMc⟩ := Stacks.SheafOfModules.exists_picardClass_eq
    X.presheaf X.ringCatIsSheaf c
  refine ⟨M, hM, (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _
    (Stacks.SheafOfModules.isInvertible_schemeTensorPower X M hM (n : ℤ)) hL).1 ?_⟩
  refine (Stacks.SheafOfModules.picardClass_schemeTensorPower X M hM (n : ℤ)).trans ?_
  calc
    (n : ℤ) • Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf M hM =
        n • Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf M hM :=
      natCast_zsmul _ _
    _ = n • c := congrArg (fun z => n • z) hMc
    _ = _ := hc

/-- An actual tensor root of a pullback gives the corresponding equality of Picard classes.
The pullback is the native scheme-module pullback, with no cohomological hypotheses. -/
theorem nsmul_picardClass_eq_pullback_of_schemeTensorPower_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (L : Y.Modules) (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L)
    (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (e : Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
      (Scheme.Modules.pullback f).obj L) :
    n • X.picardClass M hM = Picard.schemePullbackClassHom f (Y.picardClass L hL) := by
  have hpull := Stacks.RingedSpace.modulePullback_isInvertible_of f.toLRSHom.toShHom L hL
  have he := (Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatIsSheaf _ _
    (Stacks.SheafOfModules.isInvertible_schemeTensorPower X M hM (n : ℤ)) hpull).2 ⟨e⟩
  calc
    n • X.picardClass M hM = (n : ℤ) • X.picardClass M hM :=
      (natCast_zsmul _ _).symm
    _ = Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
        (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ))
        (Stacks.SheafOfModules.isInvertible_schemeTensorPower X M hM (n : ℤ)) :=
      (Stacks.SheafOfModules.picardClass_schemeTensorPower X M hM (n : ℤ)).symm
    _ = _ := he.trans (Picard.pullbackClass_classOf f.toLRSHom.toShHom L hL).symm

end Stacks.Kummer
