module

import Colib.AlgebraicGeometry.Modules.Invertible.PicardRoot

/-! Tests for extracting actual tensor roots from divisible Picard classes. -/

open CategoryTheory AlgebraicGeometry Stacks.Kummer

universe u

-- Root extraction is ordinary module theory and needs no cohomology or properness.
example (X : Scheme.{u}) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (1 : ℤ) ≅ L) :=
  exists_schemeTensorPower_iso_of_picard_nsmul X 1 L hL ⟨X.picardClass L hL, by simp⟩

-- An actual tensor-power isomorphism controls the literal native pullback on Picard classes.
example {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (L : Y.Modules) (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L)
    (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (e : Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
      (Scheme.Modules.pullback f).obj L) :
    n • X.picardClass M hM = Stacks.Picard.schemePullbackClassHom f (Y.picardClass L hL) :=
  nsmul_picardClass_eq_pullback_of_schemeTensorPower_iso f n L hL M hM e

-- The pure class calculation includes exponent zero, without invertibility of an integer.
example {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L)
    (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    (e : Stacks.SheafOfModules.schemeTensorPower X M hM 0 ≅
      (Scheme.Modules.pullback f).obj L) :
    0 • X.picardClass M hM = Stacks.Picard.schemePullbackClassHom f (Y.picardClass L hL) :=
  nsmul_picardClass_eq_pullback_of_schemeTensorPower_iso f 0 L hL M hM e
