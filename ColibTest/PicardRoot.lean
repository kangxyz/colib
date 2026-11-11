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
