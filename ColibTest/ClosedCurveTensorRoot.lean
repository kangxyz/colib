module

import Colib.AlgebraicGeometry.EtaleCohomology.ClosedCurveTensorRoot

open CategoryTheory AlgebraicGeometry Stacks.Kummer

universe u

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  (q : X ⟶ Spec (.of k)) [IsCurve k q] [Smooth q] [IsProper q]
  (L : X.Modules) (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L)
  (hdeg : picardDegree k q (IsCurve.topologicalKrullDim_eq_one (k := k) (f := q)).le
    (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace (X.picardClass L hL)) = 0)

-- Only separable closedness is assumed; no algebraic-closedness instance is supplied.
-- Composite exponents return the original module as an actual tensor power.
example (hn : IsUnit (6 : k)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (6 : ℤ) ≅ L) :=
  exists_schemeTensorPower_iso_of_picardDegree_eq_zero q (n := 6) hn L hL hdeg

-- Exponent one uses the same endpoint and needs no characteristic assumption.
example :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (1 : ℤ) ≅ L) :=
  exists_schemeTensorPower_iso_of_picardDegree_eq_zero q (n := 1) (by simp) L hL hdeg

open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory

-- The lower point wrapper also exposes no etaleness certificate.
example (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (hn : IsUnit (6 : k))
    (a : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ∃ b : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A), 6 • b = a :=
  Stacks.Groupoids.exists_nsmul_eq_of_isUnit_of_isSepClosed A 6 hn a
