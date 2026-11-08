/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectGlobalScalar

/-! # Inversion and restriction of actual global-unit automorphisms

These are equalities of the existing native isomorphisms, before taking any K-theory class.
Adapted from `GlobalUnitInversion.lean` and `GlobalUnitRestriction.lean` in
`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No Aglib object or adapter is used.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The literal inverse scalar is the inverse of the actual perfect automorphism. -/
theorem perfectGlobalUnitIso_app_inv (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectGlobalUnitIso X q⁻¹).app K = ((perfectGlobalUnitIso X q).app K).symm := by
  apply Iso.ext
  rfl

/-- Literal open restriction takes the actual automorphism to its pulled-back unit. -/
theorem perfectRestrict_globalUnitIso_app {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (q : (Γ(X, ⊤))ˣ)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectComplexesRestrictOpenImmersion j).mapIso ((perfectGlobalUnitIso X q).app K) =
      (perfectGlobalUnitIso U (Units.map j.appTop.hom.toMonoidHom q)).app
        ((perfectComplexesRestrictOpenImmersion j).obj K) := by
  apply Iso.ext
  exact perfectRestrict_scalar_eq_globalUnit j (↑q)
    (Units.map j.appTop.hom.toMonoidHom q) rfl K

end AlgebraicGeometry.Scheme.Modules
