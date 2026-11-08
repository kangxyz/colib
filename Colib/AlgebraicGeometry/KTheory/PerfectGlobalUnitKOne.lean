/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectGlobalUnit
public import Colib.AlgebraicGeometry.Modules.PerfectRankOneRestriction
public import Colib.AlgebraicGeometry.KTheory.PerfectRestriction
public import Colib.KTheory.Waldhausen.AutomorphismKOne

/-! # Fine K-one classes of actual global units

The independent class is built from the existing global-unit automorphism in the native
perfect category. Its actual object-component normalization and canonical chosen-zero
rebasing are those of `automorphismKOneClass` and `KMap`.

Adapted from `ScalarLaurentClassComparison.lean:37-47`, `GlobalUnitKOneInversion.lean`
and `GlobalUnitKOneRestriction.lean` in `Quillen/AlgebraicGeometry/PerfectComplexes` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory Waldhausen

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The independent fine class of the actual global-unit automorphism. -/
def perfectGlobalUnitKOneClass (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K 1 :=
  (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).automorphismKOneClass
    ((perfectGlobalUnitIso X q).app K)

/-- An isomorphic presentation of the native perfect object gives the same unit class. -/
theorem perfectGlobalUnitKOneClass_iso (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (e : K ≅ L) :
    perfectGlobalUnitKOneClass X q K = perfectGlobalUnitKOneClass X q L := by
  apply (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weakEndomorphismKOneClass_iso e
    ((perfectGlobalUnitIso X q).hom.app K) ((perfectGlobalUnitIso X q).hom.app L)
  simpa only [Functor.id_map] using ((perfectGlobalUnitIso X q).hom.naturality e.hom).symm

/-- Inverting the actual unit inverts its object-component-normalized fine class. -/
theorem perfectGlobalUnitKOneClass_inv (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectGlobalUnitKOneClass X q⁻¹ K = (perfectGlobalUnitKOneClass X q K)⁻¹ := by
  unfold perfectGlobalUnitKOneClass
  rw [perfectGlobalUnitIso_app_inv]
  exact ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).automorphismKOneHom K).map_inv
    (Aut.of ((perfectGlobalUnitIso X q).app K))

/-- The original fine restriction K-map preserves the actual pulled-back unit class. -/
theorem perfectGlobalUnitKOneClass_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (q : (Γ(X, ⊤))ˣ)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    KMap (perfectComplexesRestrictOpenImmersion_isExact j) 1
        (perfectGlobalUnitKOneClass X q K) =
      perfectGlobalUnitKOneClass U (Units.map j.appTop.hom.toMonoidHom q)
        ((perfectComplexesRestrictOpenImmersion j).obj K) := by
  unfold perfectGlobalUnitKOneClass
  rw [KMap_automorphismKOneClass, perfectRestrict_globalUnitIso_app]

/-- The fine restriction formula retains the actual structure-sheaf restriction isomorphism. -/
theorem perfectGlobalUnitKOneClass_restrict_rankOne {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (q : (Γ(X, ⊤))ˣ) :
    KMap (perfectComplexesRestrictOpenImmersion_isExact j) 1
        (perfectGlobalUnitKOneClass X q (rankOnePerfectComplex X)) =
      perfectGlobalUnitKOneClass U (Units.map j.appTop.hom.toMonoidHom q)
        (rankOnePerfectComplex U) := by
  rw [perfectGlobalUnitKOneClass_restrict]
  exact perfectGlobalUnitKOneClass_iso _ _ (rankOnePerfectComplexRestrictIso j)

/-- On a literal open subset this is the existing public restriction K-map. -/
theorem perfectGlobalUnitKOneClass_restrict_opens (X : Scheme.{u}) (U : X.Opens)
    (q : (Γ(X, ⊤))ˣ)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectComplexesRestrictKMap X U 1 (perfectGlobalUnitKOneClass X q K) =
      perfectGlobalUnitKOneClass U.toScheme (Units.map U.ι.appTop.hom.toMonoidHom q)
        ((perfectComplexesRestrictFunctor X U).obj K) :=
  perfectGlobalUnitKOneClass_restrict U.ι q K

attribute [colib_tag "COL-0305"] perfectGlobalUnitKOneClass
  perfectGlobalUnitKOneClass_inv perfectGlobalUnitKOneClass_restrict

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarLaurentClassComparison.lean:37-47"
  "adaptation" "The independent fine class of the actual native global-unit automorphism,
    invariant under actual object isomorphisms with the original component normalization"]
  perfectGlobalUnitKOneClass perfectGlobalUnitKOneClass_iso

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GlobalUnitKOneInversion.lean:32-40"
  "adaptation" "The inverse unit gives the inverse normalized fine class, using native Aut.asIso"]
  perfectGlobalUnitKOneClass_inv

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/GlobalUnitKOneRestriction.lean:33-49"
  "adaptation" "Actual fine open restriction, with the original canonical zero rebase and the
    native structure-sheaf restriction isomorphism"]
  perfectGlobalUnitKOneClass_restrict perfectGlobalUnitKOneClass_restrict_rankOne

end AlgebraicGeometry.Scheme.Modules
