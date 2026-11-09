/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectGlobalScalar
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullback
public import Colib.AlgebraicGeometry.Modules.GlobalScalarPullback

/-! # Global units on bounded-above flat perfect complexes

The actual fully faithful inclusion restricts the native degreewise global unit. Both directions
retain the original scalar on each term, and arbitrary geometric pullback preserves this action.

Adapted from Quillen's `Modules/PerfectComplexes/BoundedFlat/GlobalUnit.lean` and
`GlobalUnitPullback.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.RingedSpace
open Stacks.RegularSequence (globalSmulCenter)

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Restrict the actual termwise global unit along the fully faithful chain inclusion. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/GlobalUnit.lean:25-28"
  "adaptation" "Native global unit on bounded-above flat perfect complexes"]
def boundedAboveFlatPerfectGlobalUnitIso (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ) :
    𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ≅
      𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
      (complexGlobalUnitIso X q))

/-- Inclusion retains the original forward scalar chain map. -/
theorem boundedAboveFlatPerfectGlobalUnitIso_hom_original (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
        ((boundedAboveFlatPerfectGlobalUnitIso X q).hom.app K) =
      (complexGlobalUnitIso X q).hom.app K.obj := by
  exact (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_preimage
    ((complexGlobalUnitIso X q).hom.app K.obj)

/-- Inclusion retains the original inverse scalar chain map. -/
theorem boundedAboveFlatPerfectGlobalUnitIso_inv_original (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
        ((boundedAboveFlatPerfectGlobalUnitIso X q).inv.app K) =
      (complexGlobalUnitIso X q).inv.app K.obj := by
  exact (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_preimage
    ((complexGlobalUnitIso X q).inv.app K.obj)

/-- Every forward term is multiplication by the native global unit. -/
theorem boundedAboveFlatPerfectGlobalUnitIso_hom_terms (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) (n : ℤ) :
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
      ((boundedAboveFlatPerfectGlobalUnitIso X q).hom.app K)).f n =
      (globalSmulCenter X (q : Γ(X, ⊤))).app (K.obj.X n) := by
  rw [boundedAboveFlatPerfectGlobalUnitIso_hom_original]
  rfl

/-- Every inverse term is multiplication by the native inverse unit. -/
theorem boundedAboveFlatPerfectGlobalUnitIso_inv_terms (X : Scheme.{u}) (q : (Γ(X, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) (n : ℤ) :
    ((boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map
      ((boundedAboveFlatPerfectGlobalUnitIso X q).inv.app K)).f n =
      (globalSmulCenter X (↑(q⁻¹) : Γ(X, ⊤))).app (K.obj.X n) := by
  rw [boundedAboveFlatPerfectGlobalUnitIso_inv_original]
  rfl

/-- Arbitrary geometric pullback preserves the actual forward global-unit action. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    GlobalUnitPullback.lean:22-36"
  "adaptation" "Native scalar compatibility for arbitrary bounded-above flat perfect pullback"]
theorem boundedAboveFlatPerfectPullback_map_globalUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : (Γ(Y, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectPullback f).map
        ((boundedAboveFlatPerfectGlobalUnitIso Y q).hom.app K) =
      (boundedAboveFlatPerfectGlobalUnitIso X
        (Units.map f.appTop.hom.toMonoidHom q)).hom.app
          ((boundedAboveFlatPerfectPullback f).obj K) := by
  apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
  change ((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((boundedAboveFlatPerfectComplex Y.toRingedSpace).ι.map
      ((boundedAboveFlatPerfectGlobalUnitIso Y q).hom.app K)) = _
  rw [boundedAboveFlatPerfectGlobalUnitIso_hom_original,
    boundedAboveFlatPerfectGlobalUnitIso_hom_original]
  ext n : 1
  exact pullback_map_globalSmulCenter f (q : Γ(Y, ⊤)) (K.obj.X n)

/-- Arbitrary geometric pullback also preserves the actual inverse global-unit action. -/
theorem boundedAboveFlatPerfectPullback_map_globalUnit_inv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : (Γ(Y, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectPullback f).map
        ((boundedAboveFlatPerfectGlobalUnitIso Y q).inv.app K) =
      (boundedAboveFlatPerfectGlobalUnitIso X
        (Units.map f.appTop.hom.toMonoidHom q)).inv.app
          ((boundedAboveFlatPerfectPullback f).obj K) := by
  apply (boundedAboveFlatPerfectComplex X.toRingedSpace).ι.map_injective
  change ((pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((boundedAboveFlatPerfectComplex Y.toRingedSpace).ι.map
      ((boundedAboveFlatPerfectGlobalUnitIso Y q).inv.app K)) = _
  rw [boundedAboveFlatPerfectGlobalUnitIso_inv_original,
    boundedAboveFlatPerfectGlobalUnitIso_inv_original]
  ext n : 1
  exact pullback_map_globalSmulCenter f (↑(q⁻¹) : Γ(Y, ⊤)) (K.obj.X n)

end AlgebraicGeometry.Scheme.Modules
