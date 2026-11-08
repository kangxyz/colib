/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.RelativeFlatFactorization
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectQuasiCompact
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectWaldhausen
public import Colib.CategoryTheory.Waldhausen.Approximation.Basic

/-!
# Actual Approximation by Bounded Above Flat Perfect Complexes

A common upper bound permits good truncation of the target without changing its cohomology.
The actual relative flat factorization supplies the original commuting triangle. Its short
exact quotient is perfect by the native cone-to-quotient quasi-isomorphism, so the inclusion
is a genuine admissible cofibration. On quasi-compact ringed spaces, local perfectness supplies
the required target bound; no quasi-separatedness or resolution property is assumed.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Approximation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, on the native original chain maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.RingedSpace

/-- An actual bound gives the original cofibration and quasi-isomorphism factorization. -/
@[colib_tag "COL-0325",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Approximation.lean:43-77"
    "adaptation" "Actual App2 factorization, with an actual bounded-above flat perfect quotient"]
theorem boundedAboveFlatPerfect_relative_factorization_of_bound {X : RingedSpace.{u, u}}
    (K : (boundedAboveFlatPerfectComplex X).FullSubcategory)
    (L : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X)))
    (f : (boundedAboveFlatPerfectInclusion X).obj K ⟶ L) (b : ℤ)
    [K.obj.IsStrictlyLE b] [L.obj.IsLE b] :
    ∃ (M : (boundedAboveFlatPerfectComplex X).FullSubcategory) (i : K ⟶ M)
      (p : (boundedAboveFlatPerfectInclusion X).obj M ⟶ L),
      (boundedAboveFlatPerfectWaldhausen X).cof i ∧
        (perfectComplexesWaldhausen X).weq p ∧
        (boundedAboveFlatPerfectInclusion X).map i ≫ p = f := by
  let s : K.obj ⟶ L.obj := f.hom
  let fT := boundedAboveMapToTruncLE s b
  obtain ⟨M, Q, i, p₀, q, w, hp₀, hfac, hS, hbM, hbQ, hMflat, hQflat⟩ :=
    exists_boundedAbove_relative_flat_factorization X fT b K.property.2.2
  let : QuasiIso p₀ := hp₀
  let p : M ⟶ L.obj := p₀ ≫ L.obj.ιTruncLE b
  have hp : QuasiIso p := by dsimp [p]; infer_instance
  have hMp : IsPerfectComplex M := (isPerfectComplex_iff_of_quasiIso p hp).mpr L.property
  have hQp : IsPerfectComplex Q := isPerfectComplex_X₃_of_shortExact hS K.property.1 hMp
  let M' : (boundedAboveFlatPerfectComplex X).FullSubcategory :=
    ⟨M, hMp, ⟨b + 1, hbM⟩, hMflat⟩
  let i' : K ⟶ M' := ObjectProperty.homMk i
  let p' : (boundedAboveFlatPerfectInclusion X).obj M' ⟶ L := ObjectProperty.homMk p
  refine ⟨M', i', p', ?_, hp, ?_⟩
  · exact (boundedAboveFlatPerfectWaldhausen_cof_iff X i').mpr
      ⟨Q, ⟨hQp, ⟨b + 1, hbQ⟩, hQflat⟩, q, w, hS⟩
  · apply ObjectProperty.hom_ext
    change i ≫ (p₀ ≫ L.obj.ιTruncLE b) = f.hom
    rw [← Category.assoc, hfac]
    exact boundedAboveMapToTruncLE_comp s b

/-- Quasi-compactness alone proves App1 and the genuine relative App2 for the literal inclusion. -/
@[colib_tag "COL-0325",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Approximation.lean:79-91"
    "adaptation"
    "Quasi-compact-only approximation, without an assumed replacement or K-equivalence"]
theorem boundedAboveFlatPerfectInclusion_approximation
    (X : RingedSpace.{u, u}) [CompactSpace X.carrier] :
    Waldhausen.HasApproximationProperty (boundedAboveFlatPerfectWaldhausen X)
      (perfectComplexesWaldhausen X) (boundedAboveFlatPerfectInclusion X) where
  reflects _ h := h
  lift {K L} f := by
    obtain ⟨b, hb⟩ := L.property.exists_isLE
    obtain ⟨c, hc⟩ := K.property.2.1
    have : K.obj.IsStrictlyLE (max c b) := K.obj.isStrictlyLE_of_le c _ (le_max_left _ _)
    have : L.obj.IsLE (max c b) := L.obj.isLE_of_le b _ (le_max_right _ _)
    exact boundedAboveFlatPerfect_relative_factorization_of_bound K L f (max c b)

end AlgebraicGeometry.RingedSpace
