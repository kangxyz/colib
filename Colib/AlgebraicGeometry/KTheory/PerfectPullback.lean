/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPullback
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectComparison

/-!
# Arbitrary perfect K-pullback via the literal flat comparison

For quasi-compact schemes the proved literal inclusion equivalence transports the actual
bounded-above flat chain K-map to all native perfect complexes. This does not assert that
underived pullback is exact on all perfect chain complexes. Compactness is used only by the
flat-to-perfect comparison. No quasi-separatedness or resolution property is required.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullbackFunctor.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}} [CompactSpace Y] [CompactSpace Z]

/-- Actual perfect K-pullback, conjugated by the equivalence of the literal flat inclusion. -/
@[colib_tag "COL-0326",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullback.lean:33-38"
    "adaptation" "Actual flat KMap transported by the proved literal inclusion comparison"]
def perfectKPullback (f : X ⟶ Y) (n : ℕ) :
    (perfectComplexesWaldhausen Y.toRingedSpace).K n →*
      (perfectComplexesWaldhausen X.toRingedSpace).K n :=
  (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n).comp
    ((boundedAboveFlatPerfectKPullback f n).comp
      (boundedAboveFlatPerfectKEquiv Y.toRingedSpace n).symm.toMonoidHom)

/-- The unchanged literal inclusion K-map intertwines actual flat and perfect pullback. -/
@[colib_tag "COL-0326"]
theorem boundedAboveFlatPerfectToPerfectKMap_pullback (f : X ⟶ Y) (n : ℕ) :
    (perfectKPullback f n).comp (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace n) =
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n).comp
        (boundedAboveFlatPerfectKPullback f n) := by
  ext a
  change boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n
    (boundedAboveFlatPerfectKPullback f n
      ((boundedAboveFlatPerfectKEquiv Y.toRingedSpace n).symm
        ((boundedAboveFlatPerfectKEquiv Y.toRingedSpace n) a))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The actual flat representative square uniquely determines all-perfect K-pullback. -/
theorem perfectKPullback_unique (f : X ⟶ Y) (n : ℕ)
    (k : (perfectComplexesWaldhausen Y.toRingedSpace).K n →*
      (perfectComplexesWaldhausen X.toRingedSpace).K n)
    (hk : k.comp (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace n) =
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n).comp
        (boundedAboveFlatPerfectKPullback f n)) : k = perfectKPullback f n := by
  apply (MonoidHom.cancel_right
    (boundedAboveFlatPerfectToPerfectKMap_bijective Y.toRingedSpace n).surjective).1
  exact hk.trans (boundedAboveFlatPerfectToPerfectKMap_pullback f n).symm

@[simp]
theorem perfectKPullback_id (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    perfectKPullback (𝟙 X) n = MonoidHom.id ((perfectComplexesWaldhausen X.toRingedSpace).K n) := by
  ext a
  obtain ⟨b, rfl⟩ := (boundedAboveFlatPerfectToPerfectKMap_bijective X.toRingedSpace n).surjective a
  have h := DFunLike.congr_fun (boundedAboveFlatPerfectToPerfectKMap_pullback (𝟙 X) n) b
  simpa only [MonoidHom.comp_apply, boundedAboveFlatPerfectKPullback_id, MonoidHom.id_apply] using h

@[simp]
theorem perfectKPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    perfectKPullback (f ≫ g) n = (perfectKPullback f n).comp (perfectKPullback g n) := by
  apply (MonoidHom.cancel_right
    (boundedAboveFlatPerfectToPerfectKMap_bijective Z.toRingedSpace n).surjective).1
  rw [boundedAboveFlatPerfectToPerfectKMap_pullback, MonoidHom.comp_assoc,
    boundedAboveFlatPerfectToPerfectKMap_pullback, ← MonoidHom.comp_assoc,
    boundedAboveFlatPerfectToPerfectKMap_pullback, MonoidHom.comp_assoc,
    boundedAboveFlatPerfectKPullback_comp]

/-- The original bounded-vector-bundle-to-perfect inclusion is natural under arbitrary pullback. -/
@[colib_tag "COL-0326"]
theorem boundedFiniteLocallyFreeToPerfectKMap_pullback (f : X ⟶ Y) (n : ℕ) :
    (perfectKPullback f n).comp (boundedFiniteLocallyFreeToPerfectKMap Y n) =
      (boundedFiniteLocallyFreeToPerfectKMap X n).comp (boundedFiniteLocallyFreeKPullback f n) := by
  rw [← boundedAboveFlatPerfectToPerfectKMap_comp, ← boundedAboveFlatPerfectToPerfectKMap_comp,
    ← MonoidHom.comp_assoc, boundedAboveFlatPerfectToPerfectKMap_pullback,
    MonoidHom.comp_assoc, boundedFiniteLocallyFreeToFlatKMap_pullback, MonoidHom.comp_assoc]

end AlgebraicGeometry.Scheme
