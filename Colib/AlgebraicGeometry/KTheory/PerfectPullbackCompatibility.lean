/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectPullbackCompatibility
public import Colib.AlgebraicGeometry.KTheory.PerfectPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectFlatPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport

/-! # Compatibility with the original flat and open perfect K-maps

These equalities concern the actual canonical KMaps in every natural degree, including zero.
Only the target of arbitrary pullback is assumed compact. No source compactness, separation,
regularity or resolution property is imposed. No whole-prespectrum homotopy is asserted.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullback.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- The actual exact flat K-map commutes with the unchanged literal inclusion. -/
@[colib_tag "COL-0328",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Functor.lean:101-106"
    "adaptation" "The actual flat pullback square of unchanged literal inclusion KMaps"]
theorem boundedAboveFlatPerfectToPerfectKMap_flatPullback (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) n).comp
        (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace n) =
      (boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n).comp
        (boundedAboveFlatPerfectKPullback f n) := by
  unfold boundedAboveFlatPerfectToPerfectKMap boundedAboveFlatPerfectKPullback
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (boundedAboveFlatPerfectInclusionFlatPullbackIso f) n

/-- Arbitrary perfect K-pullback is the original exact flat K-map when the morphism is flat. -/
@[colib_tag "COL-0328",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/DerivedPullback.lean:77-88"
    "generalization" "Original flat/open map equality, requiring only target compactness"]
theorem perfectKPullback_eq_flatPullback [CompactSpace Y] (f : X ⟶ Y) [Flat f] (n : ℕ) :
    perfectKPullback f n = Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) n :=
  (perfectKPullback_unique f n _ (boundedAboveFlatPerfectToPerfectKMap_flatPullback f n)).symm

/-- Open immersion pullback is the canonical K-map of actual ordinary restriction. -/
@[colib_tag "COL-0328"]
theorem perfectKPullback_eq_restrict [CompactSpace Y] (j : X ⟶ Y) [IsOpenImmersion j]
    (n : ℕ) :
    perfectKPullback j n =
      Waldhausen.KMap (perfectComplexesRestrictOpenImmersion_isExact j) n :=
  (perfectKPullback_eq_flatPullback j n).trans
    (Waldhausen.KMap_eq_of_iso _ _ (perfectRestrictIsoFlatPullback j).symm n)

/-- The original open-subset restriction map is unchanged, even for a noncompact open. -/
@[colib_tag "COL-0328"]
theorem perfectKPullback_eq_restrictSubset (Y : Scheme.{u}) [CompactSpace Y]
    (U : Y.Opens) (n : ℕ) :
    perfectKPullback U.ι n = perfectComplexesRestrictKMap Y U n :=
  (perfectKPullback_eq_restrict U.ι n).trans
    (Waldhausen.KMap_eq_of_iso _ _ (perfectRestrictSubsetIsoOpenImmersion Y U).symm n)

/-- The existing coarse restriction composite is the same actual perfect pullback map. -/
theorem perfectOpenKRestrict_comp_eq_perfectKPullback [CompactSpace Y]
    (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectOpenKMap j n) = perfectKPullback j n :=
  (perfectOpenKRestrict_comp_perfectOpenKMap j n).trans (perfectKPullback_eq_restrict j n).symm

/-- Composition with an exact flat pullback needs no compactness of the middle scheme. -/
theorem perfectKPullback_comp_flatLeft [CompactSpace Z] (f : X ⟶ Y) [Flat f]
    (g : Y ⟶ Z) (n : ℕ) :
    perfectKPullback (f ≫ g) n =
      (Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) n).comp
        (perfectKPullback g n) := by
  symm
  apply perfectKPullback_unique
  rw [MonoidHom.comp_assoc, boundedAboveFlatPerfectToPerfectKMap_pullback,
    ← MonoidHom.comp_assoc, boundedAboveFlatPerfectToPerfectKMap_flatPullback,
    MonoidHom.comp_assoc, boundedAboveFlatPerfectKPullback_comp]

/-- A commuting open-pair square intertwines the actual ambient restriction K-maps.
This does not construct a supported or relative-open pullback. -/
@[colib_tag "COL-0328"]
theorem perfectKPullback_restrict_square {U V : Scheme.{u}} [CompactSpace Y]
    [CompactSpace V] (j : U ⟶ X) (k : V ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] (f : X ⟶ Y) (g : U ⟶ V)
    (h : j ≫ f = g ≫ k) (n : ℕ) :
    (Waldhausen.KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).comp
        (perfectKPullback f n) =
      (perfectKPullback g n).comp
        (Waldhausen.KMap (perfectComplexesRestrictOpenImmersion_isExact k) n) := by
  have hj := Waldhausen.KMap_eq_of_iso
    (perfectComplexesRestrictOpenImmersion_isExact j)
    (perfectFlatPullback_waldhausenExact j) (perfectRestrictIsoFlatPullback j) n
  rw [hj, ← perfectKPullback_comp_flatLeft, ← perfectKPullback_eq_restrict,
    ← perfectKPullback_comp, h]

end AlgebraicGeometry.Scheme
