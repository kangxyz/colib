/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.CoefficientPolynomialLaurentCoordinates
public import Colib.AlgebraicGeometry.ProjectiveLine.PositiveBassQuotient
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionUnits

/-! # Transport of the actual inverse Laurent operation on the coefficient fiber -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R)

local notation "pLaurent" =>
  (AlgebraicGeometry.Scheme.BaseChange.Coefficients.laurentProjection P a)

/-- The actual coefficient Laurent map is flat by its native geometric projection comparison. -/
instance compactFiberLaurentProjection_flat : Flat pLaurent := by
  let e := compactFiberLaurentIso P a
  let p := (Relative.laurentProjection.app (compactFiber P a)).hom
  let : IsIso e.hom := e.isIso_hom
  let : IsOpenImmersion e.hom := inferInstance
  let : Flat e.hom := inferInstance
  let : Flat p := Relative.instFlatLaurentProjection (compactFiber P a)
  rw [← compactFiberLaurentIso_projection P a]
  exact Flat.comp e.hom p

/-- The coefficient operation uses exactly the actual inverse of its forward Laurent scalar. -/
theorem positiveBassUnitSection_coefficient (n : ℕ) :
    (KMap (perfectFlatPullback_waldhausenExact (compactFiberLaurentIso P a).hom) (n + 1)).comp
      (positiveBassUnitSection (compactFiber P a) n) =
    originalKSelfTrackOperation _ _
      (perfectFlatUnitHomotopy pLaurent
        (boundedAboveFlatCoefficientUnit
          (Opposite.op P, (laurentUnderFunctor R).obj a)
          (PolynomialLaurent.laurentCoordinate a.right))⁻¹) n := by
  let p := (Relative.laurentProjection.app (compactFiber P a)).hom
  let e := (compactFiberLaurentIso P a).hom
  let q := relativeLaurentCoordinateUnit (compactFiber P a)
  have h := perfectFlatUnitHomotopy_originalKOperation_postcomp e p q⁻¹ n
  have hu : Units.map e.appTop.hom.toMonoidHom q⁻¹ =
      (boundedAboveFlatCoefficientUnit
        (Opposite.op P, (laurentUnderFunctor R).obj a)
        (PolynomialLaurent.laurentCoordinate a.right))⁻¹ := by
    rw [map_inv]
    exact congrArg Inv.inv (compactFiberLaurentIso_coordinate P a)
  change (KMap (perfectFlatPullback_waldhausenExact e) (n + 1)).comp
      (positiveBassUnitSection (compactFiber P a) n) = _ at h
  rw [hu] at h
  let : Flat pLaurent := compactFiberLaurentProjection_flat P a
  exact h.trans (@perfectFlatUnitHomotopy_originalKOperation_congr _ _ (e ≫ p) pLaurent
    (Flat.comp e p) (compactFiberLaurentProjection_flat P a)
    (compactFiberLaurentIso_projection P a) _ n)

end AlgebraicGeometry.Scheme.ProjectiveLine
