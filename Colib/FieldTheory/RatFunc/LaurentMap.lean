/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.RatFunc.CoefficientMap
public import Mathlib.FieldTheory.Laurent

/-!
# Native rational Taylor translation and coefficient extension

The original `RatFunc.laurent a` is the native Taylor translation on rational
functions, with coordinate `X + C a`. It commutes with the existing rational
coefficient map after translating the center by that same field map.
No rational map or field model is defined.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace RatFunc

variable {k : Type u} [Field k] {K : Type v} [Field K]

/-- The native rational Taylor map commutes with the original coefficient map. -/
theorem laurent_comp_mapRingHom (φ : k →+* K) (a : k) :
    (laurent (φ a)).toRingHom.comp
        (mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) =
      (mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)).comp
          (laurent a).toRingHom := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
  apply RingHom.ext
  intro p
  change laurent (φ a)
      (mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
          (algebraMap k[X] (RatFunc k) p)) =
    mapRingHom (Polynomial.mapRingHom φ)
      (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)
        (laurent a (algebraMap k[X] (RatFunc k) p))
  rw [mapRingHom_algebraMap, laurent_algebraMap, laurent_algebraMap,
    mapRingHom_algebraMap]
  change algebraMap K[X] (RatFunc K) (taylor (φ a) (p.map φ)) =
    algebraMap K[X] (RatFunc K) ((taylor a p).map φ)
  rw [Polynomial.map_taylor]

/-- Coefficient naturality evaluated at an arbitrary original rational function. -/
theorem laurent_mapRingHom (φ : k →+* K) (a : k) (x : RatFunc k) :
    laurent (φ a)
        (mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) x) =
      mapRingHom (Polynomial.mapRingHom φ)
        (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ) (laurent a x) :=
  RingHom.congr_fun (laurent_comp_mapRingHom φ a) x

/-- A constant-coefficient polynomial is fixed by native rational translation. -/
theorem map_C_laurent (a : k) (p : k[X]) :
    (p.map (C : k →+* RatFunc k)).map (laurent a).toRingHom = p.map C := by
  rw [Polynomial.map_map]
  congr 1
  ext c
  exact laurent_C a c

end RatFunc
