/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.NativeNisnevichParameter

/-! # The original motivic parameter at its native signed endpoints

These equalities retain `motivicSheafParameterProduct` itself. The canonical
motivic complex is compared to native signed ordinary chains by its existing
isomorphism; no alternative parameter map or topology inverse is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The original motivic parameter is the native signed arrow with its actual
canonical source and target comparison isomorphisms. -/
theorem motivicSheafParameterProduct_eq_nativeSigned (q : ℕ) :
    motivicSheafParameterProduct k q =
      signedParameterArrow ((torusParameterSheafFunctor k).mapHomologicalComplex (.up ℤ))
          (reducedTorusNisnevichParameterCochain k q)
        (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega)
        (motivicSheafComplexOrdinaryShiftIso k q)
        (motivicSheafComplexOrdinaryShiftIso k (q + 1)) := by
  exact motivicSheafParameterProduct_eq k q

/-- Removing only the canonical endpoint comparisons gives the existing native
Nisnevich signed parameter, with the source inverse and target forward map. -/
theorem motivicSheafParameterProduct_nativeSigned_conjugate (q : ℕ) :
    (motivicSheafComplexOrdinaryShiftIso k q).inv ≫
      motivicSheafParameterProduct k q ≫
      (((torusParameterSheafFunctor k).mapHomologicalComplex (.up ℤ))).map ((shiftFunctor _ (1 :
          ℤ)).map
        (motivicSheafComplexOrdinaryShiftIso k (q + 1)).hom) =
    reducedTorusNisnevichParameterSigned k q := by
  rw [motivicSheafParameterProduct_eq_nativeSigned]
  simpa only [Iso.trans_refl, reducedTorusNisnevichParameterSigned] using
    (signedParameterArrow_conjugate ((torusParameterSheafFunctor k).mapHomologicalComplex (.up ℤ))
        (reducedTorusNisnevichParameterCochain k q)
      (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega) (Iso.refl _) (Iso.refl _)
      (motivicSheafComplexOrdinaryShiftIso k q)
      (motivicSheafComplexOrdinaryShiftIso k (q + 1)))

end AlgebraicGeometry.PresheafWithTransfers
