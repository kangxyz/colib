/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenMaps

/-! # Equality of the prescribed support for the literal restriction functor -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  {S : V.Opens} (h : j ⁻¹ᵁ T = S)

/-- The original restriction, with its target support written using an equal open. -/
def perfectSupportedRestrictCongr :
    (perfectSupported T.ι).FullSubcategory ⥤ (perfectSupported S.ι).FullSubcategory :=
  h ▸ perfectSupportedRestrict j T

/-- Exactness of the original restriction with the same support written differently. -/
theorem perfectSupportedRestrictCongr_exact :
    IsExact (perfectSupportedWaldhausen T.ι).cof (perfectSupportedWaldhausen T.ι).weq
      (perfectSupportedWaldhausen S.ι).cof (perfectSupportedWaldhausen S.ι).weq
      (perfectSupportedRestrictCongr j T h) := by
  subst S
  exact perfectSupportedRestrict_exact j T

/-- Rewriting the support leaves the original underlying restriction functor. -/
def perfectSupportedRestrictCongr_comp_ι :
    perfectSupportedRestrictCongr j T h ⋙ (perfectSupported S.ι).ι ≅
      (perfectSupported T.ι).ι ⋙ (restrictFunctor j).mapHomologicalComplex (.up ℤ) := by
  subst S
  exact Iso.refl _

end AlgebraicGeometry.Scheme.Modules
