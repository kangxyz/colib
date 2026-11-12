/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.CommonNonvanishingRatio

/-! The common open, generators, unit and full-boundary normalization are all constructed. -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

example {X B : Scheme.{u}} (P : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf P]
    (i : B ⟶ X) (Up Uc : X.Opens)
    (hUp : (⊤ : B.Opens) ≤ i ⁻¹ᵁ Up) (hUc : (⊤ : B.Opens) ≤ i ⁻¹ᵁ Uc)
    (p : Γ(P, Up)) (c : Γ(P, Uc))
    (τ : (pullback i).obj P ≅ SheafOfModules.unit B.ringCatSheaf)
    (hp : Hom.app τ.hom ⊤ (pullbackSectionHom i P Up ⊤ hUp p) = (1 : Γ(B, ⊤)))
    (hc : Hom.app τ.hom ⊤ (pullbackSectionHom i P Uc ⊤ hUc c) = (1 : Γ(B, ⊤))) :
    i.appLE _ ⊤ (top_le_preimage_commonSectionNonvanishingOpen P i Up Uc hUp hUc p c τ hp hc)
      (commonNonvanishingRatioUnit P Up Uc p c).val = (1 : Γ(B, ⊤)) :=
  appLE_commonNonvanishingRatioUnit_eq_one P i Up Uc hUp hUc p c τ hp hc

#print axioms AlgebraicGeometry.Scheme.Modules.generatorOnLocalNonvanishing
#print axioms AlgebraicGeometry.Scheme.Modules.appLE_commonNonvanishingRatioUnit_eq_one
