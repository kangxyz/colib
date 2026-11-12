/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularGeneratorRatioBoundary

/-! The ordinary unit ratio retains the full boundary scheme, including nilpotents. -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

example {X B : Scheme.{u}} (i : B ⟶ X) (P : X.Modules)
    (U : X.Opens) (hU : (⊤ : B.Opens) ≤ i ⁻¹ᵁ U)
    (p c : Stacks.SheafOfModules.GeneratorSections X.toRingedSpace P U)
    (τ : (pullback i).obj P ≅ SheafOfModules.unit B.ringCatSheaf)
    (hp : Hom.app τ.hom ⊤ (pullbackSectionHom i P U ⊤ hU p.val) = (1 : Γ(B, ⊤)))
    (hc : Hom.app τ.hom ⊤ (pullbackSectionHom i P U ⊤ hU c.val) = (1 : Γ(B, ⊤))) :
    i.appLE U ⊤ hU (Stacks.SheafOfModules.generatorRatioUnit P U p c).val =
      (1 : Γ(B, ⊤)) :=
  appLE_generatorRatioUnit_eq_one i P U hU p c τ hp hc

#print axioms AlgebraicGeometry.Scheme.Modules.appLE_generatorRatioUnit_eq_one
