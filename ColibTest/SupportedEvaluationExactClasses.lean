/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupport

/-! Full-signature consumers for the actual fixed-open supported evaluation. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen
universe u
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]


example {K L : (boundedAboveFlatPerfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectSupportedWaldhausen j).cof f ↔
      ∃ (Q : CochainComplex (Spec R).Modules ℤ) (_hQ : boundedAboveFlatPerfectSupported j Q)
        (g : L.obj ⟶ Q) (h : f.hom ≫ g = 0),
        (ShortComplex.mk f.hom g h).ShortExact :=
  boundedAboveFlatPerfectSupportedWaldhausen_cof_iff j f

example {K L : (boundedAboveFlatPerfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectSupportedWaldhausen j).weq f ↔ QuasiIso f.hom :=
  boundedAboveFlatPerfectSupportedWaldhausen_weq_iff j f
