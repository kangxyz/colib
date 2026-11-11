/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Category.ModuleCat.Tor.RingTower

/-! # Direct consumers with literal maps, degree zero, and the actual inverse map -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

variable {R B A C : Type u} [CommRing R] [CommRing B] [CommRing A] [CommRing C]
  (f : R →+* B) (g : B →+* A) (φ : R →+* C)

section ModuleCoefficient

variable (M : ModuleCat.{u} R) (N : ModuleCat.{u} B)
  (h : ∀ i : ℕ, 0 < i → IsZero
    (((CategoryTheory.Tor (ModuleCat.{u} R) i).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))).obj M))

example (P : ProjectiveResolution M) :
    ProjectiveResolution ((ModuleCat.extendScalars.{u, u, u} f).obj M) :=
  ModuleCat.Tor.extendedProjectiveResolutionOfIsZeroTor f P h

example (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars f).obj N)).obj M ≅
      (ModuleCat.restrictScalars f).obj
        (((CategoryTheory.Tor (ModuleCat.{u} B) n).obj N).obj
          ((ModuleCat.extendScalars.{u, u, u} f).obj M)) :=
  ModuleCat.Tor.changeOfRingsIsoOfIsZeroTor f N M h n

-- Degree zero is part of the same construction; no vanishing in degree zero is assumed.
example :
    ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj N)).obj M ≅
      (ModuleCat.restrictScalars f).obj
        (((CategoryTheory.Tor (ModuleCat.{u} B) 0).obj N).obj
          ((ModuleCat.extendScalars.{u, u, u} f).obj M)) :=
  ModuleCat.Tor.changeOfRingsIsoOfIsZeroTor f N M h 0

end ModuleCoefficient

-- This consumer is about actual rings and their given coefficient maps, not placeholder objects.
section RingTower

variable (h : ∀ i : ℕ, 0 < i → IsZero
    (((CategoryTheory.Tor (ModuleCat.{u} R) i).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)))) (n : ℕ)

example :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A))).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) ≅
      (ModuleCat.restrictScalars f).obj
        (((CategoryTheory.Tor (ModuleCat.{u} B) n).obj
          ((ModuleCat.restrictScalars g).obj (ModuleCat.of A A))).obj
            ((ModuleCat.extendScalars.{u, u, u} f).obj
              ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)))) :=
  ModuleCat.Tor.ringTowerIsoOfIsZeroTor f g φ h n

-- Apply the actual inverse to the actual comparison of a native Tor element.
example
    (x : ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A))).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))) :
    (ModuleCat.Tor.ringTowerIsoOfIsZeroTor f g φ h n).inv
      ((ModuleCat.Tor.ringTowerIsoOfIsZeroTor f g φ h n).hom x) = x :=
  ModuleCat.inv_hom_apply (ModuleCat.Tor.ringTowerIsoOfIsZeroTor f g φ h n) x

-- The comparison preserves the given R-action, including on its restricted target.
example (r : R)
    (x : ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A))).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))) :
    (ModuleCat.Tor.ringTowerIsoOfIsZeroTor f g φ h n).hom (r • x) =
      r • (ModuleCat.Tor.ringTowerIsoOfIsZeroTor f g φ h n).hom x :=
  (ModuleCat.Tor.ringTowerIsoOfIsZeroTor f g φ h n).hom.hom.map_smul r x

end RingTower
