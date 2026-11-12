module

import Colib.AlgebraicGeometry.EtaleCohomology.ProperStrictlyHenselianRestriction

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology

universe u

attribute [local instance 2000] hasExt_sheaf_smallEtale_succ

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

-- The native quotient point uses the canonical residue-field structure.
example : GrothendieckTopology.Point (Spec (.of R)).smallEtaleTopology :=
  pointSmallEtale (Ω := IsLocalRing.ResidueField R) (residueFieldPoint R)

-- Exact public type: no acyclicity, invertibility, smoothness, or dimension assumption.
example {n : ℕ} (hn : 0 < n) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion R f) F q) :=
  bijective_etaleCohomologyRestrictionMap_closedFibre_of_strictlyHenselian R f hn q F hF

example {n : ℕ} (hn : 0 < n)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion R f) F 0) :=
  bijective_etaleCohomologyRestrictionMap_closedFibre_of_strictlyHenselian R f hn 0 F hF

example {n : ℕ} (hn : 0 < n)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion R f) F 2) :=
  bijective_etaleCohomologyRestrictionMap_closedFibre_of_strictlyHenselian R f hn 2 F hF

-- Positive integer 1 is allowed, not just primes or integers greater than 1.
example (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (1 : ℤ) • 𝟙 F = 0) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion R f) F q) :=
  bijective_etaleCohomologyRestrictionMap_closedFibre_of_strictlyHenselian
    R f (n := 1) (by decide) q F hF

-- Composite coefficients are allowed, without assuming 6 is invertible in R.
example (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (6 : ℤ) • 𝟙 F = 0) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} (closedFibreInclusion R f) F q) :=
  bijective_etaleCohomologyRestrictionMap_closedFibre_of_strictlyHenselian
    R f (n := 6) (by decide) q F hF
