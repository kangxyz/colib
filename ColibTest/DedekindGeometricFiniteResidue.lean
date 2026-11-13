/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.DedekindFiniteResidue

open AlgebraicGeometry
open scoped nonZeroDivisors
universe u
noncomputable section
variable (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

local instance : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat K (nonZeroDivisors R)))

-- The literal original public map, with the supplied field and original algebra structure.
example (hfinite : ∀ p : IsDedekindDomain.HeightOneSpectrum R, Finite p.asIdeal.ResidueField) :
    Function.Injective (Scheme.pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R K))) 2) :=
  FGModuleCat.DedekindFiniteResidue.spec_genericGTwo_pullback_field_injective R K hfinite

#print axioms FGModuleCat.DedekindFiniteResidue.spec_genericGTwo_pullback_field_injective
