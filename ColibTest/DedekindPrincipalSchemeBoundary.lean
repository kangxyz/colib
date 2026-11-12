/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.DedekindPrincipalBoundary

open CategoryTheory CategoryTheory.ExactCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent
open FGModuleCat.DedekindLocalDvr
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
noncomputable section
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
  (K : Type u) [Field K] [Algebra (Localization.AtPrime p.asIdeal) K]
  [IsFractionRing (Localization.AtPrime p.asIdeal) K]
  {π : Localization.AtPrime p.asIdeal} (hπ : Irreducible π)

-- The supplied field, original geometric pullbacks, and inverse scalar transport are retained.
example (n : ℕ) (a : Scheme.G (Spec (CommRingCat.of K)) (n + 1)) :
    publicSpecGRingEquiv (CommRingCat.of p.asIdeal.ResidueField) n
      (Scheme.pullbackG (Spec.map (principalClosedResidueEquiv R p hπ).toCommRingCatIso.hom) n
        (Scheme.PrincipalClosed.boundaryG (CommRingCat.of (Localization.AtPrime p.asIdeal)) π n
          (Scheme.pullbackG
            (Spec.map (principalAwayFieldEquiv R p K hπ).symm.toRingEquiv.toCommRingCatIso.hom)
            (n + 1) a))) =
    localDvrBoundary R p n
      ((FGModuleCat.finiteRestrictionExact.{u, u, u}
        (localFractionFieldEquiv R p K).toRingHom
        (RingHom.Finite.of_surjective _ (localFractionFieldEquiv R p K).surjective)).smallKMap
          (n + 1) (publicSpecGRingEquiv (CommRingCat.of K) (n + 1) a)) :=
  principalSchemeBoundary_nativeBoundary_field R p K hπ n a

#print axioms FGModuleCat.DedekindLocalDvr.principalSchemeBoundary_nativeBoundary
#print axioms FGModuleCat.DedekindLocalDvr.principalSchemeBoundary_nativeBoundary_field
