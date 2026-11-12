/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties.DepthRegularityAndFibres
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Regularity and integrality of the original strict-local scheme

At a geometric point of a regular scheme, the native geometric henselization tower preserves
regularity of the ordinary stalk. Its canonical ring equivalence transports regularity to the
original etale local ring. Thus the actual native strict henselization is regular, Noetherian
and integral. No smooth structure over a field is imposed on the strict-local scheme.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The original etale local ring over a locally Noetherian scheme is Noetherian. -/
theorem isNoetherianRing_etaleLocalRing [IsLocallyNoetherian S] :
    IsNoetherianRing ↥(etaleLocalRing B S hS s) := by
  let R := ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
  let T := geometricHenselizationTower S s
  have : IsNoetherianRing T.strictHenselization :=
    (isNoetherianRing_iff_henselizations R T.henselization T.strictHenselization
      (separableClosure (ResidueField R) s.residueField)).2.mp inferInstance
  exact isNoetherianRing_of_ringEquiv T.strictHenselization
    (etaleLocalRingEquivStrictHenselization B S hS s)

/-- Local Noetherianity of the original scheme makes its actual strict-local scheme
Noetherian; no regularity assumption is needed. -/
theorem isNoetherian_strictHenselization [IsLocallyNoetherian S] :
    IsNoetherian (strictHenselization B S hS s) := by
  have := isNoetherianRing_etaleLocalRing B S hS s
  infer_instance

/-- Regularity of the ordinary stalk passes through its native geometric henselization tower
and the canonical equivalence to the original etale local ring. -/
theorem isRegularLocalRing_etaleLocalRing_of_isRegular (hreg : IsRegular S) :
    IsRegularLocalRing ↥(etaleLocalRing B S hS s) := by
  have : IsLocallyNoetherian S := isLocallyNoetherian_of_isRegular hreg
  let R := ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField)))
  let T := geometricHenselizationTower S s
  have : IsRegularLocalRing R := ((isRegular_iff_regular_stalks S).mp hreg).2 _
  have : IsRegularLocalRing T.strictHenselization :=
    (isRegularLocalRing_iff_henselizations R T.henselization T.strictHenselization
      (separableClosure (ResidueField R) s.residueField)).2.mp inferInstance
  exact IsRegularLocalRing.of_ringEquiv
    (etaleLocalRingEquivStrictHenselization B S hS s)

/-- The actual etale local ring is regular as a ring, including its Noetherian condition. -/
theorem isRegularRing_etaleLocalRing_of_isRegular (hreg : IsRegular S) :
    IsRegularRing ↥(etaleLocalRing B S hS s) := by
  have := isRegularLocalRing_etaleLocalRing_of_isRegular B S hS s hreg
  exact ((IsLocalRing.isRegularRing_tfae (R := ↥(etaleLocalRing B S hS s))).out 1 3).mp
    (inferInstance : IsRegularLocalRing ↥(etaleLocalRing B S hS s))

/-- The native strict henselization at a geometric point of a regular scheme is regular. -/
theorem isRegular_strictHenselization_of_isRegular (hreg : IsRegular S) :
    IsRegular (strictHenselization B S hS s) :=
  (isRegular_spec_iff _).mpr (isRegularRing_etaleLocalRing_of_isRegular B S hS s hreg)

/-- The original affine strict-local scheme is Noetherian, not merely locally Noetherian. -/
theorem isNoetherian_strictHenselization_of_isRegular (hreg : IsRegular S) :
    IsNoetherian (strictHenselization B S hS s) := by
  have := isRegularRing_etaleLocalRing_of_isRegular B S hS s hreg
  infer_instance

/-- The original strict-local scheme is integral because its actual regular local ring is a
nonzero domain. No component or replacement spectrum is selected. -/
theorem isIntegral_strictHenselization_of_isRegular (hreg : IsRegular S) :
    IsIntegral (strictHenselization B S hS s) := by
  have := isRegularLocalRing_etaleLocalRing_of_isRegular B S hS s hreg
  have : IsDomain ↥(etaleLocalRing B S hS s) := IsRegularLocalRing.isDomain _
  infer_instance

end AlgebraicGeometry
