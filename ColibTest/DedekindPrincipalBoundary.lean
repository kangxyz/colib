/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.GTheory.Dedekind.PrincipalBoundaryComparison

open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

universe u
noncomputable section
variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  (p : IsDedekindDomain.HeightOneSpectrum R)
  {π : Localization.AtPrime p.asIdeal} (hπ : Irreducible π)

-- The original native consumer, with the actual scalar restrictions on both sides.
example (n : ℕ) :
    ((FGModuleCat.DedekindLocalDvr.principalResidueRestrictionExact R p hπ).smallKMap n).comp
      (FGModuleCat.Localization.closedConnectingHom π n) =
    (FGModuleCat.DedekindLocalDvr.localDvrBoundary R p n).comp
      ((FGModuleCat.DedekindLocalDvr.principalFractionRestrictionExact R p hπ).smallKMap
        (n + 1)) :=
  FGModuleCat.DedekindLocalDvr.principalBoundary_nativeBoundary R p hπ n
