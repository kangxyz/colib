/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectGlobalUnitKOne

/-! Regressions for the actual global-unit automorphism, its fine class and canonical K-map. -/

noncomputable section
open CategoryTheory Waldhausen AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (q : (Γ(X, ⊤))ˣ)
  (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))

-- The fine class is literally the existing automorphism class, not a restricted coarse class.
example : perfectGlobalUnitKOneClass X q K =
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).automorphismKOneClass
      ((perfectGlobalUnitIso X q).app K) := rfl

-- Both scalar directions are the actual sheaf action in every complex degree.
example (n : ℤ) : (((perfectGlobalUnitIso X q).hom.app K).hom).f n =
    (Stacks.RegularSequence.globalSmulCenter X (q : Γ(X, ⊤))).app (K.obj.X n) := rfl

example : (perfectGlobalUnitIso X q⁻¹).app K =
    ((perfectGlobalUnitIso X q).app K).symm := perfectGlobalUnitIso_app_inv X q K

example : perfectGlobalUnitKOneClass X q⁻¹ K = (perfectGlobalUnitKOneClass X q K)⁻¹ :=
  perfectGlobalUnitKOneClass_inv X q K

example {L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (e : K ≅ L) : perfectGlobalUnitKOneClass X q K = perfectGlobalUnitKOneClass X q L :=
  perfectGlobalUnitKOneClass_iso X q e

example : KMap (perfectComplexesRestrictOpenImmersion_isExact j) 1
      (perfectGlobalUnitKOneClass X q K) =
    perfectGlobalUnitKOneClass U (Units.map j.appTop.hom.toMonoidHom q)
      ((perfectComplexesRestrictOpenImmersion j).obj K) :=
  perfectGlobalUnitKOneClass_restrict j q K

example : KMap (perfectComplexesRestrictOpenImmersion_isExact j) 1
      (perfectGlobalUnitKOneClass X q (rankOnePerfectComplex X)) =
    perfectGlobalUnitKOneClass U (Units.map j.appTop.hom.toMonoidHom q)
      (rankOnePerfectComplex U) := perfectGlobalUnitKOneClass_restrict_rankOne j q

-- The opens-only public K-map is retained, including its chosen-zero rebase.
example (V : X.Opens) :
    perfectComplexesRestrictKMap X V 1 (perfectGlobalUnitKOneClass X q K) =
      perfectGlobalUnitKOneClass V.toScheme (Units.map V.ι.appTop.hom.toMonoidHom q)
        ((perfectComplexesRestrictFunctor X V).obj K) :=
  perfectGlobalUnitKOneClass_restrict_opens X V q K
