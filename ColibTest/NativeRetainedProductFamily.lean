/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedProductFamily

/-! Literal paired-map scope checks. These sources are UNCOMPILED. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialSectionPencil

universe u

variable {R : Type u} [CommRing R] {S X V : Scheme.{u}}
  (t : S ⟶ Spec (.of R)) [IsSeparated t] (q : X ⟶ S) (r : V ⟶ S)
  (L : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L] (a c : Γ(L, ⊤))

example : IsClosedImmersion (retainedAmbientPair t q r) := inferInstance

example : IsClosedImmersion (retainedFamilyPair t q r L a c) := inferInstance

example : retainedFamilyPair t q r L a c ≫ pullback.fst _ _ =
    familySource (q ≫ t) (pullback.fst q r) L a c :=
  retainedFamilyPair_fst t q r L a c

example : retainedFamilyPair t q r L a c ≫ pullback.snd _ _ =
    retainedFamilyTarget t q r L a c := retainedFamilyPair_snd t q r L a c

example [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)] :
    IsClosedImmersion (nativeRetainedFamilyPair t q r L a c) := inferInstance

#check parameterMap_isPullback
#check retainedParameterIso
#check retainedFamilyPair_eq_lift
#check nativeRetainedFamilyPair_fst
#check nativeRetainedFamilyPair_snd
#check nativeSection_parameterIso
