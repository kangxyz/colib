/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.OpenBaseChangePlus
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.Basic

/-! # The bounded-below flat and self-base-change maps for projective space -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedBaseChangePlus

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard

local instance {S T : Scheme.{u}} (g : T ⟶ S) [Flat g] :
    PreservesFiniteLimits (Scheme.Modules.pullback g) :=
  Stacks.AlgebraicGeometry.FlatBaseChangeDerived.preservesFiniteLimits_pullback g

/-- The actual bounded-below mate for a flat cartesian square. -/
@[expose] def flatSquareBaseChangePlus {X X' S T : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
    (h : IsPullback a b f g) :=
  letI : Flat a := MorphismProperty.of_isPullback h.flip inferInstance
  derivedBaseChangePlus (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward b)
    (Scheme.Modules.pullback g) (Scheme.Modules.pullback a)
    (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans h.w)

/-- The native flat base-change mate for the projective line. -/
@[expose] def projectiveLineFlatBaseChangePlus {S T : Scheme.{u}} (g : T ⟶ S)
    [Flat g] :=
  flatSquareBaseChangePlus (isPullback_projectiveSpaceOverMap 1 g)

/-- The original projective-line self-square, with the two distinct projections. -/
@[expose] def lineSelfBaseChangePlus (R : CommRingCat.{u}) :=
  let f := projectiveSpaceOver 1 (Spec R) ↘ Spec R
  flatSquareBaseChangePlus (IsPullback.of_hasPullback f f)

/-- The self-square map is characterized by the underived mate and both derived units. -/
theorem lineSelfBaseChangePlus_unit (R : CommRingCat.{u})
    (K : HomotopyCategory.Plus (projectiveSpaceOver 1 (Spec R)).Modules) :
    let f := projectiveSpaceOver 1 (Spec R) ↘ Spec R
    letI : Flat (pullback.fst f f) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback f f).flip inferInstance
    (Scheme.Modules.pullback f).mapDerivedCategoryPlus.map
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnith.app K) ≫
      (lineSelfBaseChangePlus R).app (DerivedCategory.Plus.Qh.obj K) =
    (derivedBaseChangePlusAux (Scheme.Modules.pushforward f)
      (Scheme.Modules.pushforward (pullback.snd f f))
      (Scheme.Modules.pullback f) (Scheme.Modules.pullback (pullback.fst f f))
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        (IsPullback.of_hasPullback f f).w)).app K :=
  derivedBaseChangePlus_fac _ _ _ _ _ K

end AlgebraicGeometry.projectiveSpaceOver
