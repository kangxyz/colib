/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.PerfectBaseChange
public import Colib.AlgebraicGeometry.Scheme.OpenBaseChangePlus

/-! # The bounded-below open base-change mate for the projective line -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedBaseChangePlus

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard

private theorem pullback_open_preservesFiniteLimits {S T : Scheme.{u}}
    (g : T ⟶ S) [IsOpenImmersion g] : PreservesFiniteLimits (Scheme.Modules.pullback g) :=
  preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback g)

local instance {S T : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g] :
    PreservesFiniteLimits (Scheme.Modules.pullback g) := pullback_open_preservesFiniteLimits g

local instance {S T : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g] :
    IsOpenImmersion (projectiveSpaceOverMap 1 g) :=
  MorphismProperty.of_isPullback (isPullback_projectiveSpaceOverMap 1 g).flip inferInstance

/-- The actual bounded-below mate is induced by the underived pullback–pushforward mate. -/
def projectiveLineOpenBaseChangePlus {S T : Scheme.{u}} (g : T ⟶ S)
    [IsOpenImmersion g] :=
  Scheme.Modules.openSquareBaseChangePlus (isPullback_projectiveSpaceOverMap 1 g)

/-- Open base change is invertible at every bounded-below input, without any
perfectness or quasi-coherence premise. -/
theorem isIso_projectiveLineOpenBaseChangePlus_app {S T : Scheme.{u}}
    (g : T ⟶ S) [IsOpenImmersion g]
    (K : DerivedCategory.Plus (projectiveSpaceOver 1 S).Modules) :
    IsIso ((projectiveLineOpenBaseChangePlus g).app K) := by
  exact Scheme.Modules.isIso_openSquareBaseChangePlus_app (isPullback_projectiveSpaceOverMap 1 g) K

/-- The canonical open base-change isomorphism, natural in the input complex. -/
@[expose] def projectiveLineOpenBaseChangePlusIso {S T : Scheme.{u}}
    (g : T ⟶ S) [IsOpenImmersion g] :=
  Scheme.Modules.openSquareBaseChangePlusIso (isPullback_projectiveSpaceOverMap 1 g)

/-- The natural isomorphism keeps the actual mate on every input. -/
theorem projectiveLineOpenBaseChangePlusIso_hom_app {S T : Scheme.{u}}
    (g : T ⟶ S) [IsOpenImmersion g]
    (K : DerivedCategory.Plus (projectiveSpaceOver 1 S).Modules) :
    (projectiveLineOpenBaseChangePlusIso g).hom.app K =
      (projectiveLineOpenBaseChangePlus g).app K :=
  Scheme.Modules.openSquareBaseChangePlusIso_hom_app (isPullback_projectiveSpaceOverMap 1 g) K


/-- The actual comparison retains the native underived mate and the right
derived units. This characterizes its forward map on bounded-below complexes. -/
theorem projectiveLineOpenBaseChangePlusIso_unit {S T : Scheme.{u}}
    (g : T ⟶ S) [IsOpenImmersion g]
    (K : HomotopyCategory.Plus (projectiveSpaceOver 1 S).Modules) :
    (Scheme.Modules.pullback g).mapDerivedCategoryPlus.map
        ((Scheme.Modules.pushforward (projectiveSpaceOver 1 S ↘ S)).rightDerivedFunctorPlusUnith.app
          K) ≫
      (projectiveLineOpenBaseChangePlusIso g).hom.app (DerivedCategory.Plus.Qh.obj K) =
    (derivedBaseChangePlusAux (Scheme.Modules.pushforward (projectiveSpaceOver 1 S ↘ S))
      (Scheme.Modules.pushforward (projectiveSpaceOver 1 T ↘ T))
      (Scheme.Modules.pullback g) (Scheme.Modules.pullback (projectiveSpaceOverMap 1 g))
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
        (isPullback_projectiveSpaceOverMap 1 g).w)).app K := by
  exact Scheme.Modules.openSquareBaseChangePlusIso_unit (isPullback_projectiveSpaceOverMap 1 g) K

end AlgebraicGeometry.projectiveSpaceOver
