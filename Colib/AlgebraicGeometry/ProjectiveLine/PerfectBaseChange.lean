/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.PerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange

/-! # Derived base change for perfect objects on the projective line

The actual base-change morphism is invertible for a perfect input, including
nonflat changes of base, by the proper flat theorem (Stacks, Tag 0B91).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard

/-- The canonical derived base-change map for the projective-line projection
is an isomorphism at an intrinsic perfect object. -/
theorem isIso_projectiveLinePerfectBaseChange {S T : Scheme.{u}} (g : T ⟶ S)
    (E : DerivedCategory (projectiveSpaceOver 1 S).Modules)
    (hE : RingedSpace.IsPerfect (X := (projectiveSpaceOver 1 S).toRingedSpace) E) :
    IsIso (derivedBaseChangeMap (projectiveSpaceOverMap 1 g).toLRSHom.toShHom
      (projectiveSpaceOver 1 T ↘ T).toLRSHom.toShHom
      (projectiveSpaceOver 1 S ↘ S).toLRSHom.toShHom g.toLRSHom.toShHom
      (comp_toShHom_of_comm (isPullback_projectiveSpaceOverMap 1 g).w) E) := by
  let f := projectiveSpaceOver 1 S ↘ S
  have := locallyOfFiniteType_terminal_from_projectiveSpaceAtUniverse.{u} 1
  let : LocallyOfFinitePresentation f := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  have hf : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  exact (ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat
    f hf inferInstance inferInstance E hE).2 g (projectiveSpaceOver 1 T ↘ T)
      (projectiveSpaceOverMap 1 g) (isPullback_projectiveSpaceOverMap 1 g)

end AlgebraicGeometry.projectiveSpaceOver
