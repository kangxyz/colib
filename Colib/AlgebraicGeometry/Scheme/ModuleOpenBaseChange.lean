/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange

/-! # Base change of module direct images along open immersions -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.OpenBaseChange

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The pullback square of an open immersion is canonically the pullback of its range. -/
def openImmersionPullbackRangeIso {X Y V : Scheme.{u}} (f : X ⟶ Y) (j : V ⟶ Y)
    [IsOpenImmersion j] : Limits.pullback f j ≅ Limits.pullback f j.opensRange.ι := by
  let t := pullback.map f j f j.opensRange.ι (𝟙 X) j.isoOpensRange.hom (𝟙 Y)
    (by simp) (by simp)
  let : IsIso t := pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso t

theorem openImmersionPullbackRangeIso_fst {X Y V : Scheme.{u}} (f : X ⟶ Y) (j : V ⟶ Y)
    [IsOpenImmersion j] :
    (openImmersionPullbackRangeIso f j).hom ≫ pullback.fst f j.opensRange.ι = pullback.fst f j := by
  simp [openImmersionPullbackRangeIso]

theorem openImmersionPullbackRangeIso_snd {X Y V : Scheme.{u}} (f : X ⟶ Y) (j : V ⟶ Y)
    [IsOpenImmersion j] :
    (openImmersionPullbackRangeIso f j).hom ≫ pullback.snd f j.opensRange.ι =
      pullback.snd f j ≫ j.isoOpensRange.hom := by
  simp [openImmersionPullbackRangeIso]

/-- Base change along an open immersion, expressed in the actual pullback square. -/
def pushforwardOpenBaseChange {X Y V : Scheme.{u}} (f : X ⟶ Y) (j : V ⟶ Y)
    [IsOpenImmersion j] :
    pushforward f ⋙ restrictFunctor j ≅
      restrictFunctor (pullback.fst f j) ⋙ pushforward (pullback.snd f j) := by
  let W := j.opensRange
  let q := j.isoOpensRange
  let e := openImmersionPullbackRangeIso f j
  have hq : q.hom ≫ W.ι = j := j.isoOpensRange_hom_ι
  have h₁ : e.hom ≫ pullback.fst f W.ι = pullback.fst f j := openImmersionPullbackRangeIso_fst f j
  have h₂ : e.hom ≫ pullback.snd f W.ι = pullback.snd f j ≫ q.hom :=
    openImmersionPullbackRangeIso_snd f j
  have h₃ : pullback.snd f W.ι ≫ q.inv = e.inv ≫ pullback.snd f j := by
    rw [← cancel_epi e.hom, ← Category.assoc, h₂]
    simp
  calc
    pushforward f ⋙ restrictFunctor j ≅
        (pushforward f ⋙ restrictFunctor W.ι) ⋙ restrictFunctor q.hom :=
      Functor.isoWhiskerLeft _ (restrictFunctorCongr hq.symm ≪≫
        restrictFunctorComp q.hom W.ι) ≪≫ (Functor.associator _ _ _).symm
    _ ≅ (restrictFunctor (pullback.fst f W.ι) ⋙ pushforward (pullback.snd f W.ι)) ⋙
        restrictFunctor q.hom := Functor.isoWhiskerRight (restrictPushforwardIsoPullback f W) _
    _ ≅ restrictFunctor (pullback.fst f W.ι) ⋙ pushforward (pullback.snd f W.ι ≫ q.inv) :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (restrictFunctorIsoPushforwardInv q) ≪≫
        pushforwardComp _ _)
    _ ≅ restrictFunctor (pullback.fst f W.ι) ⋙
        (restrictFunctor e.hom ⋙ pushforward (pullback.snd f j)) :=
      Functor.isoWhiskerLeft _ (pushforwardCongr h₃ ≪≫ (pushforwardComp _ _).symm ≪≫
        Functor.isoWhiskerRight (restrictFunctorIsoPushforwardInv e).symm _)
    _ ≅ restrictFunctor (pullback.fst f j) ⋙ pushforward (pullback.snd f j) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((restrictFunctorComp e.hom _).symm ≪≫
        restrictFunctorCongr h₁) _

end AlgebraicGeometry.Scheme.Modules
