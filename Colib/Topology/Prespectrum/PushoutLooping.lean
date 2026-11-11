/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.HomotopyPushout
public import Colib.Topology.Prespectrum.LoopTranspose
public import Colib.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# Reconstructed pushout-loop comparison prototype

The actual homotopy pushout descends the looped inclusions and the original whole glue.
This adopted reconstructed source is not historical byte recovery.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout.Looping
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- The original overlap homotopy applied pointwise to actual loops. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLooping.lean:30"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def loopGlue : Homotopy
    (parameterLoopingMap f ≫ parameterLoopingMap (inl f g))
    (parameterLoopingMap g ≫ parameterLoopingMap (inr f g)) :=
  (glue f g).parameterLooping.cast
    (parameterLoopingFunctor.map_comp f (inl f g))
    (parameterLoopingFunctor.map_comp g (inr f g))

/-- The actual pushout-to-looped-pushout map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLooping.lean:38"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def comparison : prespectrum (parameterLoopingMap f) (parameterLoopingMap g) ⟶
    parameterLooping (prespectrum f g) :=
  desc _ _ (parameterLoopingMap (inl f g)) (parameterLoopingMap (inr f g))
    (loopGlue f g)

/-- The left summand is the original looped inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLooping.lean:44"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem comparison_left :
    inl (parameterLoopingMap f) (parameterLoopingMap g) ≫ comparison f g =
      parameterLoopingMap (inl f g) := by
  exact inl_desc _ _ _ _ _

/-- The right summand is the original looped inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLooping.lean:50"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem comparison_right :
    inr (parameterLoopingMap f) (parameterLoopingMap g) ≫ comparison f g =
      parameterLoopingMap (inr f g) := by
  exact inr_desc _ _ _ _ _

/-- The complete overlap retains its cylinder height independently of loop time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLooping.lean:56"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem comparison_cylinder (n : ℕ) (s t : unitInterval)
    (γ : Path (A.point n) (A.point n)) :
    Path.toContinuousMap ((comparison f g).map n
        (cylinder (parameterLoopingMap f) (parameterLoopingMap g) n (s, γ))) t =
      cylinder f g n (s, γ t) := rfl

variable {A' B' C' : LoopPrespectrum.{u}}
    (f' : A' ⟶ B') (g' : A' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (hf : f ≫ b = a ≫ f') (hg : g ≫ c = a ≫ g')

/-- Loop all three legs of an original strict span map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLooping.lean:68"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
def loopSpanMap :
    prespectrum (parameterLoopingMap f) (parameterLoopingMap g) ⟶
      prespectrum (parameterLoopingMap f') (parameterLoopingMap g') :=
  map _ _ _ _ (parameterLoopingMap a) (parameterLoopingMap b) (parameterLoopingMap c)
    ((parameterLoopingFunctor.map_comp f b).symm.trans
      ((congrArg parameterLoopingFunctor.map hf).trans
        (parameterLoopingFunctor.map_comp a f')))
    ((parameterLoopingFunctor.map_comp g c).symm.trans
      ((congrArg parameterLoopingFunctor.map hg).trans
        (parameterLoopingFunctor.map_comp a g')))

/-- The comparison is natural on the two charts and the entire original overlap. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLooping.lean:80"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem comparison_naturality :
    loopSpanMap f g f' g' a b c hf hg ≫ comparison f' g' =
      comparison f g ≫ parameterLoopingMap (map f g f' g' a b c hf hg) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext t
  induction z using Quot.inductionOn with
  | h z =>
    cases z with
    | inl z => cases z <;> rfl
    | inr z => rfl

end Topology.LoopPrespectrum.HomotopyPushout.Looping
