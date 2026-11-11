/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.NaturalTrack

/-!
# Two original cone actions at one unchanged time

This computes the existing cone action twice as the original double cone map
of the given time slice, followed by the two existing inverse index maps.
All square hypotheses are those already needed to define that action.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u v w
namespace KTheory.Bass.ConeTrackDoubleTime
open ConeTrack NaturalTrack LoopConeTrack
variable {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
    {F : C ⥤ LoopPrespectrum.{w}} (A : Track L c F)

/-- The existing cone action is the original mapped time slice followed by its index map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrackDoubleTime.lean:35"
  "adaptation" "Original same-time double action and actual whole permutation equivariance."]
theorem cone_timeSlice (r : unitInterval) :
    diagramHomotopyAt
      (η := Functor.whiskerRight c (diagram Q F))
      (θ := Functor.whiskerRight c (diagram Q F))
      (A.cone Q χ hχ).homotopy (A.cone Q χ hχ).naturality r =
    map Q (diagramHomotopyAt
      (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F)
      A.homotopy A.naturality r) ≫ indexMap Q L χ F := by
  apply NatTrans.ext
  funext X
  exact action_at Q L c χ hχ F A.homotopy A.naturality X r

/-- Two existing cone actions retain the original two inverse index maps in order. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/ConeTrackDoubleTime.lean:48"
  "adaptation" "Original same-time double action and actual whole permutation equivariance."]
theorem doubleCone_action_at (X : C) (r : unitInterval) :
    (((A.cone Q χ hχ).cone Q χ hχ).homotopy X).at r =
      (map Q (map Q (diagramHomotopyAt
        (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F)
        A.homotopy A.naturality r)) ≫
          (map Q (indexMap Q L χ F) ≫ indexMap Q L χ (diagram Q F))).app X := by
  change (action Q L c χ hχ (diagram Q F)
    (A.cone Q χ hχ).homotopy (A.cone Q χ hχ).naturality X).at r = _
  rw [action_at, cone_timeSlice, coneMap_comp, Category.assoc]

end KTheory.Bass.ConeTrackDoubleTime
