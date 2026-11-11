/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.KTheory.Bass.NaturalTrack

open CategoryTheory Topology Topology.LoopPrespectrum KTheory.Bass
open scoped Topology unitInterval
noncomputable section
universe u v w

namespace ColibTest.NaturalTrackClosure
open KTheory.Bass.NaturalTrack
variable {C : Type u} [Category.{v} C] {L : C ⥤ C} {c : 𝟭 C ⟶ L}
  {F G K : C ⥤ LoopPrespectrum.{w}}
variable (Q : C ⥤ Arrow (Arrow C))
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

example (A : Track L c F) : Equivariant A A (𝟙 F) := by
  apply KTheory.Bass.NaturalTrack.Equivariant.id

example {A : Track L c F} {B : Track L c G} {D : Track L c K}
    {η : F ⟶ G} {θ : G ⟶ K} (hη : Equivariant A B η) (hθ : Equivariant B D θ) :
    Equivariant A D (η ≫ θ) := by
  apply KTheory.Bass.NaturalTrack.Equivariant.comp
  all_goals assumption

example (A : Track L c F) (h : F = G) :
    Equivariant A (A.cast h) (eqToHom h) := by
  apply KTheory.Bass.NaturalTrack.Equivariant.cast_target

example (B : Track L c G) (h : F = G) :
    Equivariant (B.cast h.symm) B (eqToHom h) := by
  apply KTheory.Bass.NaturalTrack.Equivariant.cast_source

example {A : Track L c F} {B : Track L c G} {η : F ⟶ G}
    (hη : Equivariant A B η) :
    Equivariant (A.cone Q χ hχ) (B.cone Q χ hχ) (ConeTrack.map Q η) := by
  apply KTheory.Bass.NaturalTrack.Equivariant.cone
  all_goals assumption

example {A : Track L c F} {B : Track L c G} {η : F ⟶ G}
    (hη : Equivariant A B η) :
    Equivariant A.loop B.loop (Functor.whiskerRight η parameterLoopingFunctor) := by
  apply KTheory.Bass.NaturalTrack.Equivariant.loop
  all_goals assumption

example {A : Track L c F} {B : Track L c G} {η : F ⟶ G}
    (hη : Equivariant A B η) :
    Equivariant (A.bass Q χ hχ) (B.bass Q χ hχ) ((strictDiagramFunctor Q).map η) := by
  apply KTheory.Bass.NaturalTrack.Equivariant.bass
  all_goals assumption

example (A : Track L c F) (X : C) (n : ℕ) (t : unitInterval)
    (γ : (parameterLooping (F.obj X)).space n) :
    (A.loop.homotopy X).level n (t, γ) =
      (A.homotopy X).parameterLooping.level n (t, γ) := rfl

example (A : Track L c F) :
    A.bass Q χ hχ = (A.cone Q χ hχ).loop := rfl

example (A : Track L c F) (X : C) :
    ((A.cone Q χ hχ).homotopy X) =
      ConeTrack.action Q L c χ hχ F A.homotopy A.naturality X := rfl

end ColibTest.NaturalTrackClosure

namespace ColibTest.NaturalTrackLoopStrength
open KTheory.Bass.LoopStrength
variable {C : Type u} [Category.{v} C]
variable {E F : C ⥤ LoopPrespectrum.{w}}
    (H : ∀ X, Homotopy (zeroHom (E.obj X) (F.obj X))
      (zeroHom (E.obj X) (F.obj X)))
    (hH : ∀ {X Y} (f : X ⟶ Y) n r x,
      (F.map f).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (E.map f).map n x))

example (Q : C ⥤ Arrow (Arrow C)) (X : C) (n : ℕ)
    (r : unitInterval) (x : (((strictDiagramFunctor Q).obj E).obj X).space n) :
    (bassHomotopy H hH Q X).level n (r, x) =
      (((strictDiagramFunctor Q).map (diagramHomotopyAt
        (η := diagramZeroMap E F) (θ := diagramZeroMap E F) H hH r)).app X).map n x :=
  KTheory.Bass.LoopStrength.bassHomotopy_apply H hH Q X n r x

example (r : unitInterval) :
    loopMap H hH ≫ diagramHomotopyAt
      (η := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (θ := diagramZeroMap (F ⋙ parameterLoopingFunctor) F)
      (evaluation F) (evaluation_naturality F) r =
      diagramHomotopyAt (η := diagramZeroMap E F) (θ := diagramZeroMap E F) H hH r :=
  KTheory.Bass.LoopStrength.loopMap_evaluation H hH r

example (Q : C ⥤ Arrow (Arrow C)) (X : C) :
    (((strictDiagramFunctor Q).map (loopMap H hH)).app X) ≫ strength Q F X =
      (bassHomotopy H hH Q X).zeroLoopMap :=
  KTheory.Bass.LoopStrength.strength_square H hH Q X

end ColibTest.NaturalTrackLoopStrength

namespace ColibTest.NaturalTrackCone
open KTheory.Bass.LoopConeTrack KTheory.Bass.ConeTrack
variable {C : Type u} [Category.{v} C]
variable (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
    (F : C ⥤ LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (c.app X)) (F.map (c.app X)))
    (hH : ∀ {X Y} (g : X ⟶ Y) n r x,
      (F.map (L.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

example (r t : unitInterval) :
    evaluationAt F t ≫ diagramHomotopyAt
      (η := Functor.whiskerRight c F) (θ := Functor.whiskerRight c F) H hH r =
      diagramHomotopyAt
        (η := Functor.whiskerRight c (F ⋙ parameterLoopingFunctor))
        (θ := Functor.whiskerRight c (F ⋙ parameterLoopingFunctor))
        (fun X => (H X).parameterLooping)
        (loop_naturality L c F H hH) r ≫ Functor.whiskerLeft L (evaluationAt F t) :=
  KTheory.Bass.LoopConeTrack.evaluation_timeSlice L c F H hH r t

example (X : C) (r t : unitInterval) :
    (map Q (evaluationAt F t)).app X ≫ (action Q L c χ hχ F H hH X).at r =
      (action Q L c χ hχ (F ⋙ parameterLoopingFunctor)
        (fun Y => (H Y).parameterLooping) (loop_naturality L c F H hH) X).at r ≫
          (map Q (evaluationAt F t)).app (L.obj X) :=
  KTheory.Bass.LoopConeTrack.action_evaluation Q L c χ hχ F H hH X r t

end ColibTest.NaturalTrackCone

namespace ColibTest.NaturalTrackTranspose
open Topology.LoopPrespectrum.LoopTranspose
example (E : LoopPrespectrum.{u}) (n : ℕ)
    (γ : Path (Path.refl (E.point n)) (Path.refl (E.point n))) (s t : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((transpose E).map n γ) s) t = γ t s := by
  apply Topology.LoopPrespectrum.LoopTranspose.transpose_apply

example {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    parameterLoopingMap (parameterLoopingMap f) ≫ transpose F =
      transpose E ≫ parameterLoopingMap (parameterLoopingMap f) := by
  apply Topology.LoopPrespectrum.LoopTranspose.naturality

end ColibTest.NaturalTrackTranspose
