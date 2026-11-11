/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.FiniteTwistedRotation

/-! # Replacing the last finite cone word by an equal actual word -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.FiniteTwistedTail
open IteratedLoopStrength FiniteLoopWords AssociatedStrength
open FiniteLoopWordSlide FiniteTwistedRotation
variable {C : Type u} [Category.{v} C]

/-- A specified finite tail equal to the geometric permutation and cone word retains the square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteTwistedTail.lean:24"
  "adaptation" "Original finite seed rotation with full casts and fixed order."]
theorem finite_twisted_rotation_of_tail (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (a : F ⟶ (strictDiagramFunctor Q).obj F)
    (b : ConeTrack.diagram Q F ⟶
      (strictDiagramFunctor Q).obj (ConeTrack.diagram Q F))
    (p : ConeTrack.diagram Q (ConeTrack.diagram Q F) ⟶
      ConeTrack.diagram Q (ConeTrack.diagram Q F))
    (q : ConeTrack.diagram Q F ⟶ ConeTrack.diagram Q F)
    (r : ConeTrack.diagram Q (ConeTrack.diagram Q F) ⟶
      ConeTrack.diagram Q (ConeTrack.diagram Q F))
    (h : (strictDiagramFunctor Q).map a ≫ strengthDiagram Q (ConeTrack.diagram Q F) =
      Functor.whiskerRight b parameterLoopingFunctor ≫
        (transposeIso (ConeTrack.diagram Q (ConeTrack.diagram Q F))).inv ≫
        loopMap 2 p)
    (hword : p ≫ ConeTrack.map Q q = r) :
    (strictDiagramFunctor Q).map
        (loopInto i a ≫ (cyclicIso i (ConeTrack.diagram Q F)).hom ≫
          loopMap (i + 1) q) ≫
        associatedStrength Q (i + 1) (ConeTrack.diagram Q F) =
      associatedStrength Q i F ≫ loopInto (i + 1)
        (A := ConeTrack.diagram Q F)
        (B := ConeTrack.diagram Q (ConeTrack.diagram Q F)) b ≫
        (cyclicIso (i + 1)
          (ConeTrack.diagram Q (ConeTrack.diagram Q F))).hom ≫
        loopMap (i + 2) r := by
  have hf := finite_twisted_rotation Q i F a b p q h
  rw [hword] at hf
  exact hf

end KTheory.Bass.FiniteTwistedTail
