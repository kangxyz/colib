/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.FiniteSeedRotation

/-! # One arbitrary finite cone word after the local seed rotation -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.FiniteTwistedRotation
open IteratedLoopStrength FiniteLoopWords AssociatedStrength
open FiniteLoopWordSlide FiniteSeedRotation
variable {C : Type u} [Category.{v} C]

private theorem append_functor_square {D : Type*} [Category* D] (B : D ⥤ D)
    {X Y Z : D} (f : X ⟶ Y) (q : Y ⟶ Y) (k : B.obj Y ⟶ Z)
    (g : B.obj X ⟶ Z) (m : Z ⟶ Z)
    (h : B.map f ≫ k = g) (hq : B.map q ≫ k = k ≫ m) :
    B.map (f ≫ q) ≫ k = g ≫ m := by
  rw [B.map_comp, Category.assoc, hq, ← Category.assoc, h]

/-- A final cone word is carried through the same finite strength by its proved naturality. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteTwistedRotation.lean:31"
  "adaptation" "Original finite seed rotation with full casts and fixed order."]
theorem finite_twisted_rotation (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (a : F ⟶ (strictDiagramFunctor Q).obj F)
    (b : ConeTrack.diagram Q F ⟶
      (strictDiagramFunctor Q).obj (ConeTrack.diagram Q F))
    (p : ConeTrack.diagram Q (ConeTrack.diagram Q F) ⟶
      ConeTrack.diagram Q (ConeTrack.diagram Q F))
    (q : ConeTrack.diagram Q F ⟶ ConeTrack.diagram Q F)
    (h : (strictDiagramFunctor Q).map a ≫ strengthDiagram Q (ConeTrack.diagram Q F) =
      Functor.whiskerRight b parameterLoopingFunctor ≫
        (transposeIso (ConeTrack.diagram Q (ConeTrack.diagram Q F))).inv ≫
        loopMap 2 p) :
    (strictDiagramFunctor Q).map
        (loopInto i a ≫ (cyclicIso i (ConeTrack.diagram Q F)).hom ≫
          loopMap (i + 1) q) ≫
        associatedStrength Q (i + 1) (ConeTrack.diagram Q F) =
      associatedStrength Q i F ≫ loopInto (i + 1)
        (A := ConeTrack.diagram Q F)
        (B := ConeTrack.diagram Q (ConeTrack.diagram Q F)) b ≫
        (cyclicIso (i + 1)
          (ConeTrack.diagram Q (ConeTrack.diagram Q F))).hom ≫
        loopMap (i + 2) (p ≫ ConeTrack.map Q q) := by
  have hf := append_functor_square (strictDiagramFunctor Q)
    (loopInto i (A := F) (B := ConeTrack.diagram Q F) a ≫
      (cyclicIso i (ConeTrack.diagram Q F)).hom)
    (loopMap (i + 1) q) (associatedStrength Q (i + 1) (ConeTrack.diagram Q F))
    _ (loopMap (i + 2) (ConeTrack.map Q q))
    (finite_seed_rotation Q i F a b p h) (associatedStrength_naturality Q (i + 1) q)
  simpa only [loopMap_comp, Category.assoc] using hf

end KTheory.Bass.FiniteTwistedRotation
