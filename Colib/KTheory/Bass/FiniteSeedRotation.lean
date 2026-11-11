/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Bass.AssociatedStrength
public import Colib.Topology.Prespectrum.FiniteLoopInnerRotation

/-!
# Finite propagation of one original seed-rotation equation

The sole input is a local finite equation on `F` and its first unlooped cone. The
finite loop strength, loop rotation, and all association maps are the existing ones.
No tower compatibility or geometric identification is assumed as a field.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace KTheory.Bass.FiniteSeedRotation
open FiniteConeStrength IteratedLoopStrength
open FiniteLoopWords FiniteLoopStrengthWords NormalizedStageMap
open IteratedStrengthNaturality IteratedStrengthSuccessor
open AssociatedStrength FiniteLoopInnerRotation FiniteLoopWordSlide
variable {C : Type u} [Category.{v} C]

attribute [reassoc] iteratedStrength_naturality iteratedStrength_succ_inner
  iteratedStrength_cyclic loopMap_comp cyclicIso_succ_inner

/-- The fixed cyclic word is natural as the actual diagram map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteSeedRotation.lean:36"
  "adaptation" "Original finite seed rotation with full casts and fixed order.", reassoc]
theorem loopMap_cyclic_naturality (i : ℕ) {F G : C ⥤ LoopPrespectrum.{w}}
    (f : F ⟶ G) :
    loopMap (i + 1) f ≫ (cyclicIso i G).hom =
      (cyclicIso i F).hom ≫ loopMap (i + 1) f := (cyclic i).hom.naturality f

/-- Two innermost mapped loops retain both original association transports and the cyclic word. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteSeedRotation.lean:42"
  "adaptation" "Original finite seed rotation with full casts and fixed order.", reassoc]
theorem double_cyclic_naturality (i : ℕ) {F G : C ⥤ LoopPrespectrum.{w}}
    (f : F ⟶ G) :
    loopMap i (loopMap 2 f) ≫
        eqToHom (loopDiagram_postcomp i (G ⋙ parameterLoopingFunctor)) ≫
        (cyclicIso i (G ⋙ parameterLoopingFunctor)).hom ≫
        eqToHom (loopDiagram_postcomp (i + 1) G) =
      eqToHom (loopDiagram_postcomp i (F ⋙ parameterLoopingFunctor)) ≫
        (cyclicIso i (F ⋙ parameterLoopingFunctor)).hom ≫
        eqToHom (loopDiagram_postcomp (i + 1) F) ≫ loopMap (i + 2) f := by
  change loopMap i (Functor.whiskerRight
      (Functor.whiskerRight f parameterLoopingFunctor) parameterLoopingFunctor) ≫ _ = _
  rw [postcomp_naturality_assoc, loopMap_cyclic_naturality_assoc, postcomp_naturality]

/-- The last finite-loop algebra keeps the old input times separate from both new times. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteSeedRotation.lean:56"
  "adaptation" "Original finite seed rotation with full casts and fixed order."]
theorem loop_rotation_tail (i : ℕ) {F G : C ⥤ LoopPrespectrum.{w}}
    (b : F ⟶ G ⋙ parameterLoopingFunctor) (p : G ⟶ G) :
    loopMap i (Functor.whiskerRight b parameterLoopingFunctor) ≫
        loopMap i (transposeIso G).inv ≫ loopMap i (loopMap 2 p) ≫
        eqToHom (loopDiagram_postcomp i (G ⋙ parameterLoopingFunctor)) ≫
        (cyclicIso i (G ⋙ parameterLoopingFunctor)).hom ≫
        eqToHom (loopDiagram_postcomp (i + 1) G) =
      eqToHom (loopDiagram_postcomp i F) ≫ loopMap (i + 1) b ≫
        eqToHom (loopDiagram_postcomp (i + 1) G) ≫
        (cyclicIso (i + 1) G).hom ≫ loopMap (i + 2) p := by
  rw [double_cyclic_naturality, cyclicIso_succ_inner_assoc, postcomp_naturality_assoc]

/-- The fixed finite loops propagate exactly one seed-rotation equation on the original cone. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/FiniteSeedRotation.lean:69"
  "adaptation" "Original finite seed rotation with full casts and fixed order."]
theorem finite_seed_rotation (Q : C ⥤ Arrow (Arrow C)) (i : ℕ)
    (F : C ⥤ LoopPrespectrum.{w})
    (a : F ⟶ (strictDiagramFunctor Q).obj F)
    (b : ConeTrack.diagram Q F ⟶
      (strictDiagramFunctor Q).obj (ConeTrack.diagram Q F))
    (p : ConeTrack.diagram Q (ConeTrack.diagram Q F) ⟶
      ConeTrack.diagram Q (ConeTrack.diagram Q F))
    (h : (strictDiagramFunctor Q).map a ≫ strengthDiagram Q (ConeTrack.diagram Q F) =
      Functor.whiskerRight b parameterLoopingFunctor ≫
        (transposeIso (ConeTrack.diagram Q (ConeTrack.diagram Q F))).inv ≫
        loopMap 2 p) :
    (strictDiagramFunctor Q).map
        (loopInto i a ≫ (cyclicIso i (ConeTrack.diagram Q F)).hom) ≫
        associatedStrength Q (i + 1) (ConeTrack.diagram Q F) =
      associatedStrength Q i F ≫ loopInto (i + 1)
        (A := ConeTrack.diagram Q F)
        (B := ConeTrack.diagram Q (ConeTrack.diagram Q F)) b ≫
        (cyclicIso (i + 1)
          (ConeTrack.diagram Q (ConeTrack.diagram Q F))).hom ≫
        loopMap (i + 2) p := by
  simp only [loopInto_eq, associatedStrength, Functor.map_comp, Category.assoc]
  rw [iteratedStrength_cyclic_assoc, iteratedStrength_succ_inner_assoc,
    iteratedStrength_naturality_assoc, ← loopMap_comp_assoc, h]
  rw [loopMap_comp, loopMap_comp]
  simp only [Category.assoc]
  exact congrArg (fun k => iteratedStrength Q i F ≫ k)
    (loop_rotation_tail i
      (F := ConeTrack.diagram Q F)
      (G := ConeTrack.diagram Q (ConeTrack.diagram Q F)) b p)

end KTheory.Bass.FiniteSeedRotation
