/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.DiagramNullTransport
public import Colib.KTheory.Bass.StrictDiagramHomotopy
public import Colib.KTheory.Bass.StrictDiagramSuccessorMap

/-!
# The original Bass action iterated on prescribed natural null tracks

Each successor uses exactly the existing Bass action and then the accepted equality-induced
right-successor maps. The original iteration objects, arrows and coefficient maps are retained.
Whole null values and cone descents record these actual transports, not merely endpoints.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G K : C ⥤ LoopPrespectrum.{w}} {a : F ⟶ G} {b : G ⟶ K}

/-- The existing whole Bass null action, bundled with its literal coefficient naturality. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNull.lean:28"
  "adaptation" "Original successor transports and same-time iterated null."]
def strictDiagramNull (H : DiagramNullHomotopy a b) :
    DiagramNullHomotopy ((strictDiagramFunctor Q).map a) ((strictDiagramFunctor Q).map b) where
  homotopy X := strictDiagramNullHomotopy a b H.homotopy H.naturality Q X
  naturality f n r x := strictDiagramMapHomotopy_naturality
    (η := a ≫ b) (θ := diagramZeroMap F K) H.homotopy H.naturality Q f n r x

/-- Iterate the same prescribed null track on the unchanged original Bass iterate arrows. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNull.lean:35"
  "adaptation" "Original successor transports and same-time iterated null."]
def strictDiagramIterateNull (H : DiagramNullHomotopy a b) :
    (n : ℕ) → DiagramNullHomotopy ((strictDiagramIterate Q n).map a)
      ((strictDiagramIterate Q n).map b)
  | 0 => H
  | n + 1 => (strictDiagramNull Q (strictDiagramIterateNull H n)).transport
      (asIso (strictDiagramSuccessorMap Q F n))
      (asIso (strictDiagramSuccessorMap Q G n))
      (asIso (strictDiagramSuccessorMap Q K n))
      (strictDiagramSuccessorMap_naturality Q a n)
      (strictDiagramSuccessorMap_naturality Q b n)

/-- The stage-zero null track is the original supplied whole track. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNull.lean:47"
  "adaptation" "Original successor transports and same-time iterated null."]
theorem strictDiagramIterateNull_zero (H : DiagramNullHomotopy a b) :
    strictDiagramIterateNull Q H 0 = H := rfl

/-- The successor retains the actual equality-induced point maps and the identical null time. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNull.lean:51"
  "adaptation" "Original successor transports and same-time iterated null."]
theorem strictDiagramIterateNull_succ_level (H : DiagramNullHomotopy a b) (n : ℕ)
    (X : C) (m : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q (n + 1)).obj F).obj X).space m) :
    ((strictDiagramIterateNull Q H (n + 1)).homotopy X).level m (r, x) =
      ((inv (strictDiagramSuccessorMap Q K n)).app X).map m
        ((strictDiagramNullHomotopy ((strictDiagramIterate Q n).map a)
          ((strictDiagramIterate Q n).map b) (strictDiagramIterateNull Q H n).homotopy
          (strictDiagramIterateNull Q H n).naturality Q X).level m
            (r, ((strictDiagramSuccessorMap Q F n).app X).map m x)) := rfl

/-- The actual cone isomorphism induced by the original successor square of the original arrow. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNull.lean:62"
  "adaptation" "Original successor transports and same-time iterated null."]
def strictDiagramSuccessorConeIso (n : ℕ) (X : C) :
    mappingCone (((strictDiagramIterate Q (n + 1)).map a).app X) ≅
      mappingCone (((strictDiagramFunctor Q).map ((strictDiagramIterate Q n).map a)).app X) :=
  DiagramNullHomotopy.coneTransportIso (asIso (strictDiagramSuccessorMap Q F n))
    (asIso (strictDiagramSuccessorMap Q G n)) (strictDiagramSuccessorMap_naturality Q a n) X

/-- The successor's original cone descent is transported through those same actual isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIterateNull.lean:69"
  "adaptation" "Original successor transports and same-time iterated null."]
theorem strictDiagramIterateNull_succ_coneDesc (H : DiagramNullHomotopy a b) (n : ℕ) (X : C) :
    mappingConeDesc (((strictDiagramIterate Q (n + 1)).map a).app X)
        (((strictDiagramIterate Q (n + 1)).map b).app X)
        ((strictDiagramIterateNull Q H (n + 1)).homotopy X) =
      (strictDiagramSuccessorConeIso Q (a := a) n X).hom ≫
        mappingConeDesc (((strictDiagramFunctor Q).map ((strictDiagramIterate Q n).map a)).app X)
          (((strictDiagramFunctor Q).map ((strictDiagramIterate Q n).map b)).app X)
          (strictDiagramNullHomotopy ((strictDiagramIterate Q n).map a)
            ((strictDiagramIterate Q n).map b) (strictDiagramIterateNull Q H n).homotopy
            (strictDiagramIterateNull Q H n).naturality Q X) ≫
          (inv (strictDiagramSuccessorMap Q K n)).app X :=
  (strictDiagramNull Q (strictDiagramIterateNull Q H n)).transport_coneDesc
    (asIso (strictDiagramSuccessorMap Q F n)) (asIso (strictDiagramSuccessorMap Q G n))
    (asIso (strictDiagramSuccessorMap Q K n))
    (strictDiagramSuccessorMap_naturality Q a n) (strictDiagramSuccessorMap_naturality Q b n) X

end KTheory.Bass
