/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.StrictDiagram

/-!
# Original map components of the strict Bass endofunctor

The component formula exposes the unchanged four-corner square map before applying the
actual cone-loop functor. Applying finite iterates to a proved seed square preserves it.
-/
/-! Implementation provenance: `Quillen/KTheory/Bass/StrictDiagramMap.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C]

/-- Each actual Bass map is the original cone-loop map of the original four component arrows. -/
theorem strictDiagramFunctor_map_app (Q : C ⥤ Arrow (Arrow C))
    {F G : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G) (X : C) :
    ((strictDiagramFunctor Q).map a).app X =
      LoopPrespectrum.strictSquareLoopedConeFunctor.map
        (((Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum.{w})).map
          ((Functor.mapArrowFunctor C LoopPrespectrum.{w}).map a)).app (Q.obj X)) := rfl

/-- Every iterated original seed square is obtained by applying the same actual Bass functor. -/
theorem strictDiagramTransition_map
    (Q : C ⥤ Arrow (Arrow C)) {F G : C ⥤ LoopPrespectrum.{w}}
    (σ : F ⟶ (strictDiagramFunctor Q).obj F) (τ : G ⟶ (strictDiagramFunctor Q).obj G)
    (a : F ⟶ G) (h : σ ≫ (strictDiagramFunctor Q).map a = a ≫ τ) (n : ℕ) :
    strictDiagramTransition Q σ n ≫ (strictDiagramIterate Q (n + 1)).map a =
      (strictDiagramIterate Q n).map a ≫ strictDiagramTransition Q τ n := by
  change (strictDiagramIterate Q n).map σ ≫
    (strictDiagramIterate Q n).map ((strictDiagramFunctor Q).map a) =
      (strictDiagramIterate Q n).map a ≫ (strictDiagramIterate Q n).map τ
  rw [← Functor.map_comp, h, Functor.map_comp]

end KTheory.Bass

attribute [colib_tag "COL-0338",
  colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagramMap.lean" "adaptation"
    "Actual strict-square cylinder, cone-loop maps and supplied-seed finite iteration"]
  KTheory.Bass.strictDiagramTransition_map
