/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.StrictDiagram

/-!
# Change of index for the original strict Bass functor

An actual isomorphism of the four-corner index diagrams induces an isomorphism
between restriction of the original Bass functor and Bass of the restricted diagram.
The prescribed forward index isomorphism acts on the entire original cone and loop.
Naturality holds for every spectrum diagram transformation. No seed or higher
coherence condition is used in this construction.
-/
/-! Implementation provenance: `Quillen/KTheory/Bass/StrictDiagramIndexChange.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u₁ v₁ u₂ v₂ w
namespace KTheory.Bass.StrictDiagramIndexChange
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)

/-- Restrict an actual prespectrum diagram along the specified index functor. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexChange.lean:29"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def restriction : (D ⥤ LoopPrespectrum.{w}) ⥤ (C ⥤ LoopPrespectrum.{w}) :=
  (Functor.whiskeringLeft C D LoopPrespectrum).obj K

/-- The full source functor of the whiskered index isomorphism. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexChange.lean:33"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem source_eq (F : D ⥤ LoopPrespectrum.{w}) :
    K ⋙ (strictDiagramFunctor Q₂).obj F =
      (K ⋙ Q₂) ⋙ (F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor) := rfl

/-- The full target retains composition on both arrow levels and functor association. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexChange.lean:38"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem target_eq (F : D ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q₁).obj (K ⋙ F) =
      (Q₁ ⋙ K.mapArrow.mapArrow) ⋙
        (F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor) := rfl

/-- Apply the given forward index isomorphism to the original whole Bass construction. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexChange.lean:44"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def iso (F : D ⥤ LoopPrespectrum.{w}) :
    K ⋙ (strictDiagramFunctor Q₂).obj F ≅ (strictDiagramFunctor Q₁).obj (K ⋙ F) :=
  Functor.isoWhiskerRight α (F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor)

/-- The actual map uses the prescribed four-corner arrow, with its original orientation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexChange.lean:49"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem iso_hom_app (F : D ⥤ LoopPrespectrum.{w}) (X : C) :
    (iso K Q₁ Q₂ α F).hom.app X = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (α.hom.app X)) := rfl

/-- The inverse uses the specified inverse four-corner arrow. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexChange.lean:54"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem iso_inv_app (F : D ⥤ LoopPrespectrum.{w}) (X : C) :
    (iso K Q₁ Q₂ α F).inv.app X = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (α.inv.app X)) := rfl

/-- Index transport is natural in every complete prespectrum diagram map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexChange.lean:59"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem iso_naturality {F G : D ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    Functor.whiskerLeft K ((strictDiagramFunctor Q₂).map η) ≫ (iso K Q₁ Q₂ α G).hom =
      (iso K Q₁ Q₂ α F).hom ≫
        (strictDiagramFunctor Q₁).map (Functor.whiskerLeft K η) := by
  apply NatTrans.ext
  funext X
  let T := (Functor.mapArrowFunctor (Arrow D) (Arrow LoopPrespectrum.{w})).map
    ((Functor.mapArrowFunctor D LoopPrespectrum.{w}).map η)
  have h := congrArg strictSquareLoopedConeFunctor.map (T.naturality (α.hom.app X))
  simp only [Functor.map_comp] at h
  exact h.symm

/-- The actual Bass/index interchange is a natural isomorphism of diagram functors. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexChange.lean:72"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def functorIso :
    strictDiagramFunctor Q₂ ⋙ restriction K ≅ restriction K ⋙ strictDiagramFunctor Q₁ :=
  NatIso.ofComponents (iso K Q₁ Q₂ α) (fun η => iso_naturality K Q₁ Q₂ α η)

end KTheory.Bass.StrictDiagramIndexChange

