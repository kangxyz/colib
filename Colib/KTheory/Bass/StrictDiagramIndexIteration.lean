/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.StrictDiagramIndexChange

/-!
# Finite original Bass iterates under a change of index

The fixed recursion follows the library's original left-iterated Bass functor.
Its natural isomorphisms retain all original stage maps. A single original
seed square implies compatibility with every actual iterated seed transition;
no compatibility of additional seeds or higher comparison choices is assumed.
-/
/-! Implementation provenance: `Quillen/KTheory/Bass/StrictDiagramIndexIteration.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u₁ v₁ u₂ v₂ w
namespace KTheory.Bass.StrictDiagramIndexChange
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)

/-- Fixed finite index transports for the unchanged original Bass iteration. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexIteration.lean:28"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def iterateIso : ∀ (i : ℕ) (F : D ⥤ LoopPrespectrum.{w}),
    K ⋙ (strictDiagramIterate Q₂ i).obj F ≅ (strictDiagramIterate Q₁ i).obj (K ⋙ F)
  | 0, F => Iso.refl (K ⋙ F)
  | i + 1, F => iterateIso i ((strictDiagramFunctor Q₂).obj F) ≪≫
      (strictDiagramIterate Q₁ i).mapIso (iso K Q₁ Q₂ α F)

/-- Stage zero keeps the original restricted diagram literally. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexIteration.lean:35"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem iterateIso_zero (F : D ⥤ LoopPrespectrum.{w}) :
    iterateIso K Q₁ Q₂ α 0 F = Iso.refl (K ⋙ F) := rfl

/-- The successor is the fixed word matching the original left recursion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexIteration.lean:39"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem iterateIso_succ_hom (i : ℕ) (F : D ⥤ LoopPrespectrum.{w}) :
    (iterateIso K Q₁ Q₂ α (i + 1) F).hom =
      (iterateIso K Q₁ Q₂ α i ((strictDiagramFunctor Q₂).obj F)).hom ≫
        (strictDiagramIterate Q₁ i).map (iso K Q₁ Q₂ α F).hom := rfl

/-- Every finite whole index transport is natural in every diagram arrow. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexIteration.lean:45"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem iterateIso_naturality (i : ℕ) {F G : D ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    Functor.whiskerLeft K ((strictDiagramIterate Q₂ i).map η) ≫
        (iterateIso K Q₁ Q₂ α i G).hom =
      (iterateIso K Q₁ Q₂ α i F).hom ≫
        (strictDiagramIterate Q₁ i).map (Functor.whiskerLeft K η) := by
  induction i generalizing F G with
  | zero => rfl
  | succ i ih =>
    change Functor.whiskerLeft K
        ((strictDiagramIterate Q₂ i).map ((strictDiagramFunctor Q₂).map η)) ≫
        ((iterateIso K Q₁ Q₂ α i ((strictDiagramFunctor Q₂).obj G)).hom ≫
          (strictDiagramIterate Q₁ i).map (iso K Q₁ Q₂ α G).hom) =
      ((iterateIso K Q₁ Q₂ α i ((strictDiagramFunctor Q₂).obj F)).hom ≫
          (strictDiagramIterate Q₁ i).map (iso K Q₁ Q₂ α F).hom) ≫
        (strictDiagramIterate Q₁ i).map
          ((strictDiagramFunctor Q₁).map (Functor.whiskerLeft K η))
    rw [← Category.assoc, ih, Category.assoc, ← Functor.map_comp,
      iso_naturality, Functor.map_comp, ← Category.assoc]

/-- Finite index change is an actual natural isomorphism of entire diagram functors. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexIteration.lean:65"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def iterateFunctorIso (i : ℕ) :
    strictDiagramIterate Q₂ i ⋙ restriction K ≅
      restriction K ⋙ strictDiagramIterate Q₁ i :=
  NatIso.ofComponents (iterateIso K Q₁ Q₂ α i)
    (fun η => iterateIso_naturality K Q₁ Q₂ α i η)

variable {F : D ⥤ LoopPrespectrum.{w}}
    (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
    (η₁ : K ⋙ F ⟶ (strictDiagramFunctor Q₁).obj (K ⋙ F))
    (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom = η₁)

include hseed in
/-- The one given original seed square implies every unchanged iterated transition square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexIteration.lean:78"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem transition_square (i : ℕ) :
    Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i) ≫
        (iterateIso K Q₁ Q₂ α (i + 1) F).hom =
      (iterateIso K Q₁ Q₂ α i F).hom ≫ strictDiagramTransition Q₁ η₁ i := by
  change Functor.whiskerLeft K ((strictDiagramIterate Q₂ i).map η₂) ≫
      ((iterateIso K Q₁ Q₂ α i ((strictDiagramFunctor Q₂).obj F)).hom ≫
        (strictDiagramIterate Q₁ i).map (iso K Q₁ Q₂ α F).hom) =
    (iterateIso K Q₁ Q₂ α i F).hom ≫ (strictDiagramIterate Q₁ i).map η₁
  rw [← Category.assoc, iterateIso_naturality, Category.assoc,
    ← Functor.map_comp, hseed]

include hseed in
/-- The specified inverse stage maps preserve the same original transitions. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexIteration.lean:91"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem inverse_transition_square (i : ℕ) :
    (iterateIso K Q₁ Q₂ α i F).inv ≫
        Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i) =
      strictDiagramTransition Q₁ η₁ i ≫ (iterateIso K Q₁ Q₂ α (i + 1) F).inv := by
  apply (cancel_mono (iterateIso K Q₁ Q₂ α (i + 1) F).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [transition_square K Q₁ Q₂ α η₂ η₁ hseed i, Iso.inv_hom_id_assoc]

end KTheory.Bass.StrictDiagramIndexChange

