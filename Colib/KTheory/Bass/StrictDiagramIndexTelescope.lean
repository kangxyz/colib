/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.StrictDiagramIndexIteration
public import Colib.Topology.Prespectrum.TelescopeDiagramMap
public import Colib.Topology.Prespectrum.StableEquivalence

/-!
# Actual telescope isomorphism under Bass index change

The forward and inverse finite index transports descend through the original
reduced telescope quotient using their proved strict transition squares. Their
composites are the identity on every original cylinder. Consequently the map is
an actual natural isomorphism and a stable equivalence without separation or
connectivity hypotheses. The only seed input is the original local seed square.
-/
/-! Implementation provenance: `Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u₁ v₁ u₂ v₂ w
namespace KTheory.Bass.StrictDiagramIndexChange
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
    {F : D ⥤ LoopPrespectrum.{w}}
    (η₂ : F ⟶ (strictDiagramFunctor Q₂).obj F)
    (η₁ : K ⋙ F ⟶ (strictDiagramFunctor Q₁).obj (K ⋙ F))
    (hseed : Functor.whiskerLeft K η₂ ≫ (iso K Q₁ Q₂ α F).hom = η₁)

/-- The original Bass telescope before restricting its actual coefficient index. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:35"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def telescope {E : Type u₁} [Category.{v₁} E] (Q : E ⥤ Arrow (Arrow E))
    {G : E ⥤ LoopPrespectrum.{w}} (η : G ⟶ (strictDiagramFunctor Q).obj G) :
    E ⥤ LoopPrespectrum.{w} :=
  Telescope.diagramFunctor (fun i => (strictDiagramIterate Q i).obj G)
    (strictDiagramTransition Q η)

/-- Restriction commutes with the original telescope as a complete diagram functor. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:42"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem restriction_telescope_eq :
    K ⋙ telescope Q₂ η₂ = Telescope.diagramFunctor
      (fun i => K ⋙ (strictDiagramIterate Q₂ i).obj F)
      (fun i => Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i)) := rfl

/-- The actual finite index maps descend with their unchanged telescope height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:48"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def telescopeMap : K ⋙ telescope Q₂ η₂ ⟶ telescope Q₁ η₁ :=
  Telescope.diagramMap (fun i => K ⋙ (strictDiagramIterate Q₂ i).obj F)
    (fun i => (strictDiagramIterate Q₁ i).obj (K ⋙ F))
    (fun i => Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i))
    (strictDiagramTransition Q₁ η₁) (fun i => (iterateIso K Q₁ Q₂ α i F).hom)
    (fun i => (transition_square K Q₁ Q₂ α η₂ η₁ hseed i).symm)

/-- The prescribed inverse finite maps also descend through the actual quotient. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:56"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def telescopeInv : telescope Q₁ η₁ ⟶ K ⋙ telescope Q₂ η₂ :=
  Telescope.diagramMap (fun i => (strictDiagramIterate Q₁ i).obj (K ⋙ F))
    (fun i => K ⋙ (strictDiagramIterate Q₂ i).obj F)
    (strictDiagramTransition Q₁ η₁)
    (fun i => Functor.whiskerLeft K (strictDiagramTransition Q₂ η₂ i))
    (fun i => (iterateIso K Q₁ Q₂ α i F).inv)
    (inverse_transition_square K Q₁ Q₂ α η₂ η₁ hseed)

/-- The forward map preserves the entire original quotient cylinder. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:65"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem telescopeMap_cylinder (X : C) (n i : ℕ) (s : unitInterval)
    (x : ((strictDiagramIterate Q₂ i).obj F |>.obj (K.obj X)).space n) :
    ((telescopeMap K Q₁ Q₂ α η₂ η₁ hseed).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate Q₂ j).obj F).obj (K.obj X))
        (fun j => (strictDiagramTransition Q₂ η₂ j).app (K.obj X)) n i (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate Q₁ j).obj (K ⋙ F)).obj X)
      (fun j => (strictDiagramTransition Q₁ η₁ j).app X) n i
      (s, ((iterateIso K Q₁ Q₂ α i F).hom.app X).map n x) := rfl

/-- The inverse keeps the same stage and complete quotient height. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:75"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem telescopeInv_cylinder (X : C) (n i : ℕ) (s : unitInterval)
    (x : ((strictDiagramIterate Q₁ i).obj (K ⋙ F) |>.obj X).space n) :
    ((telescopeInv K Q₁ Q₂ α η₂ η₁ hseed).app X).map n
      (Telescope.cylinder (fun j => ((strictDiagramIterate Q₁ j).obj (K ⋙ F)).obj X)
        (fun j => (strictDiagramTransition Q₁ η₁ j).app X) n i (s, x)) =
    Telescope.cylinder (fun j => ((strictDiagramIterate Q₂ j).obj F).obj (K.obj X))
      (fun j => (strictDiagramTransition Q₂ η₂ j).app (K.obj X)) n i
      (s, ((iterateIso K Q₁ Q₂ α i F).inv.app X).map n x) := rfl

/-- The original stage inclusion commutes with the same actual index map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:85"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem telescopeMap_inclusion (i : ℕ) :
    Functor.whiskerLeft K (Telescope.diagramInclusion
        (fun j => (strictDiagramIterate Q₂ j).obj F) (strictDiagramTransition Q₂ η₂) i) ≫
        telescopeMap K Q₁ Q₂ α η₂ η₁ hseed =
      (iterateIso K Q₁ Q₂ α i F).hom ≫ Telescope.diagramInclusion
        (fun j => (strictDiagramIterate Q₁ j).obj (K ⋙ F))
        (strictDiagramTransition Q₁ η₁) i :=
  Telescope.diagramInclusion_diagramMap _ _ _ _ _ _ i

/-- The actual two quotient maps compose to the identity, by original map composition. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:95"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem telescopeMap_inv :
    telescopeMap K Q₁ Q₂ α η₂ η₁ hseed ≫ telescopeInv K Q₁ Q₂ α η₂ η₁ hseed = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  rw [NatTrans.comp_app, NatTrans.id_app]
  dsimp only [telescopeMap, telescopeInv, Telescope.diagramMap]
  erw [Telescope.map_comp]
  simp only [Iso.hom_inv_id_app]
  exact Telescope.map_id _ _

/-- The inverse composite is also the identity on the complete original quotient. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:106"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem telescopeInv_map :
    telescopeInv K Q₁ Q₂ α η₂ η₁ hseed ≫ telescopeMap K Q₁ Q₂ α η₂ η₁ hseed = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  rw [NatTrans.comp_app, NatTrans.id_app]
  dsimp only [telescopeMap, telescopeInv, Telescope.diagramMap]
  erw [Telescope.map_comp]
  simp only [Iso.inv_hom_id_app]
  exact Telescope.map_id _ _

/-- The complete original Bass telescopes are naturally isomorphic under index change. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:117"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
def telescopeIso : K ⋙ telescope Q₂ η₂ ≅ telescope Q₁ η₁ where
  hom := telescopeMap K Q₁ Q₂ α η₂ η₁ hseed
  inv := telescopeInv K Q₁ Q₂ α η₂ η₁ hseed
  hom_inv_id := telescopeMap_inv K Q₁ Q₂ α η₂ η₁ hseed
  inv_hom_id := telescopeInv_map K Q₁ Q₂ α η₂ η₁ hseed

/-- The whole telescope comparison is stable because its actual inverse has been constructed. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramIndexTelescope.lean:124"
  "adaptation" "Actual index change, original finite transition and quotient telescope maps"]
theorem telescopeMap_stable (X : C) :
    IsStableEquivalence ((telescopeMap K Q₁ Q₂ α η₂ η₁ hseed).app X) := by
  change IsStableEquivalence ((telescopeIso K Q₁ Q₂ α η₂ η₁ hseed).hom.app X)
  intro d
  infer_instance

end KTheory.Bass.StrictDiagramIndexChange

