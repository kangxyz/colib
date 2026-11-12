/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedInput
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedClasses
public import Colib.Topology.Prespectrum.TelescopeStableEquivalence

/-!
# Stable invariance of the actual normalized row under Model input isomorphisms

The original finite Model maps and the complete normalized comparison square
prove stability of the independently constructed input map. No replacement
map is defined by conjugating stable homotopy groups.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeModelRowSeed
open NaturalTrack GeometricSeedCospan ModelRowZigzagSequentialization
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))
  (M' : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit' : ∀ X, 𝟭 (M'.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M'.obj (laurent.op.obj X)).obj.Obj)
  (hunit' : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M'.map (laurent.op.map g)).hom.toFunctor (unit' X) (unit' Y))
  (η : M ⟶ M')
  (hη : ∀ X, Preserves (η.app (laurent.op.obj X)).hom.toFunctor (unit X) (unit' X))


/-- Every actual finite normalized inclusion retains the original Model input map. -/
@[reassoc, colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInputStable.lean:43"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedStageInclusion_input (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    normalizedStageInclusion M unit hunit X i ≫
        normalizedInputMap M unit hunit M' unit' hunit' η hη X =
      stageInput M M' η i X ≫ normalizedStageInclusion M' unit' hunit' X i := by
  rw [← normalizedComparison_stageInclusion M unit hunit X i,
    Category.assoc, ← normalizedComparison_inputMap]
  have h := Telescope.inclusion_map
    (vertex squareFunctor M X)
    (fun j => (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) j).app X)
    (vertex squareFunctor M' X)
    (fun j => (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M' unit' hunit') j).app X)
    (fun j => stageInput M M' η j X)
    (fun j => input_current_square M unit hunit M' unit' hunit' η hη j X) i
  dsimp only [SchemeNaturalSeed.currentInputMap, Telescope.diagramMap, stageInput,
    vertex, ModelZigzagSequentialization.vertex] at h ⊢
  rw [← Category.assoc, h, Category.assoc,
    normalizedComparison_stageInclusion M' unit' hunit' X i]

variable [IsIso η]

/-- The original finite input maps give a stable equivalence of the current telescopes. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInputStable.lean:66"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem currentInputMap_stable_of_isIso (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((SchemeNaturalSeed.currentInputMap
      (ofModelUnits laurent.op coefficient M unit hunit)
      (ofModelUnits laurent.op coefficient M' unit' hunit')
      (Functor.whiskerRight η prespectrumFunctor)
      (inputEquivariance M unit hunit M' unit' hunit' η hη)).app X) := by
  dsimp only [SchemeNaturalSeed.currentInputMap, Telescope.diagramMap]
  apply Telescope.map_isStableEquivalence
  intro i d
  have : IsIso (Functor.whiskerRight η prespectrumFunctor) := by infer_instance
  have : IsIso ((strictDiagramIterate squareFunctor i).map
      (Functor.whiskerRight η prespectrumFunctor)) := by infer_instance
  infer_instance

/-- The actual normalized input map is stable for an isomorphism of the original Models. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowNormalizedInputStable.lean:81"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem normalizedInputMap_stable_of_isIso (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (normalizedInputMap M unit hunit M' unit' hunit' η hη X) := by
  intro d
  have hc := normalizedComparison_stable M unit hunit X d
  have hc' := normalizedComparison_stable M' unit' hunit' X d
  have hi := currentInputMap_stable_of_isIso M unit hunit M' unit' hunit' η hη X d
  have hs := congrArg ((stableHomotopyFunctor d).map)
    (normalizedComparison_inputMap M unit hunit M' unit' hunit' η hη X)
  rw [Functor.map_comp, Functor.map_comp] at hs
  have : IsIso ((stableHomotopyFunctor d).map (normalizedComparison M unit hunit X) ≫
      (stableHomotopyFunctor d).map
        (normalizedInputMap M unit hunit M' unit' hunit' η hη X)) := by
    rw [← hs]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((stableHomotopyFunctor d).map (normalizedComparison M unit hunit X)) _

end KTheory.Bass.SchemeModelRowSeed
