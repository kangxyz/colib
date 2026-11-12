/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeIteratedSeedTelescope
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTelescope
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWordRecursion

/-! # The actual stage-zero inclusions through the current-to-iterated zigzag -/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The initial class map is the literal stage-zero inclusion into the current telescope. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeStageZeroComparison.lean:26"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def currentInitial (A : Track laurent.op coefficient F) : F ⟶ currentTelescope A :=
  Telescope.diagramInclusion (fun i => (strictDiagramIterate squareFunctor i).obj F)
    (currentTransition A) 0

/-- The original iterated-seed initial class uses its independently defined inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeStageZeroComparison.lean:31"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def iteratedInitial (A : Track laurent.op coefficient F) : F ⟶ iteratedTelescope A :=
  Telescope.diagramInclusion (fun i => (strictDiagramIterate squareFunctor i).obj F)
    (fun i => strictDiagramTransition squareFunctor (seed A) i) 0

/-- Both original stage-zero loop and cone words are literally the identity. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeStageZeroComparison.lean:36"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem conjugatingIso_zero_hom : (conjugatingIso 0 F).hom = 𝟙 F := by
  rw [conjugatingIso_hom, GeometricConeFixedWords.wordAt_zero_hom]
  rfl

/-- The two actual forward routes preserve the same independent initial inclusion. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeStageZeroComparison.lean:41"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem initial_zigzag (A : Track laurent.op coefficient F) :
    currentInitial A ≫ telescopeMap A ≫ conjugacyTelescopeMap A =
      iteratedInitial A ≫ SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap A := by
  unfold currentInitial iteratedInitial
  rw [← Category.assoc, telescopeMap_inclusion]
  change (𝟙 F ≫ _) ≫ _ = _
  rw [Category.id_comp, conjugacyTelescopeMap_inclusion, conjugatingIso_zero_hom]
  erw [Category.id_comp]

/-- The actual current-to-iterated stable-group comparison keeps its three original factors. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeStageZeroComparison.lean:51"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def currentIteratedStableIso (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    stableHomotopyGroup ((currentTelescope A).obj X) d ≅
      stableHomotopyGroup ((iteratedTelescope A).obj X) d := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map ((telescopeMap A).app X)) := model_telescopeMap_stable M A X d
  let : IsIso (H.map ((conjugacyTelescopeMap A).app X)) :=
    model_conjugacyTelescopeMap_stable M A X d
  let : IsIso (H.map ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap A).app X)) :=
    SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable M A X d
  exact asIso (H.map ((telescopeMap A).app X)) ≪≫
    asIso (H.map ((conjugacyTelescopeMap A).app X)) ≪≫
    (asIso (H.map ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap A).app X))).symm

/-- The stable-group zigzag sends the independently defined current initial class to the old one. -/
@[reassoc, colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeStageZeroComparison.lean:68"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem currentIteratedStableIso_initial (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor d).map ((currentInitial A).app X) ≫
        (currentIteratedStableIso M A X d).hom =
      (stableHomotopyFunctor d).map ((iteratedInitial A).app X) := by
  let H := stableHomotopyFunctor d
  let m := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap A).app X
  let : IsIso (H.map m) :=
    SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable M A X d
  have h := congrArg H.map (congrArg (fun η => η.app X) (initial_zigzag A))
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  change H.map _ ≫ (H.map _ ≫ H.map _ ≫ inv (H.map m)) = H.map _
  simp only [← Category.assoc] at h
  rw [← Category.assoc, ← Category.assoc, h, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

end KTheory.Bass.SchemeNaturalSeed
