/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeStageInclusionComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedInputMaps

/-! # The actual finite-word correction on current-stage classes

The current-to-iterated stable-group zigzag carries each independently defined
stage inclusion through the genuine conjugating word. The resulting finite
stable automorphism is natural in the original Model input; no word is replaced
by an identity except at the separately proved initial stage.

Adapted from the original construction in
`Quillen/KTheory/Bass/SchemeStageClassComparison.lean`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap

/-- The actual finite stage comparison, conjugating word and inverse finite comparison. -/
def finiteStageStableIso (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w}) (i : ℕ)
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    stableHomotopyGroup (((strictDiagramIterate squareFunctor i).obj
      (M ⋙ prespectrumFunctor)).obj X) d ≅
    stableHomotopyGroup (((strictDiagramIterate squareFunctor i).obj
      (M ⋙ prespectrumFunctor)).obj X) d := by
  let H := stableHomotopyFunctor d
  let e := (stageMap squareFunctor i (M ⋙ prespectrumFunctor)).app X
  let : IsIso (H.map e) := model_stageMap_stable squareFunctor i M X d
  exact asIso (H.map e) ≪≫ H.mapIso ((conjugatingIso i (M ⋙ prespectrumFunctor)).app X) ≪≫
    (asIso (H.map e)).symm

/-- Every literal stage inclusion retains its full finite-word correction. -/
@[reassoc]
theorem currentIteratedStableIso_inclusion (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor))
    (i : ℕ) (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor d).map
        ((Telescope.diagramInclusion
          (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
          (currentTransition A) i).app X) ≫ (currentIteratedStableIso M A X d).hom =
      (finiteStageStableIso M i X d).hom ≫
        (stableHomotopyFunctor d).map
          ((Telescope.diagramInclusion
            (fun j => (strictDiagramIterate squareFunctor j).obj (M ⋙ prespectrumFunctor))
            (strictDiagramTransition squareFunctor (seed A)) i).app X) := by
  let H := stableHomotopyFunctor d
  let m := (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap A).app X
  let e := (stageMap squareFunctor i (M ⋙ prespectrumFunctor)).app X
  let : IsIso (H.map m) :=
    SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable M A X d
  let : IsIso (H.map e) := model_stageMap_stable squareFunctor i M X d
  have hc := congrArg H.map (congrArg (fun η => η.app X) (telescopeMap_inclusion A i))
  have hn := congrArg H.map
    (congrArg (fun η => η.app X) (conjugacyTelescopeMap_inclusion A i))
  have hi := congrArg H.map (congrArg (fun η => η.app X)
    (SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap_inclusion A i))
  simp only [NatTrans.comp_app, Functor.map_comp] at hc hn hi
  change H.map _ ≫ H.map m = H.map e ≫ H.map _ at hi
  change H.map _ ≫ H.map _ = H.map e ≫ H.map _ at hc
  change H.map _ ≫ (H.map _ ≫ H.map _ ≫ inv (H.map m)) =
    (H.map e ≫ H.map _ ≫ inv (H.map e)) ≫ H.map _
  apply (cancel_mono (H.map m)).1
  simp only [Category.assoc]
  rw [IsIso.inv_hom_id, Category.comp_id, hi]
  simp only [← Category.assoc] at hc hn ⊢
  rw [hc, Category.assoc, hn]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rfl

/-- The initial finite correction is the identity, with the original stage-zero objects. -/
theorem finiteStageStableIso_zero_hom (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) : (finiteStageStableIso M 0 X d).hom = 𝟙 _ := by
  change (stableHomotopyFunctor d).map (𝟙 _) ≫
    (stableHomotopyFunctor d).map ((conjugatingIso 0 (M ⋙ prespectrumFunctor)).hom.app X) ≫
      inv ((stableHomotopyFunctor d).map (𝟙 _)) = _
  rw [conjugatingIso_zero_hom]
  simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, IsIso.inv_id, Category.id_comp]
  exact (Category.comp_id _).trans ((stableHomotopyFunctor d).map_id _)

end KTheory.Bass.SchemeNaturalSeed
