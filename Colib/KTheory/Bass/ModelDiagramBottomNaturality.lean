/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.KTheory.Bass.ModelDiagramBottomComparison

/-!
Source: `Quillen/KTheory/Bass/ModelDiagramBottomNaturality.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Naturality of bottom contraction for original strict Model-diagram maps

The bottom comparison preserves every strict prespectrum transformation between actual
Model-valued coefficient functors. This includes native support forget/enlargement and
open restriction as soon as their existing strict transformations are supplied.
-/

@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory CategoryTheory.Limits Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
universe u w
namespace KTheory.Bass
variable {R : CommRingCat.{u}} {F G : Under R ⥤ WideSubcategory preservesZero.{w}}
  (α : F ⋙ prespectrumFunctor ⟶ G ⋙ prespectrumFunctor) (i : ℕ)

/-- The unchanged finite-stage action of the supplied original strict transformation. -/
def modelDiagramBottomMap : modelDiagramBottomFunctor F i ⟶ modelDiagramBottomFunctor G i :=
  Functor.whiskerRight ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map α)
    (stableHomotopyFunctor (-(i : ℤ)))

/-- All four unchanged stage-i components of the supplied strict transformation. -/
def modelDiagramTwoChartSquareTransformation (a : Under R) :
    modelDiagramTwoChartSquare F i a ⟶ modelDiagramTwoChartSquare G i a :=
  (((Functor.mapArrowFunctor (Arrow (Under R)) (Arrow LoopPrespectrum.{w})).map
    ((Functor.mapArrowFunctor (Under R) LoopPrespectrum.{w}).map
      ((strictDiagramIterate (laurentUnderSquareFunctor R) i).map α))).app
        (laurentUnderSquare R a))

/-- The same strict maps preserve the actual cone-cokernel identification. -/
@[reassoc]
theorem modelDiagramBottomConeIso_map (a : Under R) :
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (modelDiagramBottomMap α i)).app a ≫ (modelDiagramBottomConeIso G i a).hom =
    (modelDiagramBottomConeIso F i a).hom ≫ (stableHomotopyFunctor (-(i : ℤ))).map
      (mappingConeMap (strictSquareComparisonFunctor.map
        (modelDiagramTwoChartSquareTransformation α i a))) := by
  apply (cancel_epi ((KTheory.Bass.TwoChart.contractionπ (underToLaurent R)
    (underToLaurentInvert R) (modelDiagramBottomFunctor F i)).app a)).mp
  rw [← Category.assoc, KTheory.Bass.TwoChart.contractionMap_π, Category.assoc,
    modelDiagramBottomConeIso_π, ← Category.assoc, modelDiagramBottomConeIso_π]
  exact KTheory.Bass.TwoChartStable.comparisonConeMap_inclusion
    (modelDiagramTwoChartSquareTransformation α i a) (-(i : ℤ))

/-- The real successor identity is natural for the original finite transformation. -/
@[reassoc]
theorem modelDiagramTwoChartSuccessorIso_map (a : Under R) :
    (((strictDiagramIterate (laurentUnderSquareFunctor R) (i + 1)).map α).app a) ≫
      (modelDiagramTwoChartSuccessorIso G i).hom.app a =
    (modelDiagramTwoChartSuccessorIso F i).hom.app a ≫
      strictSquareLoopedConeFunctor.map (modelDiagramTwoChartSquareTransformation α i a) := by
  have h := congrArg (fun t => t.app a)
    ((eqToIso (strictDiagramIterate_succ_right (laurentUnderSquareFunctor R) i)).hom.naturality α)
  simpa only [modelDiagramTwoChartSuccessorIso, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    modelDiagramTwoChartConeDiagram, modelDiagramTwoChartDiagram,
    modelDiagramTwoChartSquareTransformation, modelDiagramTwoChartSquare,
    strictDiagramFunctor, Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringLeft, Functor.whiskeringRight, Functor.mapArrowFunctor,
    Functor.whiskerLeft, Functor.whiskerRight, strictSquareLoopedConeFunctor,
    mappingConeFunctor, parameterLoopingFunctor, laurentUnderSquareFunctor]
    using h

/-- The original successor component before degree transport. -/
theorem modelDiagramStableSuccessorIso_hom_app (H : Under R ⥤ WideSubcategory preservesZero.{w})
    (d : ℤ) (a : Under R) :
    (modelDiagramStableSuccessorIso H i d).hom.app a =
    (stableHomotopyFunctor d).map ((modelDiagramTwoChartSuccessorIso H i).hom.app a) ≫
      (parameterStableHomotopyIso ((modelDiagramTwoChartConeDiagram H i).obj a) d).hom := rfl

/-- The genuine signed shift preserves the original strict transformation before degree transport.
-/
@[reassoc]
theorem modelDiagramStableSuccessorIso_map (d : ℤ) (a : Under R) :
    (stableHomotopyFunctor d).map
        (((strictDiagramIterate (laurentUnderSquareFunctor R) (i + 1)).map α).app a) ≫
      (modelDiagramStableSuccessorIso G i d).hom.app a =
    (modelDiagramStableSuccessorIso F i d).hom.app a ≫
      (stableHomotopyFunctor (d + 1)).map
        (mappingConeMap (strictSquareComparisonFunctor.map
          (modelDiagramTwoChartSquareTransformation α i a))) := by
  have h := congrArg ((stableHomotopyFunctor d).map)
    (modelDiagramTwoChartSuccessorIso_map α i a)
  rw [Functor.map_comp, Functor.map_comp] at h
  rw [modelDiagramStableSuccessorIso_hom_app, modelDiagramStableSuccessorIso_hom_app,
    ← Category.assoc, h, Category.assoc]
  have hn := parameterStableHomotopyIso_naturality (mappingConeMap
    (strictSquareComparisonFunctor.map (modelDiagramTwoChartSquareTransformation α i a))) d
  simpa only [Category.assoc, modelDiagramTwoChartConeDiagram, modelDiagramTwoChartDiagram,
    modelDiagramTwoChartSquare, Functor.comp_obj, strictSquareLoopedConeFunctor,
    Functor.comp_map, mappingConeFunctor, parameterLoopingFunctor,
    laurentUnderSquareFunctor] using congrArg
    (fun k => (stableHomotopyFunctor d).map
      ((modelDiagramTwoChartSuccessorIso F i).hom.app a) ≫ k) hn

/-- The same original strict transformation survives the bottom integer-degree transport. -/
@[reassoc]
theorem modelDiagramBottomSuccessorIso_map (a : Under R) :
    (modelDiagramBottomMap α (i + 1)).app a ≫ (modelDiagramBottomSuccessorIso G i).hom.app a =
    (modelDiagramBottomSuccessorIso F i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (mappingConeMap (strictSquareComparisonFunctor.map
          (modelDiagramTwoChartSquareTransformation α i a))) := by
  let e : stableHomotopyFunctor.{w} (-((i + 1 : ℕ) : ℤ) + 1) ≅
      stableHomotopyFunctor (-(i : ℤ)) :=
    eqToIso (congrArg (fun d : ℤ => stableHomotopyFunctor.{w} d)
      (show -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ) by omega))
  let c := mappingConeMap (strictSquareComparisonFunctor.map
    (modelDiagramTwoChartSquareTransformation α i a))
  change (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
      (((strictDiagramIterate (laurentUnderSquareFunctor R) (i + 1)).map α).app a) ≫
      ((modelDiagramStableSuccessorIso G i (-((i + 1 : ℕ) : ℤ))).hom.app a ≫ e.hom.app _) =
    ((modelDiagramStableSuccessorIso F i (-((i + 1 : ℕ) : ℤ))).hom.app a ≫ e.hom.app _) ≫
      (stableHomotopyFunctor (-(i : ℤ))).map c
  rw [← Category.assoc, modelDiagramStableSuccessorIso_map, Category.assoc]
  simpa only [Category.assoc, modelDiagramTwoChartConeDiagram, modelDiagramTwoChartDiagram,
    modelDiagramTwoChartSquare, Functor.comp_obj, mappingConeFunctor,
    laurentUnderSquareFunctor] using congrArg
    (fun k => (modelDiagramStableSuccessorIso F i (-((i + 1 : ℕ) : ℤ))).hom.app a ≫ k)
    (e.hom.naturality c)

/-- The genuine bottom contraction comparison retains the supplied original strict map at i+1.
-/
@[reassoc]
theorem modelDiagramBottomContractionIso_map (a : Under R) :
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (modelDiagramBottomMap α i)).app a ≫ (modelDiagramBottomContractionIso G i).hom.app a =
    (modelDiagramBottomContractionIso F i).hom.app a ≫ (modelDiagramBottomMap α (i + 1)).app a := by
  apply (cancel_mono ((modelDiagramBottomSuccessorIso G i).hom.app a)).mp
  simp only [Category.assoc]
  rw [modelDiagramBottomSuccessorIso_map α i a]
  simp only [modelDiagramBottomContractionIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  exact modelDiagramBottomConeIso_map α i a

end KTheory.Bass
