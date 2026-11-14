/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.Bass.ModelConeZeroQuotient
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeContractionBlockSwap

/-!
# Pointwise sign transport through the original connective cone

The actual cone target inclusion transports a scalar action from the Laurent
component of an input endomorphism. The natural epimorphic quotient comparison
also transports the independently descended double-swap sign from the original
Laurent parameter to the degree-zero groups of the actual unlooped cone.
All hypotheses are at the specified original Laurent objects.

Adapted from the original construction in
`Quillen/KTheory/Bass/ConeZeroSign.lean`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open Topology Topology.LoopPrespectrum KTheory.Bass.TwoChart
universe u w
namespace KTheory.Bass.GeometricConeInterchange
open PolynomialLaurent.Relative
local notation "p" => NatTrans.op plus
local notation "m" => NatTrans.op minus
local notation "L" => laurentFunctor.op

private theorem scalar_of_epi_square {A B : AddCommGrpCat.{w}}
    (j : A ⟶ B) [Epi j] (f : A ⟶ A) (g : B ⟶ B) (z : ℤ)
    (hs : f ≫ j = j ≫ g) (hf : f = z • 𝟙 A) : g = z • 𝟙 B := by
  apply (cancel_epi j).1
  rw [← hs, hf]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Category.id_comp, Category.comp_id]

/-- A scalar on the original Laurent component determines the actual cone-map scalar. -/
theorem coneMap_zero_zsmul (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (η : F ⟶ F)
    (X : Scheme.{u}ᵒᵖ) (z : ℤ)
    (h : (stableHomotopyFunctor 0).map
      (η.app (PolynomialLaurent.GlobalIndex.laurent.op.obj X)) = z • 𝟙 _) :
    (stableHomotopyFunctor 0).map ((coneFunctor.map η).app X) = z • 𝟙 _ := by
  let j := (stableHomotopyFunctor 0).map (coneInclusion F X)
  have : Epi j := coneInclusion_zero_epi F hF X
  exact scalar_of_epi_square j _ _ z
    (KTheory.Bass.TwoChartStable.comparisonConeMap_inclusion
      (diagramSquareMap η (PolynomialLaurent.GlobalIndex.square X)) 0) h

/-- A sign at the actual Laurent parameter propagates to the H-zero row of the original cone. -/
theorem cone_doubleContractionSwap_neg
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ Y, LinearZeroGrowth (F.obj Y)) (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : doubleContractionSwap (quasiCompactStableZero F) ((L).obj X) = -𝟙 _) :
    doubleContractionSwap (quasiCompactStableZero (coneFunctor.obj F)) X = -𝟙 _ := by
  let d := coneZeroQuotient F hF
  let e := (contractionMap p m (contractionMap p m d)).app X
  have : Epi e := epi_doubleContractionMap_app p m d X
  have hs := doubleContractionSwap_neg_contraction_app (quasiCompactStableZero F) X h
  apply (cancel_epi e).1
  rw [show e ≫ doubleContractionSwap (quasiCompactStableZero (coneFunctor.obj F)) X =
      doubleContractionSwap (contraction p m (quasiCompactStableZero F)) X ≫ e from
        doubleContractionSwap_groupMap d X, hs]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.id_comp, Category.comp_id]

/-- Zero-offset growth gives the original double-Laurent epimorphism without a Model assumption. -/
theorem doubleLaurentInclusion_zero_epi_of_growth
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ Y, LinearZeroGrowth (F.obj Y)) (X : Scheme.{u}ᵒᵖ) :
    Epi ((stableHomotopyFunctor 0).map (doubleLaurentInclusion F X)) := by
  have := coneInclusion_zero_epi F hF (PolynomialLaurent.GlobalIndex.laurent.op.obj X)
  have := coneInclusion_zero_epi (coneFunctor.obj F) (cone_linearZeroGrowth F hF) X
  rw [show (stableHomotopyFunctor 0).map (doubleLaurentInclusion F X) =
      (stableHomotopyFunctor 0).map
        (coneInclusion F (PolynomialLaurent.GlobalIndex.laurent.op.obj X)) ≫
        (stableHomotopyFunctor 0).map (coneInclusion (coneFunctor.obj F) X) from
          (stableHomotopyFunctor 0).map_comp _ _]
  infer_instance

/-- The actual geometric permutation sign applies to every genuine connective cone iterate. -/
theorem permutation_zero_neg_of_growth
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ Y, LinearZeroGrowth (F.obj Y)) (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : doubleContractionSwap (quasiCompactStableZero F) X = -𝟙 _) :
    (stableHomotopyFunctor 0).map (permutation F (op X.unop.obj)).hom = -𝟙 _ := by
  let G := quasiCompactStableZero F
  let A := G.obj ((L).obj ((L).obj X))
  let B := (contraction p m (contraction p m G)).obj X
  let C := (stableHomotopyFunctor 0).obj
    ((coneFunctor.obj (coneFunctor.obj F)).obj (op X.unop.obj))
  let j : A ⟶ C := (stableHomotopyFunctor 0).map (doubleLaurentInclusion F (op X.unop.obj))
  let q : A ⟶ B := doubleContractionπ p m G X
  let d : B ⟶ C := doubleLaurentQuotientMap F hF X
  let s : A ⟶ A := G.map (doubleLaurentOppositeSwap.hom.app X)
  let r : C ⟶ C := (stableHomotopyFunctor 0).map (permutation F (op X.unop.obj)).hom
  have : Epi j := doubleLaurentInclusion_zero_epi_of_growth F hF (op X.unop.obj)
  have hd : q ≫ d = j := doubleLaurentQuotientMap_π F hF X
  have hs : q ≫ doubleContractionSwap G X = s ≫ q := doubleContractionπ_swap G X
  have ht : doubleContractionSwap G X = -𝟙 B := h
  have hr : j ≫ r = s ≫ j := doubleLaurentInclusion_permutation_stable F (op X.unop.obj) 0
  apply (cancel_epi j).1
  change j ≫ r = j ≫ (-𝟙 C)
  rw [hr, ← hd, ← Category.assoc, ← hs, ht]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.comp_id]

end KTheory.Bass.GeometricConeInterchange
