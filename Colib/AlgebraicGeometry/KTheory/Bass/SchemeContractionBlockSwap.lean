/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeDoubleContractionBraid

/-!
# Actual block transport on the fourfold Bass quotient

The block swap is the actual adjacent-swap word `s₁ s₀ s₂ s₁`, where
`s₀ = τ_(C²F)`, `s₁ = C(τ_(CF))`, and `s₂ = C²(τ_F)`.
The geometric braid relation and naturality prove its conjugacy square without
assuming a swap sign or supplying the square as input. Cancellation on the original
Laurent projection also gives a pointwise version:
`τ_F` need only be negative identity at the double Laurent base `L²X`.
The global negative-identity theorem follows as a corollary. The cubic braid also
propagates a sign at `LX` through one contraction, with no global sign hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
universe u w
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open KTheory.Bass.TwoChart

local notation "C" => contraction (NatTrans.op plus) (NatTrans.op minus)
local notation "CM" => contractionMap (NatTrans.op plus) (NatTrans.op minus)
local notation "CF" => contractionFunctor (NatTrans.op plus) (NatTrans.op minus)
local notation "τ" => doubleContractionSwapNatIso

/-- The actual adjacent-swap word that exchanges the two pairs of Laurent variables. -/
def fourfoldContractionBlockSwapNatIso
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    C (C (C (C F))) ≅ C (C (C (C F))) :=
  (CF).mapIso (τ (C F)) ≪≫ τ (C (C F)) ≪≫
    (CF).mapIso ((CF).mapIso (τ F)) ≪≫ (CF).mapIso (τ (C F))

local notation "L" => laurentFunctor.op
local notation "θ" => contractionπ (NatTrans.op plus) (NatTrans.op minus)

/-- The four original quotient projections in their fixed original order. -/
def fourfoldContractionπ (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    F.obj ((L).obj ((L).obj ((L).obj ((L).obj X)))) ⟶ (C (C (C (C F)))).obj X :=
  (θ F).app ((L).obj ((L).obj ((L).obj X))) ≫ tripleContractionπ (C F) X

instance fourfoldContractionπ_epi (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) : Epi (fourfoldContractionπ F X) := by
  unfold fourfoldContractionπ
  infer_instance

/-- Splitting off the last original quotient changes no representative. -/
theorem fourfoldContractionπ_eq (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    fourfoldContractionπ F X =
      tripleContractionπ F ((L).obj X) ≫ (θ (C (C (C F)))).app X := by
  simp only [fourfoldContractionπ, tripleContractionπ, doubleContractionπ, Category.assoc]

/-- The outer pair acts on the original fourfold Laurent representatives by `L²(σ)`. -/
@[reassoc]
theorem fourfoldContractionπ_outer_swap
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    fourfoldContractionπ F X ≫ doubleContractionSwap (C (C F)) X =
      F.map ((L).map ((L).map (doubleLaurentOppositeSwap.hom.app X))) ≫
        fourfoldContractionπ F X := by
  unfold fourfoldContractionπ
  rw [Category.assoc, tripleContractionπ_outer_swap]
  have h := (θ F).naturality ((L).map (doubleLaurentOppositeSwap.hom.app X))
  simp only [Functor.comp_map, Functor.comp_obj] at h
  rw [← Category.assoc, ← h, Category.assoc]

/-- The middle adjacent pair acts by the literal middle-variable swap. -/
@[reassoc]
theorem fourfoldContractionπ_middle_swap
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    fourfoldContractionπ F X ≫ (CM (τ (C F)).hom).app X =
      F.map ((L).map (doubleLaurentOppositeSwap.hom.app ((L).obj X))) ≫
        fourfoldContractionπ F X := by
  unfold fourfoldContractionπ
  rw [Category.assoc, tripleContractionπ_inner_swap]
  have h := (θ F).naturality (doubleLaurentOppositeSwap.hom.app ((L).obj X))
  simp only [Functor.comp_map, Functor.comp_obj] at h
  rw [← Category.assoc, ← h, Category.assoc]

/-- The inner pair acts by the literal swap at the double Laurent base. -/
@[reassoc]
theorem fourfoldContractionπ_inner_swap
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    fourfoldContractionπ F X ≫ (CM (CM (τ F).hom)).app X =
      F.map (doubleLaurentOppositeSwap.hom.app ((L).obj ((L).obj X))) ≫
        fourfoldContractionπ F X := by
  simp only [fourfoldContractionπ_eq, Category.assoc, contractionMap_π]
  exact tripleContractionπ_inner_swap_assoc F ((L).obj X) ((θ (C (C (C F)))).app X)

/-- The actual four-variable representative word exchanges the two consecutive pairs. -/
def fourfoldLaurentBlockSwap (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (L).obj ((L).obj ((L).obj ((L).obj X))) ⟶ (L).obj ((L).obj ((L).obj ((L).obj X))) :=
  (L).map (doubleLaurentOppositeSwap.hom.app ((L).obj X)) ≫
    (L).map ((L).map (doubleLaurentOppositeSwap.hom.app X)) ≫
      doubleLaurentOppositeSwap.hom.app ((L).obj ((L).obj X)) ≫
        (L).map (doubleLaurentOppositeSwap.hom.app ((L).obj X))

/-- The block isomorphism retains the literal original four-variable representative word. -/
@[reassoc]
theorem fourfoldContractionπ_blockSwap
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    fourfoldContractionπ F X ≫ (fourfoldContractionBlockSwapNatIso F).hom.app X =
      F.map (fourfoldLaurentBlockSwap X) ≫ fourfoldContractionπ F X := by
  change fourfoldContractionπ F X ≫
      ((CM (τ (C F)).hom).app X ≫ doubleContractionSwap (C (C F)) X ≫
        (CM (CM (τ F).hom)).app X ≫ (CM (τ (C F)).hom).app X) = _
  simp only [fourfoldContractionπ_middle_swap_assoc, fourfoldContractionπ_outer_swap_assoc,
    fourfoldContractionπ_inner_swap_assoc, fourfoldContractionπ_middle_swap]
  simp only [fourfoldLaurentBlockSwap, Functor.map_comp, Category.assoc]

/-- The swaps in disjoint pairs commute by naturality of the independently descended swap. -/
theorem fourfoldContractionSwap_disjoint
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (τ (C (C F))).hom ≫ CM (CM (τ F).hom) =
      CM (CM (τ F).hom) ≫ (τ (C (C F))).hom := by
  apply NatTrans.ext
  funext X
  simpa only [NatTrans.comp_app, doubleContractionSwapNatIso_hom_app] using
    (doubleContractionSwap_groupMap (τ F).hom X).symm

/-- The actual fourfold block swap conjugates the two independently descended pair swaps. -/
theorem fourfoldContractionBlockSwap_conjugates
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (fourfoldContractionBlockSwapNatIso F).hom ≫ (τ (C (C F))).hom =
      CM (CM (τ F).hom) ≫ (fourfoldContractionBlockSwapNatIso F).hom := by
  let a := (τ (C (C F))).hom
  let b := CM (τ (C F)).hom
  let c := CM (CM (τ F).hom)
  have hac : a ≫ c = c ≫ a := fourfoldContractionSwap_disjoint F
  have hab : a ≫ b ≫ a = b ≫ a ≫ b := doubleContractionSwap_braid (C F)
  have hbc : b ≫ c ≫ b = c ≫ b ≫ c := by
    simpa only [contractionMap_comp] using
      congrArg (CM) (doubleContractionSwap_braid F)
  change (b ≫ a ≫ c ≫ b) ≫ a = c ≫ (b ≫ a ≫ c ≫ b)
  calc
    (b ≫ a ≫ c ≫ b) ≫ a = b ≫ (a ≫ c) ≫ (b ≫ a) := by simp only [Category.assoc]
    _ = b ≫ (c ≫ a) ≫ (b ≫ a) := by rw [hac]
    _ = b ≫ c ≫ (a ≫ b ≫ a) := by simp only [Category.assoc]
    _ = b ≫ c ≫ (b ≫ a ≫ b) := by rw [hab]
    _ = (b ≫ c ≫ b) ≫ a ≫ b := by simp only [Category.assoc]
    _ = (c ≫ b ≫ c) ≫ a ≫ b := by rw [hbc]
    _ = c ≫ b ≫ (c ≫ a) ≫ b := by simp only [Category.assoc]
    _ = c ≫ b ≫ (a ≫ c) ≫ b := by rw [← hac]
    _ = c ≫ (b ≫ a ≫ c ≫ b) := by simp only [Category.assoc]

/-- The actual block conjugacy at a single coefficient scheme. -/
@[reassoc]
theorem fourfoldContractionBlockSwap_conjugates_app
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (fourfoldContractionBlockSwapNatIso F).hom.app X ≫
        doubleContractionSwap (C (C F)) X =
      (CM (CM (τ F).hom)).app X ≫ (fourfoldContractionBlockSwapNatIso F).hom.app X := by
  simpa only [NatTrans.comp_app, doubleContractionSwapNatIso_hom_app] using
    congrArg (fun α => α.app X) (fourfoldContractionBlockSwap_conjugates F)

/-- An inner negative sign forces the outer sign via actual block transport. -/
theorem doubleContractionSwap_neg_of_doubleMap_neg
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (h : CM (CM (τ F).hom) = -𝟙 (C (C (C (C F))))) :
    (τ (C (C F))).hom = -𝟙 (C (C (C (C F)))) := by
  apply (cancel_epi (fourfoldContractionBlockSwapNatIso F).hom).1
  rw [fourfoldContractionBlockSwap_conjugates, h]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]

/-- A sign at the single original double Laurent base propagates to the outer pair at `X`. -/
theorem doubleContractionSwap_neg_contraction_contraction_app
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : doubleContractionSwap F ((L).obj ((L).obj X)) =
      -𝟙 ((C (C F)).obj ((L).obj ((L).obj X)))) :
    doubleContractionSwap (C (C F)) X = -𝟙 ((C (C (C (C F)))).obj X) := by
  have hmap : (CM (CM (τ F).hom)).app X = -𝟙 ((C (C (C (C F)))).obj X) := by
    apply doubleContraction_hom_ext (NatTrans.op plus) (NatTrans.op minus) (C (C F)) X
    rw [doubleContractionπ_groupMap, doubleContractionSwapNatIso_hom_app, h]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]
  apply (cancel_epi ((fourfoldContractionBlockSwapNatIso F).hom.app X)).1
  rw [fourfoldContractionBlockSwap_conjugates_app, hmap]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]

/-- A sign at one Laurent base propagates one contraction by the actual cubic braid. -/
theorem doubleContractionSwap_neg_contraction_app
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : doubleContractionSwap F ((L).obj X) = -𝟙 ((C (C F)).obj ((L).obj X))) :
    doubleContractionSwap (C F) X = -𝟙 ((C (C (C F))).obj X) := by
  have hmap : (CM (τ F).hom).app X = -𝟙 ((C (C (C F))).obj X) := by
    apply contraction_hom_ext (NatTrans.op plus) (NatTrans.op minus) (C (C F)) X
    rw [contractionMap_π, doubleContractionSwapNatIso_hom_app, h]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]
  have hb := congrArg (fun α => α.app X) (doubleContractionSwap_braid F)
  simp only [NatTrans.comp_app, doubleContractionSwapNatIso_hom_app] at hb
  simp only [hmap] at hb
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id,
    neg_neg, doubleContractionSwap_comp] using hb.symm

/-- The negative sign propagates two contractions using the actual four-variable block swap. -/
theorem doubleContractionSwap_neg_contraction_contraction
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (h : (τ F).hom = -𝟙 (C (C F))) :
    (τ (C (C F))).hom = -𝟙 (C (C (C (C F)))) := by
  apply NatTrans.ext
  funext X
  simp only [doubleContractionSwapNatIso_hom_app, NatTrans.app_neg, NatTrans.id_app]
  apply doubleContractionSwap_neg_contraction_contraction_app F X
  simpa only [doubleContractionSwapNatIso_hom_app, NatTrans.app_neg, NatTrans.id_app] using
    congrArg (fun α => α.app ((L).obj ((L).obj X))) h

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
