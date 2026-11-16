/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.Bass.ConeZeroSign
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeFixedWords
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The stable sign of the prescribed geometric cone word

The independently descended quotient swap sign is required only on a specified
family of quasi-compact parameters closed under the actual Laurent functor.
The original cone inclusions propagate this pointwise input through genuine
cone iterates and through the actual endomorphism maps. The fixed beta and
word recursions then give their scalar signs, including the original power
comparison transports. No word-independent permutation action is assumed.

Adapted from the original construction in
`Quillen/KTheory/Bass/GeometricConeWordStableSign.lean`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme Topology Topology.LoopPrespectrum
universe u w
namespace KTheory.Bass.GeometricConeInterchange
open PolynomialLaurent.Relative GeometricConeFixedWords
local notation "L" => laurentFunctor.op
local notation "H" => stableHomotopyFunctor 0

/-- Every actual unlooped power retains the original zero-offset growth. -/
theorem power_linearZeroGrowth (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X)) (n : ℕ) (X : Scheme.{u}ᵒᵖ) :
    LinearZeroGrowth (((Functor.FixedWords.power coneFunctor n).obj F).obj X) := by
  induction n generalizing X with
  | zero => exact hF X
  | succ n ih => exact cone_linearZeroGrowth _ ih X

variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
  (hF : ∀ X, LinearZeroGrowth (F.obj X))
  (S : QuasiCompactSchemes.{u}ᵒᵖ → Prop)
  (hL : ∀ X, S X → S ((L).obj X))
  (hτ : ∀ X, S X → doubleContractionSwap (quasiCompactStableZero F) X = -𝟙 _)

include hF hL hτ

/-- The actual quotient sign propagates on the specified Laurent-closed family. -/
theorem power_doubleContractionSwap_neg (n : ℕ) (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (hX : S X) :
    doubleContractionSwap
      (quasiCompactStableZero ((Functor.FixedWords.power coneFunctor n).obj F)) X = -𝟙 _ := by
  induction n generalizing X with
  | zero => exact hτ X hX
  | succ n ih =>
    exact cone_doubleContractionSwap_neg _ (power_linearZeroGrowth F hF n) X
      (ih ((L).obj X) (hL X hX))

/-- Each genuine insertion has exactly the signs of its prescribed actual crossings. -/
theorem beta_zero_smul (n : ℕ) (X : QuasiCompactSchemes.{u}ᵒᵖ) (hX : S X) :
    (H).map (((beta n).hom.app F).app (op X.unop.obj)) =
      (-1 : ℤ) ^ n • 𝟙 _ := by
  induction n generalizing X with
  | zero =>
    simp only [beta, Functor.FixedWords.beta, Iso.refl_hom, NatTrans.id_app,
      CategoryTheory.Functor.map_id, pow_zero, one_smul]
  | succ n ih =>
    let Fn := (Functor.FixedWords.power coneFunctor n).obj F
    have hb : ((beta (n + 1)).hom.app F).app (op X.unop.obj) =
        (permutationFunctorIso.hom.app Fn).app (op X.unop.obj) ≫
          (coneFunctor.map ((beta n).hom.app F)).app (op X.unop.obj) :=
      congrArg (fun a => a.app (op X.unop.obj))
        (Functor.FixedWords.beta_succ_hom_app coneFunctor permutationFunctorIso n F)
    have hp : (H).map ((permutationFunctorIso.hom.app Fn).app (op X.unop.obj)) = -𝟙 _ :=
      permutation_zero_neg_of_growth Fn (power_linearZeroGrowth F hF n) X
        (power_doubleContractionSwap_neg F hF S hL hτ n X hX)
    have hc := coneMap_zero_zsmul ((Functor.FixedWords.power coneFunctor (n + 1)).obj F)
      (power_linearZeroGrowth F hF (n + 1)) ((beta n).hom.app F) (op X.unop.obj)
      ((-1 : ℤ) ^ n) (ih ((L).obj X) (hL X hX))
    rw [hb, Functor.map_comp, hp, hc]
    change (-𝟙 _) ≫ ((-1 : ℤ) ^ n • 𝟙 _) =
      (-1 : ℤ) ^ (n + 1) • 𝟙 _
    simp only [Preadditive.neg_comp, Category.id_comp, pow_succ,
      mul_smul, neg_one_zsmul, smul_neg]
    rfl

/-- The specified whole geometric word has its actual triangular crossing sign. -/
theorem word_zero_smul (n : ℕ) (X : QuasiCompactSchemes.{u}ᵒᵖ) (hX : S X) :
    (H).map (((word n).hom.app F).app (op X.unop.obj)) =
      (-1 : ℤ) ^ (n.choose 2) • 𝟙 _ := by
  induction n generalizing X with
  | zero =>
    simp only [word, Functor.FixedWords.fixedWord, Iso.refl_hom, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Nat.choose_zero_succ, pow_zero, one_smul]
  | succ n ih =>
    have hw : ((word (n + 1)).hom.app F).app (op X.unop.obj) =
        (coneFunctor.map ((word n).hom.app F)).app (op X.unop.obj) ≫
          ((beta n).hom.app F).app (op X.unop.obj) := rfl
    have hc := coneMap_zero_zsmul ((Functor.FixedWords.power coneFunctor n).obj F)
      (power_linearZeroGrowth F hF n) ((word n).hom.app F) (op X.unop.obj)
      ((-1 : ℤ) ^ (n.choose 2)) (ih ((L).obj X) (hL X hX))
    rw [hw, Functor.map_comp, hc, beta_zero_smul F hF S hL hτ n X hX]
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]
    rw [← pow_add]
    congr 2
    simp only [Nat.choose_succ_succ, Nat.choose_one_right]

/-- Both original whole-diagram equality transports preserve the computed word scalar. -/
theorem wordAt_zero_smul (n : ℕ) (X : QuasiCompactSchemes.{u}ᵒᵖ) (hX : S X) :
    (H).map ((wordAt n F).hom.app (op X.unop.obj)) =
      (-1 : ℤ) ^ (n.choose 2) • 𝟙 _ := by
  let e := (eqToIso (power_obj n F)).app (op X.unop.obj)
  have hw : (wordAt n F).hom.app (op X.unop.obj) =
      e.inv ≫ ((word n).hom.app F).app (op X.unop.obj) ≫ e.hom := rfl
  rw [hw, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    word_zero_smul F hF S hL hτ n X hX]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.id_comp]
  rw [← CategoryTheory.Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]

end KTheory.Bass.GeometricConeInterchange
