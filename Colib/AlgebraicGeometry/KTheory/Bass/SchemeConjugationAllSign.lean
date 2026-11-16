/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeWordStableSign
public import Colib.Topology.Prespectrum.FiniteLoopStableSign
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeStageClassComparison

/-!
# Original finite corrections from the genuine pointwise quotient sign

Actual parameter-shift naturality transports the computed geometric-word
scalar through precisely the prescribed number of loops. The original loop
reversal has the same scalar, so their literal composite acts identically in
the original negative degree. The original finite stage comparison is retained.

Adapted from the original construction in
`Quillen/KTheory/Bass/SchemeConjugationAllSign.lean`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum.FiniteLoopWords
open KTheory.Bass.GeometricConeFixedWords
open KTheory.Bass.GeometricConeInterchange
universe u v w
namespace KTheory.Bass.SchemeNaturalSeed

private theorem scalar_change_degree {E : LoopPrespectrum.{w}} (f : E ⟶ E)
    {d e : ℤ} (hde : d = e) (z : ℤ)
    (h : (stableHomotopyFunctor d).map f = z • 𝟙 _) :
    (stableHomotopyFunctor e).map f = z • 𝟙 _ := by
  cases hde
  exact h

/-- The literal finite loop map transports a scalar from the actual shifted stable degree. -/
theorem loopMap_stable_scalar {C : Type u} [Category.{v} C]
    (n : ℕ) {F : C ⥤ LoopPrespectrum.{w}} (f : F ⟶ F) (X : C)
    (d : ℤ) (z : ℤ)
    (h : (stableHomotopyFunctor (d + (n : ℤ))).map (f.app X) = z • 𝟙 _) :
    (stableHomotopyFunctor d).map ((loopMap n f).app X) = z • 𝟙 _ := by
  induction n generalizing d with
  | zero =>
    change (stableHomotopyFunctor d).map (f.app X) = _
    exact scalar_change_degree (f.app X) (by omega) z h
  | succ n ih =>
    change (stableHomotopyFunctor d).map
      (parameterLoopingMap ((loopMap n f).app X)) = _
    apply parameterLoopingMap_stable_scalar _ d z
    apply ih (d + 1)
    have he : d + ((n + 1 : ℕ) : ℤ) = (d + 1) + (n : ℤ) := by omega
    exact scalar_change_degree (f.app X) he z h

variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (hF : ∀ X, LinearZeroGrowth (F.obj X))
    (S : QuasiCompactSchemes.{u}ᵒᵖ → Prop)
    (hL : ∀ X, S X → S (PolynomialLaurent.Relative.laurentFunctor.op.obj X))
    (hτ : ∀ X, S X → PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero F) X = -𝟙 _)

include hF hL hτ in
/-- Both signs in the original finite correction cancel in its original negative degree. -/
theorem conjugatingIso_neg_nat_id (n : ℕ) (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (hX : S X) :
    (stableHomotopyFunctor (-(n : ℤ))).map
      ((conjugatingIso n F).hom.app (op X.unop.obj)) = 𝟙 _ := by
  have hw := wordAt_zero_smul F hF S hL hτ n X hX
  have hl := loopMap_stable_scalar n (wordAt n F).hom (op X.unop.obj)
    (-(n : ℤ)) ((-1 : ℤ) ^ (n.choose 2))
    (scalar_change_degree ((wordAt n F).hom.app (op X.unop.obj))
      (by omega) ((-1 : ℤ) ^ (n.choose 2)) hw)
  change (stableHomotopyFunctor (-(n : ℤ))).map
    (((reversalIso n
      (FiniteConeTopology.iterate PolynomialLaurent.GlobalIndex.squareFunctor n F)).hom.app
        (op X.unop.obj)) ≫ (loopMap n (wordAt n F).hom).app (op X.unop.obj)) = _
  rw [CategoryTheory.Functor.map_comp, reversalIso_stable_sign, hl]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
    smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul]
  rfl

private theorem conjugate_identity {A B : AddCommGrpCat.{w}}
    (f : A ⟶ B) [IsIso f] (q : B ⟶ B) (hq : q = 𝟙 B) :
    f ≫ q ≫ inv f = 𝟙 A := by
  rw [hq, Category.id_comp, IsIso.hom_inv_id]

/-- The unchanged finite-stage comparison transports the original all-index identity. -/
theorem finiteStageStableIso_neg_nat_id
    (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (hM : ∀ Y, S Y → PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (M ⋙ prespectrumFunctor)) Y = -𝟙 _)
    (hS : ∀ Y, S Y → S (PolynomialLaurent.Relative.laurentFunctor.op.obj Y))
    (n : ℕ) (X : QuasiCompactSchemes.{u}ᵒᵖ) (hX : S X) :
    (finiteStageStableIso M n (op X.unop.obj) (-(n : ℤ))).hom = 𝟙 _ := by
  let H := stableHomotopyFunctor (-(n : ℤ))
  let e := (NormalizedStageMap.stageMap
    PolynomialLaurent.GlobalIndex.squareFunctor n
      (M ⋙ prespectrumFunctor)).app (op X.unop.obj)
  have : IsIso (H.map e) := NormalizedStageMap.model_stageMap_stable
    PolynomialLaurent.GlobalIndex.squareFunctor n M (op X.unop.obj) (-(n : ℤ))
  exact conjugate_identity (H.map e)
    (H.map ((conjugatingIso n (M ⋙ prespectrumFunctor)).hom.app (op X.unop.obj)))
    (conjugatingIso_neg_nat_id (M ⋙ prespectrumFunctor)
      (fun Y => model_linearZeroGrowth (M.obj Y)) S hS hM n X hX)

end KTheory.Bass.SchemeNaturalSeed
