/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.PairedActionLift
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.PairedSectionCylinderLifting
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionAction
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CorrectionLambdaAction
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.GraphAction
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedLambdaDescent

/-!
# Lifting the two original representatives with the same section choices

The two lambda correspondences and the correction act on the actual original
representatives. Their source and target comparisons are literal graphs of the
restriction maps through the same two section choices.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample Stacks.Divisors Stacks.Morphisms
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

set_option maxHeartbeats 1200000 in
-- Use the one telescope shared with the native polynomial refinement.
/-- The four original actions supply the whole-cylinder lifting of the
matching representatives. -/
theorem nisnevichImage_wholeCylinder_lift_of_pairedSectionData
    {k : Type u} [Field k] : PairedSectionCylinderLifting k := by
  unfold PairedSectionCylinderLifting
  intro S X Y P C A Z D₁ D₂ V _ _ _ _ _ _
    t _ q _ _ π _ _ f _ j _ _ jA _ _ p _ hRet hB hA
    a _ _ z s hs H e d₁ hd₁ d₂ _ _ hd₂ ha c₁ c₂ v _ _ u hu g hg hc₁ hc₂
    zA hmark _ _ _ _ bI hbI bE hbE hResidual
    b bA rB rA Y₀ X₀ V₀ A₀ A₁ hSourceBase hTargetBase ha₀ u₀ p₀ g₀ a₀ I₀
    Pst hPst hSrc hPuncture hInfinity hIntegral Xo U U' T Ao Yo Bo jU l _ _
    hne eT h he E i pT oA oY rAo rYo rBo hAo hYo hBoA hBoY hCover σ sA sY hm hsA hsY
  let lambdaB₀ : Cor.mk Y₀ ⟶ Cor.mk V₀ := c₁.lambda t v hc₁
  let lambdaA₀ : Cor.mk X₀ ⟶ Cor.mk A₁ := c₂.lambda t (a ≫ jA) hc₂
  let psi₀ : Cor.mk A₀ ⟶ Cor.mk V₀ := c₁.psi t v hc₁
  let Q := nisnevichImage Pst
  let hQ := nisnevichImage_isA1Invariant Pst hPst
  let γ := Cor.graphFunctor k
  have hE₂ : Q.transfer (lambdaB₀ ≫ γ.map u₀) = Q.transfer (γ.map (𝟙 Y₀)) :=
    SectionData.transfer_lambda_comp_graph_eq_id (q := q) (π := f ≫ π)
      (j := j) (p := p) t v hc₁ u hu c₁ Q hQ
  have hE₄ : Q.transfer (psi₀ ≫ γ.map u₀) = 0 :=
    SectionData.transfer_psi_comp_graph_eq_zero (q := q) (π := f ≫ π)
      (j := j) (p := p) t v hc₁ u hu c₁ Q hQ
  have hE₃ : Q.transfer (Sub.sub (α := Cor.mk Y₀ ⟶ Cor.mk A₁)
      (lambdaB₀ ≫ γ.map g₀) (γ.map p₀ ≫ lambdaA₀)) = 0 :=
    nisnevichImage_transfer_pairedLambdaDifference_zero t q π f j jA p hRet
      hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ v g hg hc₁ hc₂ bI hbI
      Pst hPst hSrc hResidual hPuncture hInfinity hIntegral
  have hE₅ : Q.transfer (Sub.sub (α := Cor.mk A₀ ⟶ Cor.mk A₁)
      (γ.map a₀ ≫ lambdaA₀) (psi₀ ≫ γ.map g₀)) = Q.transfer (γ.map (I₀).hom) :=
    transfer_lambda_sub_correction_eq_graph t q π f j jA p hRet hB hA
      a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ v g hg hc₁ hc₂ bI hbI bE hbE Q hQ hInfinity
  exact nisnevichImage_wholeCylinder_lift_of_pairedActions
    t q π f j jA p hRet hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂
    v u hu g hg hc₁ hc₂ Pst jU l hne eT h he E i pT oA oY rAo rYo rBo hAo hYo hBoA hBoY
    hCover σ sA sY hm hsA hsY hE₂ hE₄ hE₃ hE₅

end AlgebraicGeometry.PresheafWithTransfers
