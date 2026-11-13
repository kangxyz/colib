/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.BoundaryUnit
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.GraphProduct
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.PullbackGeneration
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionData

/-!
# The normalized quotient of the original paired graph sections

Both generating sections and the finite locally free witness are retained
on the same open. The normalized quotient reads one on the whole
boundary coproduct and satisfies the original norm equation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
set_option cleanup.letToHave false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.Morphisms TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance]
  compactificationGraphIdeal_isEffectiveCartierDivisor
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

local instance {U : Scheme.{u}} (L : U.Modules) [hL : IsInvertibleModule U L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L := hL

local instance {U : Scheme.{u}} (D : U.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule U (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

/-- The same graph numerator and pole section determine a specified coefficient
on the actual pullback. -/
structure PairedGraphRatioWitness {X W : Scheme.{u}} (g : W ⟶ X)
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (T : X.Modules) [IsInvertibleModule X T]
    (n : Γ(Stacks.Divisors.tensorModules (divisorSheaf D) T, ⊤)) (d : Γ(T, ⊤))
    (c : Γ(W, ⊤)) : Prop where
  /-- The graph numerator generates on this pullback. -/
  numerator : graphNumeratorGeneratesOnPullback g D T n
  /-- The pole factor generates on this pullback. -/
  pole : sectionGeneratesOnPullback g T d
  /-- The coefficient reads the actual graph times the pole in the numerator frame. -/
  coefficient : c = graphSectionRatioCoefficientOfGenerating g D T n d numerator

/-- Restrict both generating sections and their exact coefficient through
a specified factorization of the original chart map. -/
theorem PairedGraphRatioWitness.pullback {X W W' : Scheme.{u}} (g : W ⟶ X)
    (u : W' ⟶ W) (g' : W' ⟶ X) (h : u ≫ g = g')
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (T : X.Modules) [IsInvertibleModule X T]
    (n : Γ(Stacks.Divisors.tensorModules (divisorSheaf D) T, ⊤)) (d : Γ(T, ⊤))
    (c : Γ(W, ⊤)) (hc : PairedGraphRatioWitness g D T n d c) :
    PairedGraphRatioWitness g' D T n d (u.appTop c) := by
  subst g'
  let L := Stacks.Divisors.tensorModules (divisorSheaf D) T
  have hn := zeroScheme_pullback_eq_top_of_factor g (u ≫ g) u rfl L n hc.numerator
  have hd := zeroScheme_pullback_eq_top_of_factor g (u ≫ g) u rfl T d hc.pole
  exact ⟨hn, hd, (congrArg (fun a ↦ u.appTop a) hc.coefficient).trans
    (graphSectionRatioCoefficient_comp g D T u n d hc.numerator hn)⟩

/-- The actual coefficient is regular on an affine chart where the original
graph remains Cartier. -/
theorem PairedGraphRatioWitness.isRightRegular_appTop {X W V : Scheme.{u}}
    (g : W ⟶ X) (v : V ⟶ W) [IsAffine V]
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (hD : IsEffectiveCartierDivisor ((D.comap g).comap v))
    (T : X.Modules) [IsInvertibleModule X T]
    (n : Γ(Stacks.Divisors.tensorModules (divisorSheaf D) T, ⊤)) (d : Γ(T, ⊤))
    (c : Γ(W, ⊤)) (hc : PairedGraphRatioWitness g D T n d c) :
    IsRightRegular (v.appTop c) :=
  (congrArg (fun x : Γ(W, ⊤) ↦ IsRightRegular (v.appTop x)) hc.coefficient).mpr
    (isRegular_appTop_graphSectionRatioCoefficient g D T v hD n d hc.numerator hc.pole).right

/-- A normalized quotient for the two actual graph coefficients. -/
abbrev NormQuotientOfGraphRatios {X Y X₀ Y₀ B₁ B₂ : Scheme.{u}} (U : Y.Opens)
    (g : X ⟶ U.toScheme) [IsFiniteLocallyFree g] (u₁ : X ⟶ X₀) (u₂ : U.toScheme ⟶ Y₀)
    (D₁ : X₀.IdealSheafData) [IsEffectiveCartierDivisor D₁]
    (T₁ : X₀.Modules) [IsInvertibleModule X₀ T₁]
    (n₁ : Γ(Stacks.Divisors.tensorModules (divisorSheaf D₁) T₁, ⊤)) (d₁ : Γ(T₁, ⊤))
    (D₂ : Y₀.IdealSheafData) [IsEffectiveCartierDivisor D₂]
    (T₂ : Y₀.Modules) [IsInvertibleModule Y₀ T₂]
    (n₂ : Γ(Stacks.Divisors.tensorModules (divisorSheaf D₂) T₂, ⊤)) (d₂ : Γ(T₂, ⊤))
    (m₁ : B₁ ⟶ Y) (m₂ : B₂ ⟶ Y) : Prop :=
  ∃ (hn₁ : graphNumeratorGeneratesOnPullback u₁ D₁ T₁ n₁)
    (hn₂ : graphNumeratorGeneratesOnPullback u₂ D₂ T₂ n₂),
    NormQuotientOnBoundaries U g m₁ m₂
      (graphSectionRatioCoefficientOfGenerating u₁ D₁ T₁ n₁ d₁ hn₁)
      (graphSectionRatioCoefficientOfGenerating u₂ D₂ T₂ n₂ d₂ hn₂)

variable {S X Y P C A Z D₁ D₂ : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsSeparated π] [SmoothOfRelativeDimension 1 π]
  (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
  (d₂ : D₂ ⟶ P) (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))
  (c₁ : SectionData q (f ≫ π) j p hB a z s hs H e d₁ hd₁ ha)
  (c₂ : SectionData q π jA (𝟙 X) hA a z z (Category.comp_id z) (IsPullback.of_id_snd)
    e d₂ hd₂ ha)

local notation "b" => (j ≫ f ≫ π)
local notation "zA" => (z ≫ jA)
local notation "F" => (graphProductMap π f j)
local notation "κ" => (graphTargetParameterMap π f j jA p hRet)
local notation "Δ₁" => (Hom.ker (compactificationGraph (f ≫ π) j))
local notation "Δ₂" => (Hom.ker (compactificationGraph π jA))
local notation "mI" => (retainedProductInclusion b π d₂)
local notation "mZ" => (retainedProductInclusion b π zA)

set_option maxHeartbeats 1200000 in
-- The two graph ratios retain their actual generating sections on the whole open.
/-- The original graph ratios give a normalized quotient on a good open. -/
abbrev HasPairedNormUnit : Prop :=
  ∃ (V : (pullback b π : Scheme.{u}).Opens)
    (hV : IsFiniteLocallyFree (pullback.snd F V.ι)),
    @NormQuotientOfGraphRatios (pullback F V.ι) (pullback b π)
      (pullback b (f ≫ π)) (pullback (jA ≫ π) π)
      (pullback b (d₂ ≫ π)) (pullback b (zA ≫ π))
      V (pullback.snd F V.ι) hV (pullback.fst F V.ι) (V.ι ≫ κ)
      Δ₁ (compactificationGraphIdeal_isEffectiveCartierDivisor (f ≫ π) j)
      c₁.T c₁.T_invertible c₁.aS c₁.bS
      Δ₂ (compactificationGraphIdeal_isEffectiveCartierDivisor π jA)
      c₂.T c₂.T_invertible c₂.aS c₂.bS mI mZ

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
