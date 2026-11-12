/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.ClosedTriangle
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.GraphProduct
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionCoefficient

/-!
# Norm association for the two original normalized sections

On an affine chart where both pairs generate, the original graph triangle
computes the norm ideal. Its generators are the coefficients of the two
chosen pairs, using the same actual norm and scalar action.

Adapted from
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Boundary/SectionPairNormIdeal.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
open Stacks.SheafOfModules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

local instance {U : Scheme.{u}} (L : U.Modules) [hL : IsInvertibleModule U L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible U.sheaf.obj U.ringCatSheaf.property L := hL

local instance {U : Scheme.{u}} (D : U.IdealSheafData) [IsEffectiveCartierDivisor D] :
    IsInvertibleModule U (divisorSheaf D) := Stacks.Divisors.isInvertible_divisorSheaf D

variable {S P C X Y W : Scheme.{u}} (π : P ⟶ S) [IsSeparated π] (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (h : j ≫ f = p ≫ jA)
  (w : W ⟶ pullback (j ≫ f ≫ π) π) [IsAffine W]

local notation "D₁" => (Hom.ker (compactificationGraph (f ≫ π) j))
local notation "D₂" => (Hom.ker (compactificationGraph π jA))
local notation "F" => (graphProductMap π f j)
local notation "w₁" => (pullback.fst F w)
local notation "w₂" => (w ≫ graphTargetParameterMap π f j jA p h)
local notation "g" => (pullback.snd F w)

omit [IsFinite f] [IsAffine W] in
/-- The target graph pulled to a flat chart of the actual parameter product
is the Cartier graph of the original retained map. -/
theorem isEffectiveCartierDivisor_targetGraph_on_chart
    [SmoothOfRelativeDimension 1 π] [Flat w] :
    IsEffectiveCartierDivisor ((D₂).comap w₂) := by
  rw [IdealSheafData.comap_comp, ← targetNormGraph_ker π f j jA p h]
  exact isPullbackDefined_of_flat w _
    (inferInstanceAs (IsEffectiveCartierDivisor
      (relativeGraphIdeal (j ≫ f ≫ π) π (j ≫ f) (Category.assoc j f π))))

variable [hD₁ : IsEffectiveCartierDivisor
    (Scheme.Hom.ker (compactificationGraph (f ≫ π) j))]
  [hD₂ : IsEffectiveCartierDivisor (Scheme.Hom.ker (compactificationGraph π jA))]
  (T₁ : (pullback (j ≫ f ≫ π) (f ≫ π)).Modules)
  [IsInvertibleModule (pullback (j ≫ f ≫ π) (f ≫ π)) T₁]
  (T₂ : (pullback (jA ≫ π) π).Modules)
  [IsInvertibleModule (pullback (jA ≫ π) π) T₂]

local notation "L₁" => (Stacks.Divisors.tensorModules (divisorSheaf D₁) T₁)
local notation "L₂" => (Stacks.Divisors.tensorModules (divisorSheaf D₂) T₂)

local instance : IsInvertibleModule (pullback (j ≫ f ≫ π) (f ≫ π)) L₁ :=
  @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _ (divisorSheaf D₁) T₁
    (@Stacks.Divisors.isInvertible_divisorSheaf _ D₁ hD₁) inferInstance

local instance : IsInvertibleModule (pullback (jA ≫ π) π) L₂ :=
  @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _ (divisorSheaf D₂) T₂
    (@Stacks.Divisors.isInvertible_divisorSheaf _ D₂ hD₂) inferInstance

local instance : IsInvertibleModule (pullback F w) ((Modules.pullback w₁).obj L₁) :=
  Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback w₁ L₁

local instance : IsInvertibleModule W ((Modules.pullback w₂).obj L₂) :=
  Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback w₂ L₂

include hD₁ hD₂ in
/-- The two original graph coefficients are associated by the actual norm.
Freeness refers only to the full affine inverse image of this target chart. -/
theorem exists_graphSectionRatio_norm_associated
    (a₁ : Γ(L₁, ⊤)) (b₁ : Γ(T₁, ⊤))
    (a₂ : Γ(L₂, ⊤)) (b₂ : Γ(T₂, ⊤))
    (ha₁ : zeroScheme _ ((Modules.pullback w₁).obj L₁) (pullbackGlobalSections w₁ L₁ a₁) = ⊤)
    (hb₁ : zeroScheme _ ((Modules.pullback w₁).obj T₁) (pullbackGlobalSections w₁ T₁ b₁) = ⊤)
    (ha₂ : zeroScheme _ ((Modules.pullback w₂).obj L₂) (pullbackGlobalSections w₂ L₂ a₂) = ⊤)
    (hb₂ : zeroScheme _ ((Modules.pullback w₂).obj T₂) (pullbackGlobalSections w₂ T₂ b₂) = ⊤)
    (hCartier : IsEffectiveCartierDivisor ((D₂).comap w₂)) :
    let : Algebra Γ(W, ⊤) Γ((pullback F w : Scheme.{u}), ⊤) := (g).appTop.hom.toAlgebra
    ∀ [Module.Free Γ(W, ⊤) Γ((pullback F w : Scheme.{u}), ⊤)], ∃ μ : Γ(W, ⊤)ˣ,
      Algebra.norm Γ(W, ⊤) (graphSectionRatioCoefficient w₁ D₁ T₁ a₁ b₁ ha₁) =
        (μ : Γ(W, ⊤)) * graphSectionRatioCoefficient w₂ D₂ T₂ a₂ b₂ ha₂ := by
  dsimp only
  let : Algebra Γ(W, ⊤) Γ(pullback F w, ⊤) := (g).appTop.hom.toAlgebra
  intro hfree
  let : Module.Free Γ(W, ⊤) Γ(pullback F w, ⊤) := hfree
  let : IsAffine (pullback F w) := isAffine_of_isAffineHom g
  let i₁ := pullback.snd (compactificationGraph (f ≫ π) j) w₁
  let i₂ := (graphNormChartDomainIso π f j w).hom ≫ pullback.snd (targetNormGraph π f j) w
  have hi : i₁ ≫ g = i₂ := graphNormChart_triangle π f j w
  have hk₁ : i₁.ker = (D₁).comap w₁ :=
    ker_eq_comap_of_cartesian (IsPullback.of_hasPullback
      (compactificationGraph (f ≫ π) j) w₁).flip
  have hk₂ : i₂.ker = (D₂).comap w₂ := by
    change ((graphNormChartDomainIso π f j w).hom ≫
      pullback.snd (targetNormGraph π f j) w).ker = _
    rw [Hom.ker_comp_of_isIso, ker_eq_comap_of_cartesian
      (IsPullback.of_hasPullback (targetNormGraph π f j) w).flip,
      targetNormGraph_ker π f j jA p h, IdealSheafData.comap_comp]
  have hs := Hom.span_norm_eq_of_affineClosedTriangle g i₁ i₂ hi
    (graphSectionRatioCoefficient w₁ D₁ T₁ a₁ b₁ ha₁)
    (graphSectionRatioCoefficient w₂ D₂ T₂ a₂ b₂ ha₂)
    (by rw [hk₁]; exact graphSectionRatioCoefficient_ideal w₁ D₁ T₁ a₁ b₁ ha₁ hb₁)
    (by rw [hk₂]; exact graphSectionRatioCoefficient_ideal w₂ D₂ T₂ a₂ b₂ ha₂ hb₂)
  let c₁ := Algebra.norm Γ(W, ⊤) (graphSectionRatioCoefficient w₁ D₁ T₁ a₁ b₁ ha₁)
  let c₂ := graphSectionRatioCoefficient w₂ D₂ T₂ a₂ b₂ ha₂
  have hs' : Ideal.span {c₁} = Ideal.span {c₂} := hs
  have hc₂ : _root_.IsRegular c₂ := isRegular_iff_mem_nonZeroDivisors.2
    (Stacks.Divisors.Eta.mem_nonZeroDivisors_of_ideal_eq_span _ hCartier
      ⟨⊤, isAffineOpen_top W⟩ (graphSectionRatioCoefficient_ideal w₂ D₂ T₂ a₂ b₂ ha₂ hb₂))
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp
    (hs' ▸ Ideal.subset_span (Set.mem_singleton c₁))
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp
    (hs'.symm ▸ Ideal.subset_span (Set.mem_singleton c₂))
  have huv : u * v = 1 := hc₂.left (by
    calc
      c₂ * (u * v) = (c₂ * u) * v := (mul_assoc _ _ _).symm
      _ = c₁ * v := by rw [← hu]
      _ = c₂ := hv.symm
      _ = c₂ * 1 := (mul_one _).symm)
  let μ : Γ(W, ⊤)ˣ := ⟨u, v, huv, by simpa only [mul_comm] using huv⟩
  refine ⟨μ, ?_⟩
  change c₁ = u * c₂
  exact hu.trans (mul_comm c₂ u)

end AlgebraicGeometry.Scheme.RelativeCurvePencil
