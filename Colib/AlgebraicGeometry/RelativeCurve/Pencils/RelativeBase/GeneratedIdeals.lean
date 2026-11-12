/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.GeneratedPencil
/-! # Exact whole relative support data from the generated section pairs -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

local instance (X : Scheme.{u}) (M : X.Modules) [hM : IsInvertibleModule X M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M := hM

variable {S X C Y A B Z D : Scheme.{u}}
  {q : X ⟶ S} [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  {π : C ⟶ S} [IsSeparated π]
  {j : Y ⟶ C} [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  {p : Y ⟶ X} {hq : j ≫ π = p ≫ q} {a : A ⟶ X}
  {z : Z ⟶ X} {s : Z ⟶ Y} {hs : s ≫ p = z} {H : IsPullback s (𝟙 Z) p z}
  {e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf}
  {d : D ⟶ C} {hd : Disjoint (Set.range j) (Set.range d)}
  {ha : Disjoint (Set.range a) (Set.range z)}

variable (α : B ⟶ Y) (β : B ⟶ A) (h : α ≫ p = β ≫ a)
local notation "XA" => pullback (j ≫ π) π
local notation "XN" => pullback (a ≫ q) π
local notation "F" => divisorSheaf (Scheme.Hom.ker (compactificationGraph π j))
local notation "σ" => divisorSheafGlobalSection (Scheme.Hom.ker (compactificationGraph π j))
local notation "gA" => commonToLambda π j α
local notation "gN" => commonToPsi (q) π j p hq a α β h
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "iN" => psiBoundaryInclusion (q) π j p hq a
  (z) s hs d
local notation "i" => commonBoundaryInclusion π j α s d
local notation "qB" => commonProjection π j α

namespace SectionData

variable (c : SectionData q π j p hq a z s hs H e d hd ha)

/-- The actual product of numerators, on two different source products. -/
theorem commonEnd_zeroScheme :
    letI := c.T_invertible
    letI := c.N_invertible
    letI : IsInvertibleModule XA (tensorModules F c.T) :=
      @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
        (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
    @AlgebraicGeometry.zeroScheme _ (c.commonLine α β h) (c.commonLine_invertible α β h)
      (c.commonEnd α β h) =
      (zeroScheme _ (tensorModules F c.T) c.aS).comap gA *
        (zeroScheme _ c.N c.nS).comap gN := by
  let := c.T_invertible
  let := c.N_invertible
  let hTensor : IsInvertibleModule XA (tensorModules F c.T) :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
      (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
  let := hTensor
  let MA := (Modules.pullback gA).obj (tensorModules F c.T)
  let MN := (Modules.pullback gN).obj c.N
  let hMA : IsInvertibleModule (commonAmbient π j α) MA :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA gA
      (tensorModules F c.T) hTensor
  let hMN : IsInvertibleModule (commonAmbient π j α) MN :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN gN c.N c.N_invertible
  have hProduct := @zeroScheme_tensorSection_eq_mul _ MA MN hMA hMN
    (pullbackGlobalSections gA (tensorModules F c.T) c.aS) (pullbackGlobalSections gN c.N c.nS)
  exact hProduct.trans (congrArg₂ (· * ·)
    (zeroScheme_pullback gA (tensorModules F c.T) c.aS) (zeroScheme_pullback gN c.N c.nS))

/-- The graph-times-poles start has its full original graph ideal, not merely
its reduced support or divisor class. -/
theorem commonStart_zeroScheme : letI := c.T_invertible; letI := c.N_invertible
    @AlgebraicGeometry.zeroScheme _ (c.commonLine α β h) (c.commonLine_invertible α β h)
      (c.commonStart α β h) =
      ((compactificationGraph π j).ker.comap gA * (zeroScheme _ c.T c.bS).comap gA) *
        (zeroScheme _ c.N c.dS).comap gN := by
  let := c.T_invertible
  let := c.N_invertible
  let hTensor : IsInvertibleModule XA (tensorModules F c.T) :=
    @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
      (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible
  let := hTensor
  let MA := (Modules.pullback gA).obj (tensorModules F c.T)
  let MN := (Modules.pullback gN).obj c.N
  let hMA : IsInvertibleModule (commonAmbient π j α) MA :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA gA
      (tensorModules F c.T) hTensor
  let hMN : IsInvertibleModule (commonAmbient π j α) MN :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN gN c.N c.N_invertible
  let G := (compactificationGraph π j).ker
  let pA := tensorSection F c.T ⊤ σ c.bS
  have hInner : zeroScheme XA (tensorModules F c.T) pA = G * zeroScheme XA c.T c.bS :=
    (zeroScheme_tensorSection_eq_mul F c.T σ c.bS).trans
      (congrArg (fun I : (XA).IdealSheafData => I * zeroScheme XA c.T c.bS)
        (zeroScheme_canonicalSection G))
  have hA := (zeroScheme_pullback gA (tensorModules F c.T) pA).trans
    ((congrArg (fun I : (XA).IdealSheafData => I.comap gA) hInner).trans
      (Stacks.IdealSheaf.comap_mul G (zeroScheme XA c.T c.bS) gA))
  have hProduct := @zeroScheme_tensorSection_eq_mul _ MA MN hMA hMN
    (pullbackGlobalSections gA _ pA) (pullbackGlobalSections gN c.N c.dS)
  exact hProduct.trans (congrArg₂ (· * ·) hA (zeroScheme_pullback gN c.N c.dS))

/-- The actual denominator product retains both independent source changes. -/
theorem commonPole_zeroScheme : letI := c.T_invertible; letI := c.N_invertible
    @AlgebraicGeometry.zeroScheme _ (c.commonPoleLine α β h) (c.commonPoleLine_invertible α β h)
      (c.commonPole α β h) =
      (zeroScheme _ c.T c.bS).comap gA * (zeroScheme _ c.N c.dS).comap gN := by
  let := c.T_invertible
  let := c.N_invertible
  let MA := (Modules.pullback gA).obj c.T
  let MN := (Modules.pullback gN).obj c.N
  let hMA : IsInvertibleModule (commonAmbient π j α) MA :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA gA
      c.T c.T_invertible
  let hMN : IsInvertibleModule (commonAmbient π j α) MN :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN gN c.N c.N_invertible
  have hProduct := @zeroScheme_tensorSection_eq_mul _ MA MN hMA hMN
    (pullbackGlobalSections gA c.T c.bS) (pullbackGlobalSections gN c.N c.dS)
  exact hProduct.trans (congrArg₂ (· * ·)
    (zeroScheme_pullback gA c.T c.bS) (zeroScheme_pullback gN c.N c.dS))

end SectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
