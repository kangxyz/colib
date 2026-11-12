/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionData
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedBoundaryCover
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedFamilyRestriction
/-! # The literal whole finite-flat family over a general relative base -/

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
  {k : Type u} [Field k] (t : S ⟶ Spec (.of k))
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

/-- The literal common numerator line, retaining its original pullback bracketing. -/
def commonLine : (commonAmbient π j α).Modules :=
  tensorModules ((Modules.pullback gA).obj (tensorModules F c.T)) ((Modules.pullback gN).obj c.N)

/-- The literal graph-times-poles start; no expected zero ideal is substituted. -/
def commonStart : Γ(c.commonLine α β h, ⊤) :=
  tensorSection _ _ ⊤
    (pullbackGlobalSections gA _ (tensorSection F c.T ⊤ σ c.bS))
    (pullbackGlobalSections gN c.N c.dS)

/-- The literal product of the two independently generated numerators. -/
def commonEnd : Γ(c.commonLine α β h, ⊤) :=
  tensorSection _ _ ⊤ (pullbackGlobalSections gA _ c.aS) (pullbackGlobalSections gN c.N c.nS)

/-- The actual common pole line. -/
def commonPoleLine : (commonAmbient π j α).Modules :=
  tensorModules ((Modules.pullback gA).obj c.T) ((Modules.pullback gN).obj c.N)

/-- The actual product of the original denominator sections. -/
def commonPole : Γ(c.commonPoleLine α β h, ⊤) :=
  tensorSection _ _ ⊤ (pullbackGlobalSections gA c.T c.bS) (pullbackGlobalSections gN c.N c.dS)

private theorem graphCoefficient_invertible : IsInvertibleModule XA (tensorModules F c.T) :=
  @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F c.T
    (inferInstanceAs (IsInvertibleModule XA F)) c.T_invertible

/-- The actual common numerator line is invertible. -/
theorem commonLine_invertible :
    IsInvertibleModule (commonAmbient π j α) (c.commonLine α β h) :=
  @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _
    ((Modules.pullback gA).obj (tensorModules F c.T)) ((Modules.pullback gN).obj c.N)
    (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA gA
      (tensorModules F c.T) (c.graphCoefficient_invertible))
    (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN gN c.N c.N_invertible)

/-- The actual common pole line is invertible. -/
theorem commonPoleLine_invertible :
    IsInvertibleModule (commonAmbient π j α) (c.commonPoleLine α β h) :=
  @Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf _
    ((Modules.pullback gA).obj c.T) ((Modules.pullback gN).obj c.N)
    (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA gA c.T c.T_invertible)
    (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN gN c.N c.N_invertible)

/-- Invertibility on an actual pullback of the common numerator line. -/
theorem commonLine_pullback_invertible {Z' : Scheme.{u}} (j' : Z' ⟶ commonAmbient π j α) :
    IsInvertibleModule Z' ((Modules.pullback j').obj (c.commonLine α β h)) :=
  @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ j' _
    (c.commonLine_invertible α β h)

/-- Invertibility on an actual pullback of the common pole line. -/
theorem commonPoleLine_pullback_invertible {Z' : Scheme.{u}} (j' : Z' ⟶ commonAmbient π j α) :
    IsInvertibleModule Z' ((Modules.pullback j').obj (c.commonPoleLine α β h)) :=
  @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ j' _
    (c.commonPoleLine_invertible α β h)

/-- The normalization equations, and not any homotopy hypothesis, imply whole-boundary matching. -/
theorem commonEnd_boundary_eq_start :
    pullbackGlobalSections i _ (c.commonEnd α β h) =
      pullbackGlobalSections i _ (c.commonStart α β h) :=
by
  apply boundary_tensor_matching_two_sources gA gN iA iN i
    (commonBoundaryToLambda π j α s d)
    (commonBoundaryToPsi q π j p hq a α β h z s hs d)
    (commonBoundaryToLambda_inclusion π j α s d).symm
    (commonBoundaryToPsi_inclusion q π j p hq a α β h z s hs d).symm
    F c.T c.N (fullGraphFrame q π j p hq z s hs H e d hd)
    σ c.aS c.bS c.nS c.dS _ c.normalized c.scalar
  exact commonBoundaryCoordinate_eq q π j p hq z s hs H e d hd a ha α β h

/-- The actual numerator endpoint has no zeros anywhere on the common boundary. -/
theorem commonEnd_boundary_zero :
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback i).obj (c.commonLine α β h))
      (c.commonLine_pullback_invertible α β h i)
      (pullbackGlobalSections i _ (c.commonEnd α β h)) = ⊤ := by
  let := c.T_invertible
  let := c.N_invertible
  let := c.graphCoefficient_invertible
  let : IsInvertibleModule _ ((Modules.pullback gA).obj (tensorModules F c.T)) :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA gA
      (tensorModules F c.T) c.graphCoefficient_invertible
  let : IsInvertibleModule _ ((Modules.pullback gN).obj c.N) :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN gN c.N c.N_invertible
  exact zeroScheme_boundary_tensorSection_eq_top i
    ((Modules.pullback gA).obj (tensorModules F c.T)) ((Modules.pullback gN).obj c.N)
    (pullbackGlobalSections gA _ c.aS) (pullbackGlobalSections gN c.N c.nS)
    (zeroScheme_boundary_after_sourceChange gA iA i
      (commonBoundaryToLambda π j α s d) (commonBoundaryToLambda_inclusion π j α s d).symm
      _ c.aS c.numerator_zero)
    (zeroScheme_boundary_after_sourceChange gN iN i
      (commonBoundaryToPsi q π j p hq a α β h z s hs d)
      (commonBoundaryToPsi_inclusion q π j p hq a α β h z s hs d).symm
      _ c.nS c.correctionNumerator_zero)

/-- The start is nonvanishing on the whole boundary as a consequence of actual matching. -/
theorem commonStart_boundary_zero :
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback i).obj (c.commonLine α β h))
      (c.commonLine_pullback_invertible α β h i)
      (pullbackGlobalSections i _ (c.commonStart α β h)) = ⊤ :=
  (congrArg (@AlgebraicGeometry.zeroScheme _ ((Modules.pullback i).obj (c.commonLine α β h))
    (c.commonLine_pullback_invertible α β h i)) (c.commonEnd_boundary_eq_start α β h)).symm.trans
      (c.commonEnd_boundary_zero α β h)

/-- The denominator product also has no zeros on the entire common boundary. -/
theorem commonPole_boundary_zero :
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback i).obj (c.commonPoleLine α β h))
      (c.commonPoleLine_pullback_invertible α β h i)
      (pullbackGlobalSections i _ (c.commonPole α β h)) = ⊤ := by
  let := c.T_invertible
  let := c.N_invertible
  let : IsInvertibleModule _ ((Modules.pullback gA).obj c.T) :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA gA c.T c.T_invertible
  let : IsInvertibleModule _ ((Modules.pullback gN).obj c.N) :=
    @Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN gN c.N c.N_invertible
  exact zeroScheme_boundary_tensorSection_eq_top i
    ((Modules.pullback gA).obj c.T) ((Modules.pullback gN).obj c.N)
    (pullbackGlobalSections gA c.T c.bS) (pullbackGlobalSections gN c.N c.dS)
    (zeroScheme_boundary_after_sourceChange gA iA i
      (commonBoundaryToLambda π j α s d) (commonBoundaryToLambda_inclusion π j α s d).symm
      _ c.bS c.denominator_zero)
    (zeroScheme_boundary_after_sourceChange gN iN i
      (commonBoundaryToPsi q π j p hq a α β h z s hs d)
      (commonBoundaryToPsi_inclusion q π j p hq a α β h z s hs d).symm
      _ c.dS c.correctionDenominator_zero)

variable [IsAffine S] [IsAffine B] {V : Scheme.{u}} [IsAffine V]
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
  (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))

local notation "r" => retainedProductInclusion qB π v

omit [IsSeparated π] in
include hc in
/-- The full actual polynomial family is finite flat, with its literal retained
source map. Its boundary frame was constructed from the generated sections. -/
theorem retainedFamily_finite_flat [hProper : IsProper π]
    (c :
      letI : IsSeparated π := hProper.toIsSeparated
      SectionData q π j p hq a z s hs H e d hd ha) :
    let familyMap := @PolynomialSectionPencil.familySource k
      (inferInstanceAs (CommRing k)) B (qB ≫ t)
      (retainedProduct qB π v) (pullback.fst qB (v ≫ π))
      ((Modules.pullback r).obj (c.commonLine α β h)) (c.commonLine_pullback_invertible α β h r)
      (pullbackGlobalSections r _ (c.commonStart α β h))
      (pullbackGlobalSections r _ (c.commonEnd α β h))
    IsFinite familyMap ∧ Flat familyMap := by
  let := c.commonLine_invertible α β h
  let := c.commonLine_pullback_invertible α β h i
  let := retainedProduct_affine qB π v
  let := retainedProduct_smooth qB π v
  let e := frameOfZeroSchemeTop _ (pullbackGlobalSections i _ (c.commonStart α β h))
    (c.commonStart_boundary_zero α β h)
  have hf := PolynomialSectionPencil.finite_flat_retainedFamily_of_boundary_frame r (qB ≫ t)
    (pullback.fst qB π) i (c.commonLine α β h) (c.commonStart α β h) (c.commonEnd α β h)
    (commonBoundary_retained_cover π v j α s d hc)
    (c.commonEnd_boundary_eq_start α β h).symm e.hom
    (frameOfZeroSchemeTop_section _ _ _)
  let L := (Modules.pullback r).obj (c.commonLine α β h)
  let := c.commonLine_pullback_invertible α β h r
  let s₀ := pullbackGlobalSections r _ (c.commonStart α β h)
  let s₁ := pullbackGlobalSections r _ (c.commonEnd α β h)
  exact (congrArg (fun p : retainedProduct qB π v ⟶ B =>
      IsFinite (PolynomialSectionPencil.familySource (qB ≫ t) p L s₀ s₁) ∧
        Flat (PolynomialSectionPencil.familySource (qB ≫ t) p L s₀ s₁))
    (retainedProductInclusion_fst qB π v)).mp hf

omit [IsSeparated π] in
include hc in
/-- The constant pole's entire zero scheme is likewise finite and relative
Cartier; its constant polynomial family then follows by ConstantFamily. -/
theorem retainedPole_finite_relativeCartier [hProper : IsProper π]
    (c :
      letI : IsSeparated π := hProper.toIsSeparated
      SectionData q π j p hq a z s hs H e d hd ha) :
    let Z := @AlgebraicGeometry.zeroScheme _ ((Modules.pullback r).obj (c.commonPoleLine α β h))
      (c.commonPoleLine_pullback_invertible α β h r)
      (pullbackGlobalSections r _ (c.commonPole α β h))
    IsFinite (Z.subschemeι ≫ pullback.fst qB (v ≫ π)) ∧
      IsRelativeEffectiveCartierDivisor (pullback.fst qB (v ≫ π)) Z := by
  let := c.commonPoleLine_invertible α β h
  let := retainedProduct_affine qB π v
  let := retainedProduct_smooth qB π v
  have hp := finite_relativeCartier_of_boundary_zero i (pullback.fst qB π) r
    (commonBoundary_retained_cover π v j α s d hc)
    (c.commonPoleLine α β h) (c.commonPole α β h) (c.commonPole_boundary_zero α β h)
  simpa only [retainedProductInclusion_fst] using hp

end SectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
