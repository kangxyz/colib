/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SerreSections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.TwoSourceBoundaryMatching
/-! # The actual section data over an arbitrary affine Noetherian relative base -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable {S X C Y A B Z D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range z))
local notation "XA" => pullback (j ≫ π) π
local notation "XN" => pullback (a ≫ q) π
local notation "F" => divisorSheaf (Scheme.Hom.ker (compactificationGraph π j))
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "iN" => psiBoundaryInclusion (q) π j p hq a
  (z) s hs d

/-- The actual global choices produced by Serre on the two distinct unchanged sources. -/
structure SectionData where
  T : (XA).Modules
  T_invertible : IsInvertibleModule XA T
  N : (XN).Modules
  N_invertible : IsInvertibleModule XN N
  aS : Γ(tensorModules F T, ⊤)
  bS : Γ(T, ⊤)
  nS : Γ(N, ⊤)
  dS : Γ(N, ⊤)
  normalized : (fixedFactorBoundaryIso iA F T
    (fullGraphFrame q π j p hq z s hs H e d hd)).hom.app ⊤
      (pullbackGlobalSections iA _ aS) = pullbackGlobalSections iA T bS
  scalar : pullbackGlobalSections iN N nS =
    fullCorrectionCoordinate q π z e d a ha • pullbackGlobalSections iN N dS
  numerator_zero :
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback iA).obj (tensorModules F T))
      (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA iA
        (tensorModules F T)
        (@Stacks.Chow.TensorZeroScheme.isInvertible_tensorSheaf XA F T
          (inferInstanceAs (IsInvertibleModule XA F)) T_invertible))
      (pullbackGlobalSections iA _ aS) = ⊤
  denominator_zero :
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback iA).obj T)
      (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XA iA T T_invertible)
      (pullbackGlobalSections iA T bS) = ⊤
  correctionNumerator_zero :
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback iN).obj N)
      (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN iN N N_invertible)
      (pullbackGlobalSections iN N nS) = ⊤
  correctionDenominator_zero :
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback iN).obj N)
      (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ XN iN N N_invertible)
      (pullbackGlobalSections iN N dS) = ⊤

omit [IsSeparated π] in
/-- Actual relative Serre produces both whole-source pairs from the constructed
intermediate frames. The final refinement theorem must supply these frames,
not ask for them as additional geometric input. -/
theorem nonempty_sectionData [IsAffine S] [IsLocallyNoetherian S]
    [IsAffine Y] [IsAffine A] [hProper : IsProper π] [IsOpenImmersion a]
    [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
    (L : C.Modules) [IsInvertibleModule C L] (hL : IsAmple C L)
    (eD : (Modules.pullback d).obj L ≅ SheafOfModules.unit D.ringCatSheaf)
    (eZ : (Modules.pullback (s ≫ j)).obj L ≅ SheafOfModules.unit Z.ringCatSheaf) :
    letI : IsSeparated π := hProper.toIsSeparated
    Nonempty (SectionData q π j p hq a z s hs H e d hd ha) := by
  obtain ⟨m, hm⟩ := exists_eventually_relative_normalized_sections
    q π j p hq z s hs H e d hd L hL eD eZ
  obtain ⟨n, hn⟩ := exists_eventually_relative_scalar_sections
    q π j p hq z s hs e d hd L hL eD eZ a ha
  obtain ⟨aS, bS, hA, haS, hbS⟩ := hm m le_rfl
  obtain ⟨nS, dS, hN, hnS, hdS⟩ := hn n le_rfl
  exact ⟨{
    T := tensorPowModule XA ((Modules.pullback (pullback.snd (j ≫ π) π)).obj L) (m : ℤ)
    T_invertible := inferInstance
    N := tensorPowModule XN ((Modules.pullback (pullback.snd (a ≫ q) π)).obj L) (n : ℤ)
    N_invertible := inferInstance
    aS := aS
    bS := bS
    nS := nS
    dS := dS
    normalized := hA
    scalar := hN
    numerator_zero := haS
    denominator_zero := hbS
    correctionNumerator_zero := hnS
    correctionDenominator_zero := hdS }⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
