/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.SectionData

/-!
# Original-target sections on the whole infinity schemes

The prescribed normalizations give the actual restrictions of the two pencils
on the whole infinity schemes. The section comparisons precede construction of
any finite correspondence or transfer action.

The comparisons occur in
`Motivic.Transfers.Presheaf.Actions.Pencils.Restriction` and
`Motivic.Transfers.Presheaf.Actions.Pencils.Correction`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

private theorem pullbackGlobalSections_eq_of_comp_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {i : X ⟶ Z} (hi : f ≫ g = i)
    (M : Z.Modules) (a b : Γ(M, ⊤))
    (h : pullbackGlobalSections f ((Modules.pullback g).obj M) (pullbackGlobalSections g M a) =
      pullbackGlobalSections f ((Modules.pullback g).obj M) (pullbackGlobalSections g M b)) :
    pullbackGlobalSections i M a = pullbackGlobalSections i M b := by
  subst i
  have h' := congrArg (fun x =>
    Modules.Hom.app (X := X) ((Modules.pullbackComp f g).app M).hom ⊤ x) h
  exact (SectionsEqualizer.pullbackGlobalSections_comp f g M a).symm.trans
    (h'.trans (SectionsEqualizer.pullbackGlobalSections_comp f g M b))

variable {S X C Y A Z D : Scheme.{u}}
  {q : X ⟶ S} [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  {π : C ⟶ S} [IsSeparated π]
  {j : Y ⟶ C} [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  {p : Y ⟶ X} {hq : j ≫ π = p ≫ q} {a : A ⟶ X}
  {z : Z ⟶ X} {s : Z ⟶ Y} {hs : s ≫ p = z} {H : IsPullback s (𝟙 Z) p z}
  {e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf}
  {d : D ⟶ C} {hd : Disjoint (Set.range j) (Set.range d)}
  {ha : Disjoint (Set.range a) (Set.range z)}

namespace SectionData

variable (c : SectionData q π j p hq a z s hs H e d hd ha)

section Graph

local notation "b" => j ≫ π
local notation "G" => Scheme.Hom.ker (compactificationGraph π j)
local notation "F" => divisorSheaf G
local notation "σ" => divisorSheafGlobalSection G
local notation "iA" => fullGraphBoundaryMap π j s d
local notation "i∞" => infinityProductMap π j d
local notation "K" => pullback (pullback.snd b π) d ⨿ pullback b (s ≫ j ≫ π)
local notation "iL" => (coprod.inl : pullback (pullback.snd b π) d ⟶ K)

omit [IsSeparated π] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)] in
private theorem lambda_inl_boundary : iL ≫ iA = i∞ := by
  simp only [fullGraphBoundaryMap, coprod.inl_desc]

omit [IsSeparated π] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)] in
/-- Absence of zeros on the whole graph boundary restricts to infinity. -/
theorem lambda_infinity_zero_of_boundary_zero (M : (pullback b π).Modules)
    [IsInvertibleModule _ M] (s₁ : Γ(M, ⊤))
    (h : zeroScheme _ ((Modules.pullback iA).obj M) (pullbackGlobalSections iA M s₁) = ⊤) :
    zeroScheme _ ((Modules.pullback i∞).obj M) (pullbackGlobalSections i∞ M s₁) = ⊤ := by
  let I := zeroScheme (pullback b π) M s₁
  have hA : I.comap iA = ⊤ := (zeroScheme_pullback iA M s₁).symm.trans h
  exact (zeroScheme_pullback i∞ M s₁).trans (by
    change I.comap i∞ = ⊤
    rw [← lambda_inl_boundary (π := π) (j := j) (s := s) (d := d),
      Scheme.IdealSheafData.comap_comp, hA, Scheme.IdealSheafData.comap_top])

/-- The first endpoint is the native graph section tensored with the same pole. -/
def lambdaStartSection : Γ(tensorModules F c.T, ⊤) := tensorSection F c.T ⊤ σ c.bS

/-- The graph-times-pole section agrees with the prescribed numerator on the
entire infinity scheme. -/
theorem lambdaSections_infinity_eq :
    pullbackGlobalSections i∞ _ c.lambdaStartSection = pullbackGlobalSections i∞ _ c.aS := by
  let E := fullGraphFrame q π j p hq z s hs H e d hd
  let f := Modules.Hom.app (X := K) (fixedFactorBoundaryIso iA F c.T E).hom ⊤
  have hσ : f (pullbackGlobalSections iA _ c.lambdaStartSection) =
      fullGraphCoordinate q π j p hq z s hs H e d hd • pullbackGlobalSections iA c.T c.bS := by
    change Modules.Hom.app (X := K) (frameTensorContraction _ _ E).hom ⊤
      (Modules.Hom.app (X := K)
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso iA F c.T).hom ⊤
        (pullbackGlobalSections iA _ (tensorSection F c.T ⊤ σ c.bS))) = _
    rw [pullbackTensorIso_tensorSection]
    exact frameTensorContraction_tensorSection _ _ _ _ _
  have h0 : pullbackGlobalSections iA _ c.lambdaStartSection =
      fullGraphCoordinate q π j p hq z s hs H e d hd • pullbackGlobalSections iA _ c.aS := by
    have hNormalized : f (pullbackGlobalSections iA _ c.aS) = pullbackGlobalSections iA c.T c.bS :=
      c.normalized
    apply (ConcreteCategory.bijective_of_isIso f).injective
    change f (pullbackGlobalSections iA _ c.lambdaStartSection) =
      Modules.Hom.app (X := K) (fixedFactorBoundaryIso iA F c.T E).hom ⊤
        (fullGraphCoordinate q π j p hq z s hs H e d hd • pullbackGlobalSections iA _ c.aS)
    rw [Modules.Hom.app_smul]
    exact hσ.trans (congrArg (fun x => fullGraphCoordinate q π j p hq z s hs H e d hd • x)
      hNormalized.symm)
  have h1 :
      pullbackGlobalSections iL ((Modules.pullback iA).obj (tensorModules F c.T))
          (pullbackGlobalSections iA _ c.lambdaStartSection) =
        pullbackGlobalSections iL ((Modules.pullback iA).obj (tensorModules F c.T))
          (pullbackGlobalSections iA _ c.aS) := by
    rw [h0, SectionsEqualizer.pullbackGlobalSections_smul, fullGraphCoordinate_infinity, one_smul]
  exact pullbackGlobalSections_eq_of_comp_eq iL iA
    (lambda_inl_boundary (π := π) (j := j) (s := s) (d := d))
    (tensorModules F c.T) c.lambdaStartSection c.aS h1

end Graph

section Correction

local notation "b" => a ≫ q
local notation "iN" => psiBoundaryInclusion q π j p hq a z s hs d
local notation "K" => pullback (pullback.snd b π) d ⨿ pullback b (z ≫ q)
local notation "iL" => (coprod.inl : pullback (pullback.snd b π) d ⟶ K)
local notation "i∞" => pullback.fst (pullback.snd b π) d

omit [IsSeparated q] [SmoothOfRelativeDimension 1 q] [IsSeparated π]
  [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)] in
private theorem correction_inl_boundary : iL ≫ iN = i∞ := by
  simp only [psiBoundaryInclusion, coprod.inl_desc]

/-- The two prescribed correction sections restrict to the same section on the
entire infinity scheme. -/
theorem correctionSections_infinity_eq :
    pullbackGlobalSections i∞ c.N c.nS = pullbackGlobalSections i∞ c.N c.dS := by
  have hn :
      pullbackGlobalSections iL ((Modules.pullback iN).obj c.N)
          (pullbackGlobalSections iN c.N c.nS) =
        pullbackGlobalSections iL ((Modules.pullback iN).obj c.N)
          (pullbackGlobalSections iN c.N c.dS) := by
    rw [c.scalar, SectionsEqualizer.pullbackGlobalSections_smul,
      fullCorrectionCoordinate_infinity, one_smul]
  exact pullbackGlobalSections_eq_of_comp_eq iL iN
    (correction_inl_boundary (q := q) (π := π) (j := j) (p := p) (hq := hq)
      (a := a) (z := z) (s := s) (hs := hs) (d := d)) c.N c.nS c.dS hn

/-- The prescribed denominator is nowhere zero on the same whole infinity. -/
theorem correctionDenominator_infinity_zero :
    @AlgebraicGeometry.zeroScheme _ ((Modules.pullback i∞).obj c.N)
      (@Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback _ _ i∞
        c.N c.N_invertible) (pullbackGlobalSections i∞ c.N c.dS) = ⊤ := by
  let := c.N_invertible
  let I := zeroScheme (pullback b π) c.N c.dS
  have hComp : iL ≫ iN = i∞ :=
    correction_inl_boundary (q := q) (π := π) (j := j) (p := p) (hq := hq)
      (a := a) (z := z) (s := s) (hs := hs) (d := d)
  have hN : I.comap iN = ⊤ :=
    (zeroScheme_pullback iN c.N c.dS).symm.trans c.correctionDenominator_zero
  exact (zeroScheme_pullback i∞ c.N c.dS).trans (by
    change I.comap i∞ = ⊤
    rw [← hComp, Scheme.IdealSheafData.comap_comp, hN, Scheme.IdealSheafData.comap_top])

end Correction

end SectionData

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
