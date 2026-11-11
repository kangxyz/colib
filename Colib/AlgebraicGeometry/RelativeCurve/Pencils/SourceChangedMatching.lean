/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.NormalizedTensorMatching

/-!
# Literal matching after changing only the first source

The first numerator and denominator remain global sections on the original
compactification. Only their actual pullbacks are used on the punctured-source
compactification. The second scalar pair is allowed to live on this new source.
A commuting square of the full boundary maps supplies the canonical pullback
comparison; no tensor-coherence or normalization equation is added as an input.

This retains the two-source distinction required for the lambda extension in
the original relative-curve correction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

private theorem iso_hom_inv_app {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (s : Γ(M, ⊤)) : e.inv.app ⊤ (e.hom.app ⊤ s) = s :=
  congrArg (fun f => f.app ⊤ s) e.hom_inv_id

private theorem iso_inv_hom_app {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (s : Γ(N, ⊤)) : e.hom.app ⊤ (e.inv.app ⊤ s) = s :=
  congrArg (fun f => f.app ⊤ s) e.inv_hom_id

variable {X X' Z Z' : Scheme.{u}} (g : X' ⟶ X) (i : Z ⟶ X)
  (i' : Z' ⟶ X') (β : Z' ⟶ Z) (h : i' ≫ g = β ≫ i)

/-- The actual comparison of the two paths in the whole-boundary square. -/
def boundaryPullbackSquareIso (M : X.Modules) :
    (Modules.pullback i').obj ((Modules.pullback g).obj M) ≅
      (Modules.pullback β).obj ((Modules.pullback i).obj M) :=
  (Modules.pullbackComp i' g).app M ≪≫ (Modules.pullbackCongr h).app M ≪≫
    ((Modules.pullbackComp β i).app M).symm

private theorem pullbackCongr_section {A B : Scheme.{u}} {f k : A ⟶ B}
    (hf : f = k) (M : B.Modules) (s : Γ(M, ⊤)) :
    ((Modules.pullbackCongr hf).app M).hom.app ⊤ (pullbackGlobalSections f M s) =
      pullbackGlobalSections k M s := by
  subst k
  rfl

/-- The square comparison preserves the original global section, not just its
isomorphism class. -/
theorem boundaryPullbackSquareIso_section (M : X.Modules) (s : Γ(M, ⊤)) :
    (boundaryPullbackSquareIso g i i' β h M).hom.app ⊤
      (pullbackGlobalSections i' _ (pullbackGlobalSections g M s)) =
        pullbackGlobalSections β _ (pullbackGlobalSections i M s) := by
  change ((Modules.pullbackComp β i).app M).inv.app ⊤
    (((Modules.pullbackCongr h).app M).hom.app ⊤
      (((Modules.pullbackComp i' g).app M).hom.app ⊤
        (pullbackGlobalSections i' _ (pullbackGlobalSections g M s)))) = _
  rw [SectionsEqualizer.pullbackGlobalSections_comp, pullbackCongr_section,
    ← SectionsEqualizer.pullbackGlobalSections_comp β i]
  exact iso_hom_inv_app _ _

/-- An actual scalar section equation on the entire original boundary survives
the actual source change, with the literal scalar ring map. -/
theorem boundary_smul_identity_after_sourceChange (M : X.Modules) (a b : Γ(M, ⊤))
    (c : Γ(Z, ⊤))
    (hab : pullbackGlobalSections i M a = c • pullbackGlobalSections i M b) :
    pullbackGlobalSections i' _ (pullbackGlobalSections g M a) =
      β.appTop c • pullbackGlobalSections i' _ (pullbackGlobalSections g M b) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((boundaryPullbackSquareIso g i i' β h M).hom.app ⊤)).injective
  rw [Modules.Hom.app_smul, boundaryPullbackSquareIso_section,
    boundaryPullbackSquareIso_section, hab, SectionsEqualizer.pullbackGlobalSections_smul]

/-- The first normalization identifies the graph-times-denominator section with
the exact canonical coordinate times the numerator, before source restriction. -/
theorem graphPole_boundary_eq_coordinate_smul (F T : X.Modules)
    (eF : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf)
    (σ : Γ(F, ⊤)) (a : Γ(tensorModules F T, ⊤)) (b : Γ(T, ⊤))
    (ha : (fixedFactorBoundaryIso i F T eF).hom.app ⊤
      (pullbackGlobalSections i _ a) = pullbackGlobalSections i _ b) :
    pullbackGlobalSections i _ (tensorSection F T ⊤ σ b) =
      eF.hom.app ⊤ (pullbackGlobalSections i F σ) • pullbackGlobalSections i _ a := by
  apply (ConcreteCategory.bijective_of_isIso
    ((fixedFactorBoundaryIso i F T eF).hom.app ⊤)).injective
  rw [Modules.Hom.app_smul, ha]
  change (frameTensorContraction ((Modules.pullback i).obj F)
      ((Modules.pullback i).obj T) eF).hom.app ⊤
    ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i F T).hom.app ⊤
      (pullbackGlobalSections i _ (tensorSection F T ⊤ σ b))) = _
  rw [pullbackTensorIso_tensorSection, frameTensorContraction_tensorSection]

/-- The first pair extends on the original source, while the second pair lives on
the changed source. Their literal products agree on the entire changed boundary.
The numerator line is the actual pullback of `F tensor T`, not a replacement line. -/
theorem boundary_tensor_matching_after_sourceChange (F T : X.Modules) (N : X'.Modules)
    (eF : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf)
    (σ : Γ(F, ⊤)) (a : Γ(tensorModules F T, ⊤)) (b : Γ(T, ⊤)) (n d : Γ(N, ⊤))
    (ha : (fixedFactorBoundaryIso i F T eF).hom.app ⊤
      (pullbackGlobalSections i _ a) = pullbackGlobalSections i _ b)
    (hn : pullbackGlobalSections i' N n =
      β.appTop (eF.hom.app ⊤ (pullbackGlobalSections i F σ)) • pullbackGlobalSections i' N d) :
    pullbackGlobalSections i' _
      (tensorSection ((Modules.pullback g).obj (tensorModules F T)) N ⊤
        (pullbackGlobalSections g _ a) n) =
      pullbackGlobalSections i' _
        (tensorSection ((Modules.pullback g).obj (tensorModules F T)) N ⊤
          (pullbackGlobalSections g _ (tensorSection F T ⊤ σ b)) d) := by
  have hc := boundary_smul_identity_after_sourceChange g i i' β h (tensorModules F T)
    (tensorSection F T ⊤ σ b) a _ (graphPole_boundary_eq_coordinate_smul i F T eF σ a b ha)
  apply (ConcreteCategory.bijective_of_isIso
    ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i'
      ((Modules.pullback g).obj (tensorModules F T)) N).hom.app ⊤)).injective
  rw [pullbackTensorIso_tensorSection, pullbackTensorIso_tensorSection, hn, hc,
    tensorSection_smul_left, tensorSection_smul_right]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
