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
  let e := (Modules.pullbackComp β i).app M
  have h₁ := SectionsEqualizer.pullbackGlobalSections_comp i' g M s
  have h₂ := pullbackCongr_section h M s
  have h₃ := SectionsEqualizer.pullbackGlobalSections_comp β i M s
  have h₄ := (congrArg (fun t => ((Modules.pullbackCongr h).app M).hom.app ⊤ t) h₁).trans h₂
  exact (congrArg (fun t => e.inv.app ⊤ t) (h₄.trans h₃.symm)).trans (iso_hom_inv_app e _)

include h in
/-- An actual scalar section equation on the entire original boundary survives
the actual source change, with the literal scalar ring map. -/
theorem boundary_smul_identity_after_sourceChange (M : X.Modules) (a b : Γ(M, ⊤))
    (c : Γ(Z, ⊤))
    (hab : pullbackGlobalSections i M a = c • pullbackGlobalSections i M b) :
    pullbackGlobalSections i' _ (pullbackGlobalSections g M a) =
      β.appTop c • pullbackGlobalSections i' _ (pullbackGlobalSections g M b) := by
  let e := boundaryPullbackSquareIso g i i' β h M
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  have h₁ := boundaryPullbackSquareIso_section g i i' β h M a
  have h₂ := congrArg (fun t => pullbackGlobalSections β ((Modules.pullback i).obj M) t) hab
  have h₃ := SectionsEqualizer.pullbackGlobalSections_smul β
    ((Modules.pullback i).obj M) c (pullbackGlobalSections i M b)
  have h₄ := congrArg (fun t => β.appTop c • t)
    (boundaryPullbackSquareIso_section g i i' β h M b).symm
  have h₅ := Modules.Hom.app_smul e.hom (β.appTop c)
    (pullbackGlobalSections i' _ (pullbackGlobalSections g M b))
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅.symm)))

/-- The first normalization identifies the graph-times-denominator section with
the exact canonical coordinate times the numerator, before source restriction. -/
theorem graphPole_boundary_eq_coordinate_smul (F T : X.Modules)
    (eF : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf)
    (σ : Γ(F, ⊤)) (a : Γ(tensorModules F T, ⊤)) (b : Γ(T, ⊤))
    (ha : (fixedFactorBoundaryIso i F T eF).hom.app ⊤
      (pullbackGlobalSections i _ a) = pullbackGlobalSections i _ b) :
    pullbackGlobalSections i _ (tensorSection F T ⊤ σ b) =
      frameCoordinate eF (pullbackGlobalSections i F σ) • pullbackGlobalSections i _ a := by
  let e := fixedFactorBoundaryIso i F T eF
  let F' := (Modules.pullback i).obj F
  let T' := (Modules.pullback i).obj T
  let e' := frameTensorContraction F' T' eF
  let c := frameCoordinate eF (pullbackGlobalSections i F σ)
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  have h₁ := congrArg (fun t => e'.hom.app ⊤ t) (pullbackTensorIso_tensorSection i F T σ b)
  have h₂ := frameTensorContraction_tensorSection F' T' eF
    (pullbackGlobalSections i F σ) (pullbackGlobalSections i T b)
  have h₃ := congrArg (fun t => c • t) ha.symm
  have h₄ := Modules.Hom.app_smul e.hom c (pullbackGlobalSections i (tensorModules F T) a)
  exact h₁.trans (h₂.trans (h₃.trans h₄.symm))

include h in
/-- The first pair extends on the original source, while the second pair lives on
the changed source. Their literal products agree on the entire changed boundary.
The numerator line is the actual pullback of `F tensor T`, not a replacement line. -/
theorem boundary_tensor_matching_after_sourceChange (F T : X.Modules) (N : X'.Modules)
    (eF : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf)
    (σ : Γ(F, ⊤)) (a : Γ(tensorModules F T, ⊤)) (b : Γ(T, ⊤)) (n d : Γ(N, ⊤))
    (ha : (fixedFactorBoundaryIso i F T eF).hom.app ⊤
      (pullbackGlobalSections i _ a) = pullbackGlobalSections i _ b)
    (hn : pullbackGlobalSections i' N n =
      β.appTop (frameCoordinate eF (pullbackGlobalSections i F σ)) •
        pullbackGlobalSections i' N d) :
    pullbackGlobalSections i' _
      (tensorSection ((Modules.pullback g).obj (tensorModules F T)) N ⊤
        (pullbackGlobalSections g _ a) n) =
      pullbackGlobalSections i' _
        (tensorSection ((Modules.pullback g).obj (tensorModules F T)) N ⊤
          (pullbackGlobalSections g _ (tensorSection F T ⊤ σ b)) d) := by
  have hc := boundary_smul_identity_after_sourceChange g i i' β h (tensorModules F T)
    (tensorSection F T ⊤ σ b) a _ (graphPole_boundary_eq_coordinate_smul i F T eF σ a b ha)
  let M := (Modules.pullback g).obj (tensorModules F T)
  let a' := pullbackGlobalSections g (tensorModules F T) a
  let b' := pullbackGlobalSections g (tensorModules F T) (tensorSection F T ⊤ σ b)
  let e := Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i' M N
  let eΓ := (SheafOfModules.evaluation Z'.ringCatSheaf (Opposite.op ⊤)).mapIso e
  have he : Function.Injective (Modules.Hom.app (X := Z') e.hom ⊤) :=
    (ConcreteCategory.bijective_of_isIso eΓ.hom).1
  apply he
  have h₁ := pullbackTensorIso_tensorSection i' M N a' n
  have h₂ := pullbackTensorIso_tensorSection i' M N b' d
  have h₃ :
      tensorSection ((Modules.pullback i').obj M) ((Modules.pullback i').obj N) ⊤
        (pullbackGlobalSections i' M a') (pullbackGlobalSections i' N n) =
      tensorSection ((Modules.pullback i').obj M) ((Modules.pullback i').obj N) ⊤
        (pullbackGlobalSections i' M b') (pullbackGlobalSections i' N d) := by
    rw [hn, hc, tensorSection_smul_left, tensorSection_smul_right]
  exact h₁.trans (h₃.trans h₂.symm)

end AlgebraicGeometry.Scheme.RelativeCurvePencil
