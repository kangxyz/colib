/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.FramedSectionAction

/-!
# Original section actions from full-boundary equations

On a general smooth affine integral base, the actual boundary-one equations force the
whole numerator and denominator zero schemes to be finite locally free Cartier divisors.
Their sections are nonzero and their supports lie in the retained smooth curve open.
The original framed-section action theorem therefore needs no supplied finite-pair witness.
This is a consumer of root and frame data, not a construction of an etale refinement.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.ProjectiveCohomology
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors Stacks.Chow
open Stacks.SheafOfModules (schemeTensorPower)

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite
  PrincipalFamilyUnitOpen

attribute [local instance] framedCorrectionInvertible framedCorrectionQuasicoherent
  framedCorrectionDifferenceInvertible framedCorrectionDifferenceAGInvertible
  framedCorrectionPullbackInvertible framedCorrectionPullbackAGInvertible
  framedCorrectionMulCommutative framedCorrectionTensorEquivalence framedCorrectionPowerInvertible
  movingTensorQuotientSecondInvertible movingTensorQuotientTensorInvertible

/-- Full-boundary frame equations supply all finite-pair geometry needed for equality
of the unchanged original section graph actions on a general smooth affine integral base. -/
theorem transfer_boundary_framed_section_pair_eq
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K) (hP : IsA1Invariant P)
    (A T : SmoothSite (Spec (.of K))) [IsAffine A.left] [IsIntegral A.left]
    {X U B : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Nonempty B]
    [IsIntegral U] [IsNoetherian U] [U.IsQuasiAffine]
    (q : X ⟶ A.left) [IsProper q] (i : B ⟶ X)
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (r : U ⟶ Limits.pullback A.hom T.hom) (hr : r ≫ Limits.pullback.fst A.hom T.hom = j ≫ q)
    (σ τ : A.left ⟶ X) (hσ : σ ≫ q = 𝟙 A.left) (hτ : τ ≫ q = 𝟙 A.left)
    (σU τU : A.left ⟶ U) (hσU : σU ≫ j = σ) (hτU : τU ≫ j = τ)
    (hD : ∀ y : B, i y ∉ σ.ker.support)
    (hE : ∀ y : B, i y ∉ τ.ker.support)
    (L : X.Modules) [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
    (N : X.Modules) [hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N]
    (k : ℕ) (hn : ∀ x : sections P ((Cor.graphFunctor K).obj A), (k + 1) • x = 0)
    (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf σ.ker τ.ker)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(tensorObj L N, ⊤)) (b : N.sections)
    (haB : Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i (tensorObj L N) a) = (1 : Γ(B, ⊤)))
    (hbB : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) = (1 : Γ(B, ⊤))) :
    let := sectionKernel_cartier_of_factor q j σ hσ σU hσU
    let := sectionKernel_cartier_of_factor q j τ hτ τU hτU
    ∀ (_hcompat : tensorPowerMap _ e (k + 1) ≪≫ structureSheafTensorPowerIso _ (k + 1) =
      (pullbackIntegerTensorPowerIso i L hL (k + 1)).symm ≪≫ (pullback i).mapIso α ≪≫
        differenceSheafBoundaryIso i σ.ker τ.ker hD hE),
    transfer P (graphCorrespondenceOfComponents A.hom T.hom
      (σU ≫ r ≫ Limits.pullback.snd A.hom T.hom)
      (sectionTarget_base A.hom T.hom r σU
        (retainedSection_firstProjection A.hom T.hom q j r hr σ hσ σU hσU))
      (Cor.finite_genericPoints K ((Cor.graphFunctor K).obj A))) =
    transfer P (graphCorrespondenceOfComponents A.hom T.hom
      (τU ≫ r ≫ Limits.pullback.snd A.hom T.hom)
      (sectionTarget_base A.hom T.hom r τU
        (retainedSection_firstProjection A.hom T.hom q j r hr τ hτ τU hτU))
      (Cor.finite_genericPoints K ((Cor.graphFunctor K).obj A))) := by
  dsimp only
  intro hcompat
  let : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L := hL.toAlgebraicGeometry
  let : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property N := hN.toAlgebraicGeometry
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L := hL
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property N := hN
  let : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property (tensorObj L N) :=
    (Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj
      X.ringCatSheaf.property L N).toAlgebraicGeometry
  have ha := finiteLocallyFree_zeroScheme_of_boundary_frame q i j hcover
    (tensorObj L N) a (pullbackTensorFrame i L N e eN) haB
  have hb := finiteLocallyFree_zeroScheme_of_boundary_frame q i j hcover
    N (b.eval (op ⊤)) eN hbB
  let := ha.2.1
  let := hb.2.1
  exact transfer_framed_section_pair_eq P hP A T q i j hcover r hr σ τ hσ hτ
    σU τU hσU hτU hD hE L N k hn α e eN a b
    (globalSection_ne_zero_of_isEffectiveCartierDivisor_zeroScheme _ a ha.1.1)
    (globalSection_ne_zero_of_isEffectiveCartierDivisor_zeroScheme N _ hb.1.1) haB hbB
    (zeroScheme_range_subset_of_boundary_frame i j hcover _ a
      (pullbackTensorFrame i L N e eN) haB)
    (zeroScheme_range_subset_of_boundary_frame i j hcover N _ eN hbB) hcompat

/-- The same framed construction equates the restrictions along the given original smooth-site
maps. The displayed map equations identify the actual section targets, not their values. -/
theorem restriction_boundary_framed_section_pair_eq
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K) (hP : IsA1Invariant P)
    (A T : SmoothSite (Spec (.of K))) [IsAffine A.left] [IsIntegral A.left]
    {X U B : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Nonempty B]
    [IsIntegral U] [IsNoetherian U] [U.IsQuasiAffine]
    (q : X ⟶ A.left) [IsProper q] (i : B ⟶ X)
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (r : U ⟶ Limits.pullback A.hom T.hom) (hr : r ≫ Limits.pullback.fst A.hom T.hom = j ≫ q)
    (σ τ : A.left ⟶ X) (hσ : σ ≫ q = 𝟙 A.left) (hτ : τ ≫ q = 𝟙 A.left)
    (σU τU : A.left ⟶ U) (hσU : σU ≫ j = σ) (hτU : τU ≫ j = τ)
    (hD : ∀ y : B, i y ∉ σ.ker.support)
    (hE : ∀ y : B, i y ∉ τ.ker.support)
    (L : X.Modules) [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
    (N : X.Modules) [hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N]
    (k : ℕ) (hn : ∀ x : sections P ((Cor.graphFunctor K).obj A), (k + 1) • x = 0)
    (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf σ.ker τ.ker)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(tensorObj L N, ⊤)) (b : N.sections)
    (haB : Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i (tensorObj L N) a) = (1 : Γ(B, ⊤)))
    (hbB : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) = (1 : Γ(B, ⊤)))
    (f g : A ⟶ T)
    (hf : f.left = σU ≫ r ≫ Limits.pullback.snd A.hom T.hom)
    (hg : g.left = τU ≫ r ≫ Limits.pullback.snd A.hom T.hom) :
    let := sectionKernel_cartier_of_factor q j σ hσ σU hσU
    let := sectionKernel_cartier_of_factor q j τ hτ τU hτU
    ∀ (_hcompat : tensorPowerMap _ e (k + 1) ≪≫ structureSheafTensorPowerIso _ (k + 1) =
      (pullbackIntegerTensorPowerIso i L hL (k + 1)).symm ≪≫ (pullback i).mapIso α ≪≫
        differenceSheafBoundaryIso i σ.ker τ.ker hD hE),
    ((toPresheaf K).obj P).map f.op = ((toPresheaf K).obj P).map g.op := by
  dsimp only
  intro hcompat
  change transfer P ((Cor.graphFunctor K).map f) = transfer P ((Cor.graphFunctor K).map g)
  simpa only [Cor.graphFunctor_map, Cor.graphFunctor_obj, hf, hg] using
    transfer_boundary_framed_section_pair_eq P hP A T q i j hcover r hr σ τ hσ hτ
      σU τU hσU hτU hD hE L N k hn α e eN a b haB hbB hcompat

end AlgebraicGeometry.PresheafWithTransfers
