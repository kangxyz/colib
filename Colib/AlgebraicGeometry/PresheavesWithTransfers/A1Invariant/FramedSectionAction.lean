/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.FramedPairAction
public import Colib.AlgebraicGeometry.Correspondences.Divisors.GeometricFramedMovingRelation
public import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian

/-!
# Original section graph actions from a descended framed pair

This is the general smooth-base specialization of COL-1105. The actual original
section kernels supply their Cartier and whole finite locally free geometry.
The given finite pair is consumed by COL-1072 through `transfer_framed_pair_eq`,
then native retained section-kernel correspondences become the original graphs.
There is no local coefficient ring or strict-henselization-as-smooth-object input.
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

/-- A given framed finite pair on a general smooth base forces equality of the
unchanged original section graph actions. No local-ring hypothesis occurs. -/
theorem transfer_framed_section_pair_eq
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
    [IsIntegral (parameterSpace (q ≫ A.hom))]
    [IsNoetherian (parameterSpace (q ≫ A.hom))]
    (L : X.Modules) [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
    (N : X.Modules) [hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N]
    (k : ℕ) (hn : ∀ x : sections P ((Cor.graphFunctor K).obj A), (k + 1) • x = 0)
    (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf σ.ker τ.ker)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(tensorObj L N, ⊤)) (b : N.sections) (ha0 : a ≠ 0) (hb0 : b.eval (op ⊤) ≠ 0)
    (haB : Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i (tensorObj L N) a) = (1 : Γ(B, ⊤)))
    (hbB : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) = (1 : Γ(B, ⊤)))
    (haU : Set.range (zeroScheme X (tensorObj L N) a).subschemeι ⊆ Set.range j)
    (hbU : Set.range (zeroScheme X N (b.eval (op ⊤))).subschemeι ⊆ Set.range j)
    [Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme X (tensorObj L N) a).subschemeι ≫ q)]
    [Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme X N (b.eval (op ⊤))).subschemeι ≫ q)] :
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
  let : IsAffine ((𝟭 Scheme).obj A.left) := ‹IsAffine A.left›
  let : IsIntegral ((𝟭 Scheme).obj A.left) := ‹IsIntegral A.left›
  let : IsNoetherian A.left := inferInstance
  let : IsNoetherian ((𝟭 Scheme).obj A.left) := ‹IsNoetherian A.left›
  have := sectionKernel_cartier_of_factor q j σ hσ σU hσU
  have := sectionKernel_cartier_of_factor q j τ hτ τU hτU
  have := sectionKernel_finiteLocallyFree q σ hσ
  have := sectionKernel_finiteLocallyFree q τ hτ
  have hDU := sectionKernel_range_subset_of_factor q j σ hσ σU hσU
  have hEU := sectionKernel_range_subset_of_factor q j τ hτ τU hτU
  have hcov : (Set.range j)ᶜ ⊆ Set.range i := by
    intro x hx
    exact (hcover x).resolve_left hx
  have H := transfer_framed_pair_eq i σ.ker τ.ker L N P hP A T j q hcov r hr
    hDU hEU hD hE k hn α e eN hcompat a b ha0 hb0 haB hbB haU hbU
  have HS := congrArg
    (fun γ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T => transfer P γ)
    (retainedFiniteFlatDivisorCorrespondence_sectionKernel A.hom T.hom q j r hr
      σ hσ σU hσU hDU)
  have HT := congrArg
    (fun γ : (Cor.graphFunctor K).obj A ⟶ (Cor.graphFunctor K).obj T => transfer P γ)
    (retainedFiniteFlatDivisorCorrespondence_sectionKernel A.hom T.hom q j r hr
      τ hτ τU hτU hEU)
  exact HS.symm.trans (H.trans HT)

end AlgebraicGeometry.PresheafWithTransfers
