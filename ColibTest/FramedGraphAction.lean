/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.FramedGraphAction

/-!
# A geometric framed root produces the original graph moving relation

The two original sections supply their actual Cartier kernels and rank-one whole finite
locally free schemes. COL-1048 chooses the auxiliary twist, its frame and the actual nonzero
numerator and denominator. COL-1072 then produces the native signed finite-correspondence
identity and the same correction function normalized on the entire boundary. No divisor pair,
finite-locally-free certificates for it, or final signed identity is an input.
-/

noncomputable section

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

example
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K) (hP : IsA1Invariant P)
    (A T : SmoothSite (Spec (.of K))) [IsAffine A.left] [IsIntegral A.left]
    (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Nonempty (Spec (CommRingCat.of B))] (n : ℕ)
    {X U : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [IsIntegral U] [IsNoetherian U] [U.IsQuasiAffine]
    (g : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion g]
    (q : X ⟶ A.left) [IsProper q] (i : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (r : U ⟶ Limits.pullback A.hom T.hom) (hr : r ≫ Limits.pullback.fst A.hom T.hom = j ≫ q)
    (σ τ : A.left ⟶ X) (hσ : σ ≫ q = 𝟙 A.left) (hτ : τ ≫ q = 𝟙 A.left)
    (σU τU : A.left ⟶ U) (hσU : σU ≫ j = σ) (hτU : τU ≫ j = τ)
    (hD : ∀ y : Spec (CommRingCat.of B), i y ∉ σ.ker.support)
    (hE : ∀ y : Spec (CommRingCat.of B), i y ∉ τ.ker.support)
    [IsIntegral (parameterSpace (q ≫ A.hom))]
    [IsNoetherian (parameterSpace (q ≫ A.hom))]
    (L : X.Modules) [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
    (k : ℕ) (hn : ∀ x : sections P ((Cor.graphFunctor K).obj A), (k + 1) • x = 0)
    (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf σ.ker τ.ker)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :
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
  exact transfer_geometric_framed_graph_eq P hP A T R B n g q i j hcover r hr
    σ τ hσ hτ σU τU hσU hτU hD hE L k hn α e hcompat

end AlgebraicGeometry.PresheafWithTransfers
