/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.BoundaryFramedSectionActionNative

/-! # Native restriction with already supplied actual Cartier kernels

This thin interface removes result-level geometric instance constructions.
It uses the same root, sections, full boundary and actual target maps.
-/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.ProjectiveCohomology
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors Stacks.Chow
open Stacks.SheafOfModules (schemeTensorPower)
open Stacks.SheafOfModules.Invertible Stacks.AlgebraicGeometry.ModuleLimits

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite
  PrincipalFamilyUnitOpen

local instance nativeCartierActionRootRingedInvertible (X : Scheme.{v}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance nativeCartierActionRootPullbackInvertible
    {X Y : Scheme.{v}} (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance nativeCartierActionRootUnitInvertible (X : Scheme.{v}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)

/-- The native descended root equation and two top-section boundary equations
imply equality of restrictions along the given original maps. -/
theorem restriction_boundary_framed_section_pair_eq_native_cartier
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K) (hP : IsA1Invariant P)
    (A T : SmoothSite (Spec (.of K))) [IsAffine A.left] [IsIntegral A.left]
    {X U B : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [Nonempty B]
    [IsIntegral U] [IsNoetherian U] [U.IsQuasiAffine]
    (q : X ⟶ A.left) [IsProper q] (i : B ⟶ X)
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (r : U ⟶ Limits.pullback A.hom T.hom) (hr : r ≫ Limits.pullback.fst A.hom T.hom = j ≫ q)
    (σ τ : A.left ⟶ X)
    [IsEffectiveCartierDivisor σ.ker] [IsEffectiveCartierDivisor τ.ker]
    (hσ : σ ≫ q = 𝟙 A.left) (hτ : τ ≫ q = 𝟙 A.left)
    (σU τU : A.left ⟶ U) (hσU : σU ≫ j = σ) (hτU : τU ≫ j = τ)
    (hD : ∀ y : B, i y ∉ σ.ker.support)
    (hE : ∀ y : B, i y ∉ τ.ker.support)
    (L : X.Modules) [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
    (N : X.Modules) [hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf N]
    (k : ℕ) (hn : ∀ x : sections P ((Cor.graphFunctor K).obj A), (k + 1) • x = 0)
    (α : schemeTensorPower X L hL ((k + 1 : ℕ) : ℤ) ≅ differenceSheaf σ.ker τ.ker)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(tensorObj L N, ⊤)) (bN : Γ(N, ⊤))
    (haB : Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i (tensorObj L N) a) = (1 : Γ(B, ⊤)))
    (hbB : Hom.app eN.hom ⊤ (pullbackGlobalSections i N bN) = (1 : Γ(B, ⊤)))
    (f g : A ⟶ T)
    (hf : f.left = σU ≫ r ≫ Limits.pullback.snd A.hom T.hom)
    (hg : g.left = τU ≫ r ≫ Limits.pullback.snd A.hom T.hom) :
    ∀ (_he : tensorPowerCongr B.presheaf (ringSheafCond B) _ _ e (k + 1) =
      boundaryRootPowerIso i L (differenceSheaf σ.ker τ.ker) (k + 1) α
        (differenceSheafBoundaryIso i σ.ker τ.ker hD hE)),
    ((toPresheaf K).obj P).map f.op = ((toPresheaf K).obj P).map g.op := by
  intro he
  have hAction := restriction_boundary_framed_section_pair_eq_native P hP A T
    q i j hcover r hr σ τ hσ hτ σU τU hσU hτU hD hE
    L N k hn α e eN a bN haB hbB f g hf hg
  simp only at hAction
  exact hAction he

end AlgebraicGeometry.PresheafWithTransfers
