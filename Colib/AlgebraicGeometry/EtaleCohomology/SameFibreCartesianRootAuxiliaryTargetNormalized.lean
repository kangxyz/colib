/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.SameFibreCartesianRootAuxiliaryTarget

/-! # The same Cartesian root in the actual consumer output convention

Select the actual root once, then construct the auxiliary line bundle and both
sections using that very root and boundary frame. This thin interface fixes the composed root
target before any actual diagram
is specialized. It retains the selected root and all auxiliary sections and equations.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.ProjectiveCohomology
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors Stacks.EtaleCohomology
open Stacks.SheafOfModules.Invertible Stacks.AlgebraicGeometry.ModuleLimits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf
namespace Stacks.Kummer

local instance normalizedBoundaryRootAuxiliaryRingedInvertible (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance normalizedBoundaryRootAuxiliaryPullbackInvertible {X Y : Scheme.{u}}
    (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance normalizedBoundaryRootAuxiliaryUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)


/-- The auxiliary pair is produced after, and for, the selected root. -/
theorem exists_sameFibreSectionKernel_cartesian_root_auxiliaryFrames_target_normalized
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R] [IsNoetherianRing R]
    {XLocal XStage S ULocal UStage BStage : Scheme.{u}}
    [IsIntegral XLocal] [ULocal.IsQuasiAffine]
    (m : ℕ) (embedding : XLocal ⟶ Proj (polyGrading R m)) [IsClosedImmersion embedding]
    (f : XLocal ⟶ XStage) (qLocal : XLocal ⟶ Spec (.of R)) [IsProper qLocal]
    (qStage : XStage ⟶ S) [IsSeparated qStage] (g : Spec (.of R) ⟶ S)
    (h : IsPullback f qLocal qStage g)
    (jStage : UStage ⟶ XStage) [IsOpenImmersion jStage]
    [SmoothOfRelativeDimension 1 (jStage ≫ qStage)]
    (jLocal : ULocal ⟶ XLocal) [IsOpenImmersion jLocal]
    [SmoothOfRelativeDimension 1 (jLocal ≫ qLocal)]
    (s t : S ⟶ XStage) (sLocal tLocal : Spec (.of R) ⟶ XLocal)
    (hs : s ≫ qStage = 𝟙 S) (ht : t ≫ qStage = 𝟙 S)
    (hsLocal : sLocal ≫ qLocal = 𝟙 _) (htLocal : tLocal ≫ qLocal = 𝟙 _)
    (hsec : sLocal ≫ f = g ≫ s) (htec : tLocal ≫ f = g ≫ t)
    (hsj : Set.range s ⊆ Set.range jStage) (htj : Set.range t ⊆ Set.range jStage)
    (hsjLocal : Set.range sLocal ⊆ Set.range jLocal)
    (htjLocal : Set.range tLocal ⊆ Set.range jLocal)
    (hst : residueFieldPoint R ≫ sLocal = residueFieldPoint R ≫ tLocal)
    {Z : Scheme.{u}} (b : Z ⟶ BStage) (iLocal : Z ⟶ XLocal)
    [IsClosedImmersion iLocal] [IsFinite (iLocal ≫ qLocal)]
    (iStage : BStage ⟶ XStage)
    (hcover : ∀ x : XLocal, x ∈ Set.range jLocal ∨ x ∈ Set.range iLocal)
    (hb : b ≫ iStage = iLocal ≫ f)
    (τStage : (Scheme.Modules.pullback iStage).obj (differenceSheaf s.ker t.ker) ≅
      _root_.SheafOfModules.unit BStage.ringCatSheaf)
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R)) :
    ∃ (M : XLocal.Modules)
      (hM : Stacks.SheafOfModules.IsInvertible XLocal.presheaf XLocal.ringCatIsSheaf M),
      let _ := hM
      let _ : AlgebraicGeometry.SheafOfModules.IsInvertible XLocal.toRingedSpace.presheaf
          (structureSheafRing XLocal.toRingedSpace).property M := hM.toAlgebraicGeometry
      ∃ (α : tensorPower XLocal.toRingedSpace.presheaf
          (structureSheafRing XLocal.toRingedSpace).property M (n : ℤ) ≅
          (Scheme.Modules.pullback f).obj (differenceSheaf s.ker t.ker))
        (e : (Scheme.Modules.pullback iLocal).obj M ≅
          _root_.SheafOfModules.unit Z.ringCatSheaf),
        tensorPowerCongr Z.presheaf (ringSheafCond Z) _ _ e n =
          boundaryRootPowerIso iLocal M _ n α
            (pullbackBoundaryTrivialization b iStage iLocal f hb
              (differenceSheaf s.ker t.ker) τStage) ∧
        ∃ (Naux : XLocal.Modules)
          (_hNaux : AlgebraicGeometry.SheafOfModules.IsInvertible XLocal.sheaf.obj
            XLocal.ringCatSheaf.property Naux)
          (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor XLocal.sheaf).obj M).obj Naux, ⊤))
          (bN : Γ(Naux, ⊤))
          (eN : (Scheme.Modules.pullback iLocal).obj Naux ≅
            _root_.SheafOfModules.unit Z.ringCatSheaf),
          a ≠ 0 ∧ bN ≠ 0 ∧
          Scheme.Modules.Hom.app (X := Z)
            (Scheme.Modules.pullbackTensorFrame iLocal M Naux e eN).hom ⊤
            (pullbackGlobalSections iLocal _ a) = (1 : Γ(Z, ⊤)) ∧
          Scheme.Modules.Hom.app (X := Z) eN.hom ⊤ (pullbackGlobalSections iLocal Naux bN) =
            (1 : Γ(Z, ⊤)) := by
  obtain ⟨M, hM, α, e, he, Naux, hNaux, a, bN, eN, ha, hbN, haB, hbB⟩ :=
    exists_sameFibreSectionKernel_cartesian_root_auxiliaryFrames_target
      R m embedding f qLocal qStage g h jStage jLocal s t sLocal tLocal
      hs ht hsLocal htLocal hsec htec hsj htj hsjLocal htjLocal hst
      b iLocal iStage hcover hb τStage hn0 hn
  let := hM
  exact ⟨M, hM, α, e, he, Naux, hNaux, a, bN, eN, ha, hbN, haB, hbB⟩

end Stacks.Kummer
