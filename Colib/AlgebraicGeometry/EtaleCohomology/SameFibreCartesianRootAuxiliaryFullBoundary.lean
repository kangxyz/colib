/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.SameFibreCartesianRootAuxiliaryFrames
public import Colib.AlgebraicGeometry.Scheme.FiniteAffinePresentation
public import Colib.AlgebraicGeometry.Modules.Invertible.BoundaryFrameReparametrizeRoot
public import Colib.AlgebraicGeometry.Modules.Invertible.BoundaryFrameReparametrizeSquare
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.NonzeroCompatiblePair

/-! # The same original Cartesian root and its auxiliary framed sections

Select the actual root once, then construct the auxiliary line bundle and both
sections using that very root and boundary frame. The output retains the original
local root, original stage target, natural-power equation and both boundary-one
identities needed for simultaneous descent.
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

local instance fullBoundaryRootAuxiliaryRingedInvertible (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance fullBoundaryRootAuxiliaryPullbackInvertible {X Y : Scheme.{u}}
    (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance fullBoundaryRootAuxiliaryUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)


/-- The auxiliary pair is produced after, and for, the selected root. -/
theorem exists_sameFibreSectionKernel_cartesian_root_auxiliaryFrames_fullBoundary
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
      (hM : Stacks.SheafOfModules.IsInvertible XLocal.presheaf XLocal.ringCatIsSheaf M)
      (α : Stacks.SheafOfModules.schemeTensorPower XLocal M hM (n : ℤ) ≅
        differenceSheaf sLocal.ker tLocal.ker),
      let := hM
      let : AlgebraicGeometry.SheafOfModules.IsInvertible XLocal.presheaf
          (ringSheafCond XLocal) M :=
        Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM
      ∃ e : (Scheme.Modules.pullback iLocal).obj M ≅
          _root_.SheafOfModules.unit Z.ringCatSheaf,
        (tensorPowerCongr Z.presheaf (ringSheafCond Z) _ _ e n =
          boundaryRootPowerIso iLocal M
            ((Scheme.Modules.pullback f).obj (differenceSheaf s.ker t.ker)) n
            (α ≪≫ (sectionKernelDifferenceCartesianIso f qLocal qStage g h
              jStage jLocal s t sLocal tLocal hs ht hsLocal htLocal hsec htec
              hsj htj hsjLocal htjLocal).symm)
            (pullbackBoundaryTrivialization b iStage iLocal f hb
              (differenceSheaf s.ker t.ker) τStage)) ∧
      ∃ (N : XLocal.Modules)
        (_hN : AlgebraicGeometry.SheafOfModules.IsInvertible XLocal.sheaf.obj
          XLocal.ringCatSheaf.property N)
        (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor XLocal.sheaf).obj M).obj N, ⊤))
        (bN : Γ(N, ⊤))
        (eN : (Scheme.Modules.pullback iLocal).obj N ≅
          _root_.SheafOfModules.unit Z.ringCatSheaf),
        a ≠ 0 ∧ bN ≠ 0 ∧
        Scheme.Modules.Hom.app (Scheme.Modules.pullbackTensorFrame iLocal M N e eN).hom ⊤
          (pullbackGlobalSections iLocal _ a) = (1 : Γ(Z, ⊤)) ∧
        Scheme.Modules.Hom.app eN.hom ⊤ (pullbackGlobalSections iLocal N bN) =
          (1 : Γ(Z, ⊤)) := by
  obtain ⟨A, v, ε, hfin, hstructure⟩ :=
    Scheme.exists_finiteAlgebra_presentation R (iLocal ≫ qLocal)
  let := v.toAlgebra
  let := hfin
  let bSpec := ε.inv ≫ b
  let iSpec := ε.inv ≫ iLocal
  have hbSpec : bSpec ≫ iStage = iSpec ≫ f := by
    simpa only [bSpec, iSpec, Category.assoc] using congrArg (fun z => ε.inv ≫ z) hb
  have hcoverSpec : ∀ x : XLocal, x ∈ Set.range jLocal ∨ x ∈ Set.range iSpec := by
    intro x
    rcases hcover x with hx | ⟨z, rfl⟩
    · exact Or.inl hx
    · right
      refine ⟨ε.hom z, ?_⟩
      change iLocal (ε.inv (ε.hom z)) = iLocal z
      have hz : ε.inv (ε.hom z) = z := by
        simp
      rw [hz]
  obtain ⟨M, hM, α, e, he, N, hN, a, bN, eN, ha, hbN, haB, hbB⟩ :=
    exists_sameFibreSectionKernel_cartesian_root_auxiliaryFrames
      R m embedding f qLocal qStage g h jStage jLocal s t sLocal tLocal
      hs ht hsLocal htLocal hsec htec hsj htj hsjLocal htjLocal hst
      A bSpec iStage iSpec hcoverSpec hbSpec τStage hn0 hn
  let := hM
  let : AlgebraicGeometry.SheafOfModules.IsInvertible XLocal.toRingedSpace.presheaf
      (structureSheafRing XLocal.toRingedSpace).property M := hM.toAlgebraicGeometry
  have wi : ε.hom ≫ iSpec = iLocal := by simp [iSpec]
  have wb : ε.hom ≫ bSpec = b := by simp [bSpec]
  let eZ := boundaryFrameReparametrize ε.hom iSpec iLocal wi M e
  let eNZ := boundaryFrameReparametrize ε.hom iSpec iLocal wi N eN
  have hpair := boundaryFrameReparametrize_pair_one ε.hom iSpec iLocal wi
    M N e eN a bN haB hbB
  have hroot := boundaryFrameReparametrize_root ε.hom iSpec iLocal wi M
    ((Scheme.Modules.pullback f).obj (differenceSheaf s.ker t.ker)) n
    (α ≪≫ (sectionKernelDifferenceCartesianIso f qLocal qStage g h
      jStage jLocal s t sLocal tLocal hs ht hsLocal htLocal hsec htec
      hsj htj hsjLocal htjLocal).symm)
    (pullbackBoundaryTrivialization bSpec iStage iSpec f hbSpec
      (differenceSheaf s.ker t.ker) τStage) e he
  have hframe := boundaryFrameReparametrize_square ε.hom bSpec b iStage
    iSpec iLocal f wb wi hbSpec hb (differenceSheaf s.ker t.ker) τStage
  have hrootZ := hroot.trans (congrArg
    (boundaryRootPowerIso iLocal M
      ((Scheme.Modules.pullback f).obj (differenceSheaf s.ker t.ker)) n
      (α ≪≫ (sectionKernelDifferenceCartesianIso f qLocal qStage g h
        jStage jLocal s t sLocal tLocal hs ht hsLocal htLocal hsec htec
        hsj htj hsjLocal htjLocal).symm)) hframe)
  exact ⟨M, hM, α, eZ, hrootZ, N, hN, a, bN, eNZ, ha, hbN, hpair.1, hpair.2⟩

end Stacks.Kummer
