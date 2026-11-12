/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.SameFibreCartesianRoot
public import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryRootComparison

/-! # Original Cartesian same-fibre root in the native descent convention

The original local root is retained. Only the already-proved root-frame equation
is converted to the natural-power convention consumed by module limit descent.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.EtaleCohomology Stacks.Divisors
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace Stacks.Kummer

local instance sameFibreCartesianNatRingedInvertible (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM

local instance sameFibreCartesianNatPullbackInvertible {X Y : Scheme.{u}}
    (b : X ⟶ Y) (M : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf M] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      ((Scheme.Modules.pullback b).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj b.toLRSHom.toShHom M)

local instance sameFibreCartesianNatUnitInvertible (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (ringSheafCond X)
      (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_unit _ _)


/-- The actual Cartesian same-fibre root and prescribed boundary frame satisfy the
native natural-power equation used by descent, with the original local root intact. -/
theorem exists_sameFibreSectionKernel_cartesian_root_frame_nat
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {XLocal XStage S ULocal UStage BStage : Scheme.{u}}
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
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
    (b : Spec (.of B) ⟶ BStage) (iStage : BStage ⟶ XStage)
    (iLocal : Spec (.of B) ⟶ XLocal) (hb : b ≫ iStage = iLocal ≫ f)
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
          _root_.SheafOfModules.unit (Spec (.of B)).ringCatSheaf,
        tensorPowerCongr (Spec (.of B)).presheaf (ringSheafCond (Spec (.of B))) _ _ e n =
          boundaryRootPowerIso iLocal M
            ((Scheme.Modules.pullback f).obj (differenceSheaf s.ker t.ker)) n
            (α ≪≫ (sectionKernelDifferenceCartesianIso f qLocal qStage g h
              jStage jLocal s t sLocal tLocal hs ht hsLocal htLocal hsec htec
              hsj htj hsjLocal htjLocal).symm)
            (pullbackBoundaryTrivialization b iStage iLocal f hb
              (differenceSheaf s.ker t.ker) τStage) := by
  obtain ⟨M, hM, α, e, he⟩ := exists_sameFibreSectionKernel_cartesian_root_frame
    R f qLocal qStage g h jStage jLocal s t sLocal tLocal hs ht hsLocal htLocal
    hsec htec hsj htj hsjLocal htjLocal hst B b iStage iLocal hb τStage hn0 hn
  let := hM
  let : AlgebraicGeometry.SheafOfModules.IsInvertible XLocal.presheaf
      (ringSheafCond XLocal) M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM
  refine ⟨M, hM, α, e, ?_⟩
  exact (Scheme.Modules.root_frame_equation_iff iLocal M
    ((Scheme.Modules.pullback f).obj (differenceSheaf s.ker t.ker)) hM n
    (α ≪≫ (sectionKernelDifferenceCartesianIso f qLocal qStage g h
      jStage jLocal s t sLocal tLocal hs ht hsLocal htLocal hsec htec
      hsj htj hsjLocal htjLocal).symm)
    (pullbackBoundaryTrivialization b iStage iLocal f hb
      (differenceSheaf s.ker t.ker) τStage) e).mp he

end Stacks.Kummer
