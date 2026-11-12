/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.SameFibrePrescribedFrame
public import Colib.AlgebraicGeometry.Divisors.SectionKernelOpenBaseChange
public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRoot

/-!
# Same-fibre roots with the actual Cartesian stage target and boundary frame

The supplied Cartesian square identifies pullback of the original stage section
kernels with the actual local section kernels. Proper Kummer specialization supplies
a root of their local difference. Its transport through that literal difference
comparison is framed against the pullback of the specified stage boundary frame.

The boundary square need only commute. Its native pullback comparison retains both
original paths and the entire boundary. No compatibility with a separately chosen
local canonical frame, root, or equality of transfer actions is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.EtaleCohomology Stacks.Divisors
open Stacks.SheafOfModules.Invertible
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace Stacks.Kummer

/-- The scheme structure sheaf has commutative multiplication on every open. -/
local instance sameFibreCartesianRootMulCommutative (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- The actual local section difference has a root framed against the original stage's
boundary trivialization after its actual Cartesian pullback. Only retained opens are smooth. -/
theorem exists_sameFibreSectionKernel_cartesian_root_frame
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
      letI := hM
      letI : AlgebraicGeometry.SheafOfModules.IsInvertible
          (Spec (.of B)).presheaf (ringSheafCond (Spec (.of B)))
          ((Scheme.Modules.pullback iLocal).obj M) :=
        Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
          (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj iLocal.toLRSHom.toShHom M)
      ∃ e : (Scheme.Modules.pullback iLocal).obj M ≅
          _root_.SheafOfModules.unit (ringSheaf (Spec (.of B))),
        tensorPowerMap (Spec (.of B)) e n ≪≫ structureSheafTensorPowerIso (Spec (.of B)) n =
        (Scheme.Modules.pullbackIntegerTensorPowerIso iLocal M hM (n : ℤ)).symm ≪≫
          (Scheme.Modules.pullback iLocal).mapIso
            (α ≪≫ (sectionKernelDifferenceCartesianIso f qLocal qStage g h
              jStage jLocal s t sLocal tLocal hs ht hsLocal htLocal hsec htec
              hsj htj hsjLocal htjLocal).symm) ≪≫
          pullbackBoundaryTrivialization b iStage iLocal f hb
            (differenceSheaf s.ker t.ker) τStage := by
  exact exists_sameFibreSectionKernel_root_prescribed_frame R qLocal jLocal
    sLocal tLocal hsLocal htLocal hsjLocal htjLocal hst B iLocal
    ((Scheme.Modules.pullback f).obj (differenceSheaf s.ker t.ker))
    (sectionKernelDifferenceCartesianIso f qLocal qStage g h jStage jLocal
      s t sLocal tLocal hs ht hsLocal htLocal hsec htec hsj htj hsjLocal htjLocal).symm
    (pullbackBoundaryTrivialization b iStage iLocal f hb (differenceSheaf s.ker t.ker) τStage)
    hn0 hn

end Stacks.Kummer
