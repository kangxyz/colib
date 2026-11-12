/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.EtaleCohomology.SameFibreSectionDivisorRoot

/-!
# Tests for proper same-fibre roots and full-boundary frames
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology Stacks.Divisors
open Stacks.SheafOfModules.Invertible

universe u

local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

example
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X U : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hst : residueFieldPoint R ≫ s = residueFieldPoint R ≫ t)
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
        differenceSheaf s.ker t.ker) :=
  Stacks.Kummer.exists_schemeTensorPower_iso_sameFibreSectionKernel_differenceSheaf
    R q j s t hs ht hsj htj hst hn0 hn

example
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X U : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hst : residueFieldPoint R ≫ s = residueFieldPoint R ≫ t)
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B]
    (i : Spec (CommRingCat.of B) ⟶ X)
    (his : Disjoint (Set.range i) (Set.range s))
    (hit : Disjoint (Set.range i) (Set.range t))
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
      (α : Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅
        differenceSheaf s.ker t.ker),
      letI := hM
      letI : AlgebraicGeometry.SheafOfModules.IsInvertible
          (Spec (CommRingCat.of B)).presheaf (ringSheafCond (Spec (CommRingCat.of B)))
          ((Scheme.Modules.pullback i).obj M) :=
        Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
          (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom M)
      ∃ e : (Scheme.Modules.pullback i).obj M ≅
          _root_.SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
        tensorPowerMap (Spec (CommRingCat.of B)) e n ≪≫
          structureSheafTensorPowerIso (Spec (CommRingCat.of B)) n =
        (Scheme.Modules.pullbackIntegerTensorPowerIso i M hM (n : ℤ)).symm ≪≫
          (Scheme.Modules.pullback i).mapIso α ≪≫
            sectionKernelDifferenceBoundaryIso_of_range_subset q j s t hs ht hsj htj i his hit :=
  Stacks.Kummer.exists_sameFibreSectionKernel_root_compatible_frame
    R q j s t hs ht hsj htj hst B i his hit hn0 hn

#print axioms Stacks.Kummer.exists_schemeTensorPower_iso_sameFibreSectionKernel_differenceSheaf
#print axioms Stacks.Kummer.exists_sameFibreSectionKernel_root_compatible_frame
