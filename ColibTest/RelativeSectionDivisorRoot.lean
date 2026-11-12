/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.EtaleCohomology.RelativeSectionDivisorRoot

/-!
# Tests for framed roots of actual relative section-divisor differences
-/

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology Stacks.Divisors
open Stacks.SheafOfModules.Invertible

universe u

/-- Composite exponent, with no supplied Picard class or closed-fibre tensor root. -/
example (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    [SmoothOfRelativeDimension 1 q]
    [IsCurve (IsLocalRing.ResidueField R) (closedFibreProjection R q)]
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hn : IsUnit (6 : R)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (6 : ℤ) ≅
        Stacks.Divisors.differenceSheaf s.ker t.ker) :=
  Stacks.Kummer.exists_schemeTensorPower_iso_relativeSectionKernel_differenceSheaf
    R q s t hs ht (by decide) hn


local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- The final endpoint supplies the root, its isomorphism, and a frame with the exact
canonical boundary compatibility, even for a possibly nonreduced finite algebra. -/
example
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    [SmoothOfRelativeDimension 1 q]
    [IsCurve (IsLocalRing.ResidueField R) (closedFibreProjection R q)]
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
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
            sectionKernelDifferenceBoundaryIso q s t hs ht i his hit :=
  Stacks.Kummer.exists_relativeSectionKernel_root_compatible_frame
    R q s t hs ht B i his hit hn0 hn

#print axioms Stacks.Kummer.exists_schemeTensorPower_iso_relativeSectionKernel_differenceSheaf
#print axioms Stacks.Kummer.exists_relativeSectionKernel_root_compatible_frame
