/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.SameFibreDifference
import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryRoot

/-!
# Tests for same-specialization section differences on a smooth open

None of the tests assumes smoothness of the ambient separated scheme, nor that
its fibre is a curve, nor any Picard-divisibility or Cartier certificate.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open Stacks.SheafOfModules.Invertible

universe u

example {X U S : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) (h : Set.range s ⊆ Set.range j) :
    IsEffectiveCartierDivisor s.ker :=
  isEffectiveCartierDivisor_sectionKernel_of_range_subset q j s hs h

example {X U S T : Scheme.{u}} (q : X ⟶ S) [IsSeparated q] (g : T ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s : S ⟶ X) (hs : s ≫ q = 𝟙 S) (h : Set.range s ⊆ Set.range j) :
    IsPullbackDefined (pullback.fst q g) s.ker :=
  isPullbackDefined_sectionKernel_of_range_subset q g j s hs h

example {X U S T : Scheme.{u}} (q : X ⟶ S) [IsSeparated q] (g : T ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hst : g ≫ s = g ≫ t) :
    (Scheme.Modules.pullback (pullback.fst q g)).obj (differenceSheaf s.ker t.ker) ≅
      SheafOfModules.unit (pullback q g).ringCatSheaf :=
  sectionKernelDifferencePullbackUnitIsoOfRangeSubset q g j s t hs ht hsj htj hst

local instance (S : Scheme.{u}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

/-- The literal unit bundle supplies the tensor root used on the closed fibre. -/
example (X : Scheme.{u}) (n : ℕ) :
    Stacks.SheafOfModules.schemeTensorPower X (SheafOfModules.unit X.ringCatSheaf)
        (Stacks.SheafOfModules.isInvertible_unit X.presheaf X.ringCatIsSheaf) (n : ℤ) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  structureSheafTensorPowerIso X n

/-- Composite exponents require no Picard argument on the fibre: the unit module
and the actual specialization comparison are an explicit tensor root. -/
example {X U S T : Scheme.{u}} (q : X ⟶ S) [IsSeparated q] (g : T ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (s t : S ⟶ X) (hs : s ≫ q = 𝟙 S) (ht : t ≫ q = 𝟙 S)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hst : g ≫ s = g ≫ t) :
    ∃ (M : (pullback q g).Modules)
      (hM : Stacks.SheafOfModules.IsInvertible (pullback q g).presheaf
        (pullback q g).ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower (pullback q g) M hM (6 : ℤ) ≅
        (Scheme.Modules.pullback (pullback.fst q g)).obj (differenceSheaf s.ker t.ker)) := by
  let M : (pullback q g).Modules := SheafOfModules.unit (pullback q g).ringCatSheaf
  have hM : Stacks.SheafOfModules.IsInvertible (pullback q g).presheaf
      (pullback q g).ringCatIsSheaf M := Stacks.SheafOfModules.isInvertible_unit _ _
  exact ⟨M, hM, ⟨structureSheafTensorPowerIso (pullback q g) 6 ≪≫
    (sectionKernelDifferencePullbackUnitIsoOfRangeSubset q g j s t hs ht hsj htj hst).symm⟩⟩

#print axioms Stacks.Divisors.isEffectiveCartierDivisor_sectionKernel_of_range_subset
#print axioms Stacks.Divisors.isEffectiveCartierDivisor_baseChangedSection_of_range_subset
#print axioms Stacks.Divisors.differenceSheafSelfIso
#print axioms Stacks.Divisors.sectionKernelDifferencePullbackIsoOfRangeSubset
#print axioms Stacks.Divisors.sectionKernelDifferencePullbackUnitIsoOfRangeSubset
#print axioms Stacks.Divisors.sectionKernelDifferenceBoundaryIsoOfRangeSubset
