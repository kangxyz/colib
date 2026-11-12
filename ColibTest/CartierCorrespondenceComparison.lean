/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Divisors.SectionKernel
import Colib.AlgebraicGeometry.Correspondences.Divisors.WeilIdentity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] Classical.propDecidable

universe u

noncomputable section

example {X : Scheme.{u}} (Z : PrimeDivisor X) :
    (PrimeDivisor.chowEquiv Z).idealSheaf = Z.idealSheaf := rfl

example {X : Scheme.{u}} (D E : WeilDivisor X) (n : ℤ) :
    WeilDivisor.toAlgebraicCycle (n • (D - E)) =
      n • (WeilDivisor.toAlgebraicCycle D - WeilDivisor.toAlgebraicCycle E) := by
  rw [map_zsmul, map_sub]

example {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (Z : PrimeDivisor X) (x : I.subscheme) (hx : I.subschemeι x = Z.genericPoint) :
    WeilDivisor.toAlgebraicCycle (effectiveCartierWeilDivisor I hI) Z.genericPoint =
      ((Module.length (I.subscheme.presheaf.stalk x)
        (I.subscheme.presheaf.stalk x)).toNat : ℤ) := by
  rw [WeilDivisor.toAlgebraicCycle_genericPoint, effectiveCartierWeilDivisor_apply]
  exact Stacks.Chow.effectiveCartierMultiplicity_eq_stalk_length I Z x hx

example {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    WeilDivisor.toAlgebraicCycle (principalDivisor X f) =
      Stacks.Chow.principalCycle X ((Stacks.Chow.rationalFunctionsEquivFunctionField X).val f) :=
  WeilDivisor.toAlgebraicCycle_principalDivisor f

#print axioms AlgebraicGeometry.WeilDivisor.chowEquiv
#print axioms Stacks.Chow.toAlgebraicCycle_effectiveCartierWeilDivisor
#print axioms AlgebraicGeometry.WeilDivisor.toAlgebraicCycle_principalDivisor


example {C Z : Scheme.{u}} [IsNoetherian C] (r : C ⟶ Z)
    (x y : C) (a b : ℤ) (hxy : r x = r y) :
    Stacks.Chow.noetherianCyclePushforward r
        (Function.locallyFinsuppWithin.single x a + Function.locallyFinsuppWithin.single y b) =
      Function.locallyFinsuppWithin.single (r x)
        (a * (r.residueDegree x : ℤ) + b * (r.residueDegree y : ℤ)) := by
  rw [map_add, Stacks.Chow.noetherianCyclePushforward_single,
    Stacks.Chow.noetherianCyclePushforward_single, ← hxy]
  apply Function.locallyFinsuppWithin.ext
  intro z
  by_cases hz : z = r x <;> simp [Function.locallyFinsuppWithin.single_apply, hz]

example {C X Y S : Scheme.{u}} [IsNoetherian C] [IsIntegral C]
    (p : X ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
    (r : C ⟶ pullback p t) (I : C.IdealSheafData)
    [IsFinite ((I.subschemeι ≫ r) ≫ pullback.fst p t)]
    [Flat ((I.subschemeι ≫ r) ≫ pullback.fst p t)]
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    Stacks.Chow.principalCorrespondenceOfWeilIdentity p t r I I I I hI hI hI hI 0 1
      (by simp) = 0 := by
  apply Subtype.ext
  change WeilDivisor.pushforwardCycle r (principalDivisor C 1) = 0
  rw [principalDivisor_one, map_zero]

example {C X Y S : Scheme.{u}} [IsNoetherian C] [IsNoetherian X] [IsReduced X]
    (p : X ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
    (r : C ⟶ pullback p t) [IsSeparated (r ≫ pullback.fst p t)]
    (s : X ⟶ C) (hs : s ≫ (r ≫ pullback.fst p t) = 𝟙 X) :
    let := Stacks.Chow.sectionKernelProjection_isIso p t r s hs
    Stacks.Chow.finiteFlatDivisorCorrespondence p t r s.ker =
      Stacks.Chow.graphCorrespondenceOfComponents p t (s ≫ r ≫ pullback.snd p t)
        (Stacks.Chow.sectionTarget_base p t r s hs)
        (AlgebraicCycle.fundamentalCycle_genericPoints_finite X) :=
  Stacks.Chow.finiteFlatDivisorCorrespondence_sectionKernel p t r s hs

#print axioms Stacks.Chow.noetherianCyclePushforward_comp_apply
#print axioms Stacks.Chow.pushforwardCycle_effectiveCartierWeilDivisor
#print axioms Stacks.Chow.finiteFlatDivisorCorrespondence_val_apply
#print axioms Stacks.Chow.finiteFlatDivisorCorrespondence_sectionKernel
#print axioms Stacks.Chow.finiteFlatDivisorCorrespondence_sub_eq_of_weilIdentity
