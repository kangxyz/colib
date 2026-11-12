/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.NonzeroCompatiblePair

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.ProjectiveCohomology

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

open AlgebraicGeometry.Scheme.Modules

example {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (hs : Stacks.Divisors.IsEffectiveCartierDivisor
      (AlgebraicGeometry.zeroScheme X L s)) : s ≠ 0 :=
  globalSection_ne_zero_of_isEffectiveCartierDivisor_zeroScheme L s hs

example
    (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] (n : ℕ)
    {X U V : Scheme.{u}} [IsIntegral X] [IsAffine V] [U.IsQuasiAffine]
    (g : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion g]
    (q : X ⟶ V) [IsProper q] (i : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (e : (pullback i).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :
    ∃ C : ℤ, ∀ d : ℤ, C ≤ d →
      let H := (pullback g).obj (twistingSheaf (polyGrading R n) d)
      ∃ eH : (pullback i).obj H ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf,
      ∃ (a : Γ((pullbackTwistFunctor R n g d).obj M, ⊤)) (b : H.sections),
        a ≠ 0 ∧ b.eval (op ⊤) ≠ 0 ∧
        Hom.app (pullbackTensorFrame i M H e eH).hom ⊤ (pullbackGlobalSections i _ a) =
          (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
        Hom.app eH.hom ⊤ (pullbackGlobalSections i H (b.eval (op ⊤))) =
          (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
        Stacks.Divisors.IsRelativeEffectiveCartierDivisor q
          (AlgebraicGeometry.zeroScheme X ((pullbackTwistFunctor R n g d).obj M) a) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((AlgebraicGeometry.zeroScheme X
            ((pullbackTwistFunctor R n g d).obj M) a).subschemeι ≫ q) ∧
        Set.range (AlgebraicGeometry.zeroScheme X
          ((pullbackTwistFunctor R n g d).obj M) a).subschemeι ⊆
          Set.range j ∧
        Stacks.Divisors.IsRelativeEffectiveCartierDivisor q
          (AlgebraicGeometry.zeroScheme X H (b.eval (op ⊤))) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((AlgebraicGeometry.zeroScheme X H (b.eval (op ⊤))).subschemeι ≫ q) ∧
        Set.range (AlgebraicGeometry.zeroScheme X H (b.eval (op ⊤))).subschemeι ⊆ Set.range j :=
  exists_nonzero_compatible_boundary_framed_divisor_pair R B n g q i j hcover M e

#print axioms AlgebraicGeometry.globalSection_ne_zero_of_isEffectiveCartierDivisor_zeroScheme
#print axioms exists_nonzero_compatible_boundary_framed_divisor_pair
