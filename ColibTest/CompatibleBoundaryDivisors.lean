/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.CompatibleBoundaryFrames

/-!
# Compatible boundary frames retain the prescribed root frame

The auxiliary frame is produced with only local-base module-finiteness. The supplied frame
of the original invertible module remains fixed in the literal section equation.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

example (R B : Type u) [CommRing R] [IsLocalRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B] (L : (Spec (CommRingCat.of B)).Modules)
    [SheafOfModules.IsInvertible (Spec (CommRingCat.of B)).sheaf.obj
      (Spec (CommRingCat.of B)).ringCatSheaf.property L] :
    Nonempty (L ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :=
  nonempty_frame_of_module_finite R B L

example (R B : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] (n : ℕ)
    {X U S : Scheme.{u}} [IsAffine S] [U.IsQuasiAffine]
    (f : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion f]
    (q : X ⟶ S) [IsProper q] (i : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (M : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (e : (pullback i).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :
    ∃ C : ℤ, ∀ d : ℤ, C ≤ d →
      let H := (pullback f).obj (twistingSheaf (polyGrading R n) d)
      ∃ eH : (pullback i).obj H ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf,
      ∃ a : Γ((pullbackTwistFunctor R n f d).obj M, ⊤),
        Hom.app (pullbackTensorFrame i M H e eH).hom ⊤ (pullbackGlobalSections i _ a) =
          (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
        Flat ((Stacks.Divisors.zeroScheme X ((pullbackTwistFunctor R n f d).obj M) a).subschemeι ≫
          q) := by
  obtain ⟨C, hC⟩ := exists_compatible_boundary_framed_divisor_pair R B n f q i j hcover M e
  refine ⟨C, fun d hd => ?_⟩
  obtain ⟨eH, a, b, ha, -, hA, -, -, -, -, -⟩ := hC d hd
  exact ⟨eH, a, ha, hA.2⟩

#print axioms nonempty_frame_of_module_finite
#print axioms pullbackTensorFrame
#print axioms pullbackTwistUnitIso
#print axioms isInvertible_pullbackProjectiveTwist
#print axioms exists_compatible_boundary_framed_divisor_pair
