/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.SameFibreSectionDivisorRoot
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.NonzeroCompatiblePair

/-!
# The same original strict-local root and auxiliary framed pair

Proper Kummer specialization constructs a root of the actual difference of the two
section kernels and its compatible frame on the entire finite boundary. The auxiliary
pair is chosen only after that root and uses that exact frame. Neither a root, a boundary
frame, a finite pair nor the desired equality of transfer actions is an input.

The local coefficient ring is genuinely strictly henselian. No presheaf is evaluated
on its spectrum, and this theorem does not identify it with an object of a smooth site.
An actual projective embedding is retained as geometric input to the section producer.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj Stacks.ProjectiveCohomology
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors Stacks.EtaleCohomology
open Stacks.SheafOfModules (schemeTensorPower)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace Stacks.Kummer

/-- Equal residue-field section morphisms produce one original root and its original
auxiliary finite framed pair. All boundary equations retain that same root and frame. -/
theorem exists_sameFibreSectionKernel_root_framed_pair
    (R B : Type u) [CommRing R] [StrictlyHenselianLocalRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] (m : ℕ)
    {X U : Scheme.{u}} [IsIntegral X] [U.IsQuasiAffine]
    (g : X ⟶ Proj (polyGrading R m)) [IsClosedImmersion g]
    (q : X ⟶ Spec (.of R)) [IsProper q]
    (i : Spec (CommRingCat.of B) ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (s t : Spec (.of R) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _)
    (hsj : Set.range s ⊆ Set.range j) (htj : Set.range t ⊆ Set.range j)
    (hst : residueFieldPoint R ≫ s = residueFieldPoint R ≫ t)
    (his : Disjoint (Set.range i) (Set.range s))
    (hit : Disjoint (Set.range i) (Set.range t))
    {n : ℕ} (hn0 : n ≠ 0) (hn : IsUnit (n : R)) :
    ∃ (M : X.Modules)
      (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
      (α : schemeTensorPower X M hM (n : ℤ) ≅ differenceSheaf s.ker t.ker),
      letI := hM
      letI : AlgebraicGeometry.SheafOfModules.IsInvertible
          (Spec (CommRingCat.of B)).presheaf (ringSheafCond (Spec (CommRingCat.of B)))
          ((pullback i).obj M) :=
        Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
          (Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom M)
      ∃ e : (pullback i).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf,
        (tensorPowerMap (Spec (CommRingCat.of B)) e n ≪≫
          structureSheafTensorPowerIso (Spec (CommRingCat.of B)) n =
        (pullbackIntegerTensorPowerIso i M hM (n : ℤ)).symm ≪≫ (pullback i).mapIso α ≪≫
          sectionKernelDifferenceBoundaryIsoOfRangeSubset q j s t hs ht hsj htj i his hit) ∧
      ∃ d : ℤ,
      let N := (pullback g).obj (twistingSheaf (polyGrading R m) d)
      ∃ eN : (pullback i).obj N ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf,
      ∃ (a : Γ((pullbackTwistFunctor R m g d).obj M, ⊤)) (b : N.sections),
        a ≠ 0 ∧ b.eval (op ⊤) ≠ 0 ∧
        Hom.app (pullbackTensorFrame i M N e eN).hom ⊤ (pullbackGlobalSections i _ a) =
          (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
        Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) =
          (1 : Γ(Spec (CommRingCat.of B), ⊤)) ∧
        IsRelativeEffectiveCartierDivisor q
          (AlgebraicGeometry.zeroScheme X ((pullbackTwistFunctor R m g d).obj M) a) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((AlgebraicGeometry.zeroScheme X
            ((pullbackTwistFunctor R m g d).obj M) a).subschemeι ≫ q) ∧
        Set.range (AlgebraicGeometry.zeroScheme X
          ((pullbackTwistFunctor R m g d).obj M) a).subschemeι ⊆
          Set.range j ∧
        IsRelativeEffectiveCartierDivisor q (AlgebraicGeometry.zeroScheme X N (b.eval (op ⊤))) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((AlgebraicGeometry.zeroScheme X N (b.eval (op ⊤))).subschemeι ≫ q) ∧
        Set.range (AlgebraicGeometry.zeroScheme X N (b.eval (op ⊤))).subschemeι ⊆
          Set.range j := by
  obtain ⟨M, hM, α, e, he⟩ := exists_sameFibreSectionKernel_root_compatible_frame
    R q j s t hs ht hsj htj hst B i his hit hn0 hn
  let := hM
  let : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property M := hM.toAlgebraicGeometry
  obtain ⟨d, hd⟩ := exists_nonzero_compatible_boundary_framed_divisor_pair
    R B m g q i j hcover M e
  exact ⟨M, hM, α, e, he, d, hd d le_rfl⟩

end Stacks.Kummer
