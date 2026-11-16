/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedCoarseNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenCofinality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectConnectingNaturality

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSupportAcyclicKComparison.lean`.

# The original supported and acyclic coefficient K-evaluations

The actual coefficient support-to-acyclic evaluation induces precisely the
original supported section K-equivalence followed by the inverse geometric
acyclic-to-supported K-equivalence. Its inverse therefore carries the original
geometric change-of-weak-equivalence boundary to the existing supported
bounded-flat boundary followed by inverse section evaluation. These comparisons
hold in every nonnegative degree without any compactness hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientSupportedEvaluation
  boundedAboveFlatCoefficientSupportedSectionEquivalence

/-- Actual acyclic evaluation is the original supported evaluation followed by conversion. -/
theorem boundedAboveFlatCoefficientSupportAcyclicEvaluationKEquiv_eq (a : Under R) (n : ℕ) :
    boundedAboveFlatCoefficientEvaluationKEquiv
        (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
        (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
        (boundedAboveFlatCoefficientSupportAcyclicEquivalence f a)
        (boundedAboveFlatCoefficientSupportAcyclicEvaluation_exact f a)
        (boundedAboveFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n =
      (boundedAboveFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).trans
        (boundedAboveFlatPerfectAcyclicSupportedKEquiv (schemeMap f a) n).symm := by
  ext x
  change boundedAboveFlatCoefficientEvaluationKEquiv _ _ _ _ _ n x =
    KMap (boundedAboveFlatPerfectSupportedToAcyclic_exact (schemeMap f a)) n
      (boundedAboveFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n x)
  simpa only [KMap_id, MonoidHom.id_apply, boundedAboveFlatCoefficientSupportedSectionKEquiv] using
    boundedAboveFlatCoefficientEvaluationKEquiv_natural
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
      (boundedAboveFlatPerfectSupportedWaldhausen (schemeMap f a))
      (boundedAboveFlatCoefficientSupportedSectionEquivalence (schemeMap f a))
      (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor_exact (schemeMap f a))
      (boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact (schemeMap f a))
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
      (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
      (boundedAboveFlatCoefficientSupportAcyclicEquivalence f a)
      (boundedAboveFlatCoefficientSupportAcyclicEvaluation_exact f a)
      (boundedAboveFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a)
      (IsExact.id _ _)
      (boundedAboveFlatPerfectSupportedToAcyclic_exact (schemeMap f a))
      (by
        change 𝟭 _ ⋙ boundedAboveFlatCoefficientSupportAcyclicEvaluation f a ≅
          (boundedAboveFlatCoefficientSupportedSectionEquivalence (schemeMap f a)).functor ⋙
            boundedAboveFlatPerfectSupportedToAcyclic (schemeMap f a)
        rw [Functor.id_comp, boundedAboveFlatCoefficientSupportedSectionEquivalence_functor]
        exact Iso.refl _) n x

/-- Inverse actual acyclic evaluation uses exactly the original two inverse comparisons. -/
theorem boundedAboveFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_apply (a : Under R) (n : ℕ)
    (y : (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a))).K n) :
    (boundedAboveFlatCoefficientEvaluationKEquiv
        (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
        (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
        (boundedAboveFlatCoefficientSupportAcyclicEquivalence f a)
        (boundedAboveFlatCoefficientSupportAcyclicEvaluation_exact f a)
        (boundedAboveFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n).symm y =
      (boundedAboveFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).symm
        (boundedAboveFlatPerfectAcyclicSupportedKEquiv (schemeMap f a) n y) := by
  rw [boundedAboveFlatCoefficientSupportAcyclicEvaluationKEquiv_eq]
  rfl

/-- The original geometric boundary becomes the existing supported bounded-flat boundary. -/
theorem boundedAboveFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_connecting
    (a : Under R) (n : ℕ) (x : BoundedAboveFlatPerfectOpenK (schemeMap f a) (n + 1)) :
    (boundedAboveFlatCoefficientEvaluationKEquiv
        (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
        (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
        (boundedAboveFlatCoefficientSupportAcyclicEquivalence f a)
        (boundedAboveFlatCoefficientSupportAcyclicEvaluation_exact f a)
        (boundedAboveFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n).symm
      (changeWeakConnectingHom (boundedAboveFlatPerfectOpenNested (schemeMap f a))
        (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence
          (schemeMap f a)) n x) =
      (boundedAboveFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).symm
        (boundedAboveFlatPerfectOpenConnectingHom (schemeMap f a) n x) := by
  rw [boundedAboveFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_apply]
  rfl

end AlgebraicGeometry.Scheme.Modules
