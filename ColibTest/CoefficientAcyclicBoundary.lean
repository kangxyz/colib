/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportAcyclicKComparison

/-!
Original supported section evaluation identifies the unchanged geometric
relative-open boundary, without compactness assumptions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u

namespace Consumer.CoefficientSupportAcyclicKComparison
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Inverse coefficient evaluation detects vanishing of the actual supported boundary. -/
theorem inverse_acyclic_boundary_eq_one_iff (a : Under R) (n : ℕ)
    (x : BoundedAboveFlatPerfectOpenK (schemeMap f a) (n + 1)) :
    (boundedAboveFlatCoefficientEvaluationKEquiv
        (boundedAboveFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
        (acyclicStructure (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
        (boundedAboveFlatCoefficientSupportAcyclicEquivalence f a)
        (boundedAboveFlatCoefficientSupportAcyclicEvaluation_exact f a)
        (boundedAboveFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n).symm
      (changeWeakConnectingHom (boundedAboveFlatPerfectOpenNested (schemeMap f a))
        (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a))
        n x) = 1 ↔
      boundedAboveFlatPerfectOpenConnectingHom (schemeMap f a) n x = 1 := by
  rw [boundedAboveFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_connecting]
  exact (boundedAboveFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).symm.map_eq_one_iff

end Consumer.CoefficientSupportAcyclicKComparison

#print axioms
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_connecting
