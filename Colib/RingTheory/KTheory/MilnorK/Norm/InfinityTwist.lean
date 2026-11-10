/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenEquivariance
public import Colib.RingTheory.KTheory.MilnorK.Residue.CanonicalRamifiedMap
public import Colib.AlgebraicGeometry.ProjectiveLine.ChartInversionInvolution

/-!
# The actual chosen norm after inversion of the scalar parameter

Adapted from Aglib `Norm/FiniteExtension/InfinityTwist.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 28–76. The original upper
field is unchanged. Its actual scalar action is precomposed with the existing
native projective-line chart inversion. Simultaneous norm equivariance proves
the norm comparison, and native uniformizer independence gives the infinity
residue comparison. All Milnor degrees, including degree zero, are retained.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial _root_.AlgebraicGeometry

universe u

/-- The native origin identification is exactly evaluation at zero after the
canonical quotient identification used by the original infinity residue. -/
theorem residueFieldAtOriginEquiv_symm_comp_quotientRingEquivResidueField
    (k : Type u) [Field k] :
    (residueFieldAtOriginEquiv k).symm.toRingHom.comp
      (quotientRingEquivResidueField (Ideal.span {(X : k[X])})).toRingHom =
      (AdjoinRoot.liftAlgHom (X : k[X]) (Algebra.ofId k k) 0 (by simp)).toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (residueFieldAtOriginEquiv k).injective
  change residueFieldAtOriginEquiv k
    ((residueFieldAtOriginEquiv k).symm
      (quotientRingEquivResidueField (Ideal.span {(X : k[X])})
        (Ideal.Quotient.mk (Ideal.span {(X : k[X])}) p))) =
    residueFieldAtOriginEquiv k (p.eval 0)
  rw [RingEquiv.apply_symm_apply,
    ← residue_algebraMap_eq_quotientRingEquivResidueField]
  change IsLocalRing.residue (localRingAtOrigin k)
    (algebraMap k[X] (localRingAtOrigin k) p) = residueOfConstants k (p.eval 0)
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using residue_algebraMap_polynomial p

variable (k E : Type u) [Field k] [CharZero k] [Field E]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E]

/-- The original upper field with its scalar action pulled back by native inversion. -/
@[instance_reducible]
def infinityTwistAlgebra : Algebra (RatFunc k) E :=
  ((algebraMap (RatFunc k) E).comp (projectiveLineChartInversion k).toRingHom).toAlgebra

omit [CharZero k] in
/-- Precomposing the actual scalar action with inversion preserves finiteness. -/
theorem infinityTwistFinite :
    @FiniteDimensional (RatFunc k) E _ _ (infinityTwistAlgebra k E).toModule := by
  exact RingHom.Finite.comp
    (show (algebraMap (RatFunc k) E).Finite from by
      simpa only [RingHom.finite_algebraMap] using
        (inferInstance : Module.Finite (RatFunc k) E))
    (RingHom.Finite.of_surjective (projectiveLineChartInversion k).toRingHom
      (projectiveLineChartInversion k).surjective)

/-- The native chosen norm for the inverted action, on the original Milnor group. -/
def infinityTwistNorm (n : ℕ) : MilnorKTheory E n →+ MilnorKTheory (RatFunc k) n :=
  let fin := infinityTwistFinite k E
  letI := infinityTwistAlgebra k E
  letI := fin
  milnorKNorm (RatFunc k) E n

/-- Inversion of the scalar action inverts the output of the actual original norm. -/
theorem infinityTwistNorm_eq (n : ℕ) (x : MilnorKTheory E n) :
    infinityTwistNorm k E n x =
      milnorKTransport (projectiveLineChartInversion k).toRingHom n
        (milnorKNorm (RatFunc k) E n x) := by
  have h := @milnorKNorm_map_ringEquiv (RatFunc k) (RatFunc k) E E _ _ _ _
    (inferInstance : Algebra (RatFunc k) E) (infinityTwistAlgebra k E)
    (inferInstance : FiniteDimensional (RatFunc k) E) (infinityTwistFinite k E)
    (inferInstance : CharZero (RatFunc k))
    (projectiveLineChartInversion k) (RingEquiv.refl E)
    (by
      apply RingHom.ext
      intro a
      change algebraMap (RatFunc k) E a = algebraMap (RatFunc k) E
        (projectiveLineChartInversion k (projectiveLineChartInversion k a))
      rw [projectiveLineChartInversion_involutive]) n x
  change milnorKTransport (projectiveLineChartInversion k).toRingHom n
    (milnorKNorm (RatFunc k) E n x) =
      infinityTwistNorm k E n (milnorKTransport (RingHom.id E) n x) at h
  rw [milnorKTransport_id_apply] at h
  exact h.symm

/-- The original infinity residue is the canonical origin residue of the twisted norm. -/
theorem infinityResidue_milnorKNorm_eq_twist (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    infinityResidue (k := k) n (milnorKNorm (RatFunc k) E (n + 1) x) =
      milnorKTransport (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (infinityTwistNorm k E (n + 1) x)) := by
  rw [infinityTwistNorm_eq,
    dvrMilnorTameSymbol'_eq_of_ramified_identity (irreducible_algebraMap_X (k := k))]
  rfl

end Stacks.Chow
