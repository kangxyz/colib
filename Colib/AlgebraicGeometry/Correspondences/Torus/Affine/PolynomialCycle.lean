/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialClosedImmersion
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.LinearGraph

/-!
# Whole polynomial quotients as native finite correspondences

The cycle is the finite pushforward of the actual quotient scheme's fundamental
cycle. Every generic stalk length is retained, including repeated factors and
nonreduced coefficients. No field, normality, smoothness, irreducibility, or
reducedness premise is needed for this producer. Reducedness is used only for
comparison with the existing coefficient-one graph correspondence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial TopologicalSpace
open Function.locallyFinsuppWithin Stacks.Chow

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]

attribute [local instance] Classical.propDecidable

local instance : IsSeparated (multiplicativeGroupBaseChange S ↘ S) := by
  change IsSeparated (pullback.snd
    (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from S))
  infer_instance

local instance : LocallyOfFiniteType (multiplicativeGroupBaseChange S ↘ S) := by
  change LocallyOfFiniteType (pullback.snd
    (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from S))
  infer_instance

/-- The actual polynomial quotient scheme is Noetherian, including its nilpotents. -/
theorem quotient_isNoetherian (p : R[X]) :
    IsNoetherian (Spec (.of (AdjoinRoot p))) := by
  infer_instance

/-- The whole polynomial quotient, with actual generic lengths, in the native group. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Torus/Affine/PolynomialCycles.lean:42-65"
  "adaptation" "Whole monic quotient fundamental cycle in the retained native torus ambient"]
def polynomialCycle (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic)
    (hu : IsUnit (p.coeff 0)) :
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) := by
  letI := quotient_isNoetherian p
  letI := inclusion_isClosedImmersion f p hu
  letI : IsFinite (inclusion f p hu ≫ pullback.fst _ _) := by
    rw [inclusion_fst]
    exact projection_isFinite p hp
  letI : Flat (inclusion f p hu ≫ pullback.fst _ _) := by
    rw [inclusion_fst]
    exact projection_flat p hp
  exact finiteFlatSpanFundamental f (multiplicativeGroupBaseChange S ↘ S) (inclusion f p hu)

/-- The native cycle underlying the actual finite correspondence. -/
theorem polynomialCycle_val (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic)
    (hu : IsUnit (p.coeff 0)) :
    letI := quotient_isNoetherian p
    letI := inclusion_isClosedImmersion f p hu
    (polynomialCycle f p hp hu).val =
      finiteCyclePushforward (inclusion f p hu)
        (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot p)))) := rfl

/-- Closed immersion preserves the literal length of every quotient generic stalk. -/
theorem polynomialCycle_apply_generic (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0))
    (x : genericPoints (Spec (.of (AdjoinRoot p)))) :
    (polynomialCycle f p hp hu).val (inclusion f p hu x.val) =
      ((Module.length ((Spec (.of (AdjoinRoot p))).presheaf.stalk x.val)
        ((Spec (.of (AdjoinRoot p))).presheaf.stalk x.val)).toNat : ℤ) := by
  have := quotient_isNoetherian p
  have := inclusion_isClosedImmersion f p hu
  rw [polynomialCycle_val, finiteCyclePushforward_apply_of_isClosedImmersion]
  exact AlgebraicCycle.fundamentalCycle_apply_generic _ x

/-- The producer sums the whole quotient's actual generic lengths, not reduced weights. -/
theorem polynomialCycle_eq_sum (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) :
    letI := quotient_isNoetherian p
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite
      (Spec (.of (AdjoinRoot p)))).fintype
    (polynomialCycle f p hp hu).val =
      ∑ x : genericPoints (Spec (.of (AdjoinRoot p))),
        single (inclusion f p hu x.val)
          ((Module.length ((Spec (.of (AdjoinRoot p))).presheaf.stalk x.val)
            ((Spec (.of (AdjoinRoot p))).presheaf.stalk x.val)).toNat : ℤ) := by
  have := quotient_isNoetherian p
  have := inclusion_isClosedImmersion f p hu
  rw [polynomialCycle_val, AlgebraicCycle.fundamentalCycle,
    finiteCyclePushforward_ofGenericCoefficients]
  simp only [residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over arbitrary coefficients the linear cycle is the graph of the full fundamental cycle. -/
theorem polynomialCycle_linear_fundamental (f : Spec (.of R) ⟶ S) (v : Rˣ) :
    letI : IsClosedImmersion (unitGraphMap f v) :=
      isClosedImmersion_correspondenceGraphMap _ _ _ _
    (polynomialCycle f (Polynomial.X - C (v : R)) (monic_X_sub_C _)
      (linear_constant_isUnit v)).val =
        finiteCyclePushforward (unitGraphMap f v)
          (AlgebraicCycle.fundamentalCycle (Spec (.of R))) := by
  have := quotient_isNoetherian (Polynomial.X - C (v : R))
  have := inclusion_isClosedImmersion f (Polynomial.X - C (v : R)) (linear_constant_isUnit v)
  have : IsClosedImmersion (unitGraphMap f v) :=
    isClosedImmersion_correspondenceGraphMap _ _ _ _
  rw [polynomialCycle_val]
  have h := finiteCyclePushforward_comp_apply (projection (Polynomial.X - C (v : R)))
    (unitGraphMap f v)
    (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot (Polynomial.X - C (v : R))))))
  have hi : finiteCyclePushforward (projection (Polynomial.X - C (v : R)))
      (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot (Polynomial.X - C (v : R)))))) =
        AlgebraicCycle.fundamentalCycle (Spec (.of R)) := by
    have hIso := finiteCyclePushforward_fundamentalCycle_iso
      (asIso (projection (Polynomial.X - C (v : R))))
    dsimp only [asIso] at hIso
    exact hIso
  rw [hi] at h
  simpa only [← inclusion_linear f v] using h.symm

/-- On reduced affine sources, the linear polynomial gives the existing native graph. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Torus/Affine/LinearGraph.lean:93-126"
  "adaptation" "Whole quotient cycle equals the native unit graph with all source components"]
theorem polynomialCycle_linear_graph [_root_.IsReduced R]
    (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) :
    polynomialCycle f (Polynomial.X - C (v : R)) (monic_X_sub_C _) (linear_constant_isUnit v) =
      unitGraphCycle f v hR := by
  have : IsClosedImmersion (unitGraphMap f v) :=
    isClosedImmersion_correspondenceGraphMap _ _ _ _
  apply Subtype.ext
  rw [polynomialCycle_linear_fundamental]
  exact finiteCyclePushforward_fundamentalCycle_graph f
    (multiplicativeGroupBaseChange S ↘ S) (nativeAffineTorusPoint f v).left
    (affineUnitPoint_over f v)

/-- Every signed coefficient survives the genuine linear graph comparison. -/
theorem zsmul_polynomialCycle_linear_graph [_root_.IsReduced R]
    (f : Spec (.of R) ⟶ S) (v : Rˣ)
    (hR : (genericPoints (Spec (.of R))).Finite) (n : ℤ) :
    n • polynomialCycle f (Polynomial.X - C (v : R)) (monic_X_sub_C _)
        (linear_constant_isUnit v) = n • unitGraphCycle f v hR := by
  rw [polynomialCycle_linear_graph f v hR]

end AlgebraicGeometry.NativeTorusPolynomial
