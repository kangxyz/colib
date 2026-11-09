/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Correspondences.Additive.Ext
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle

/-!
# Signed additive extension of the actual incidence Tor correspondence

Two applications of the native finite-correspondence additive extension give
an actual biadditive pairing. Its generator value is the actual geometric
`incidenceTorCorrespondence`, not a supplied cycle or an assumed composition
law. Signed coefficients multiply. No unit or associativity theorem is claimed.

Original source: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/TorCycle.lean`.
The native subgroup extensionality replaces the source `Finsupp` presentation.
The field is arbitrary, and the smooth factors may be disconnected or empty.
The only geometric inputs to the generator value are the two actual admissible
correspondence points; neither coefficients nor a composition law are supplied.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]

/-- The actual incidence Tor correspondence extended additively in both variables. -/
@[colib_tag "COL-0351",
  colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/TorCycle.lean"
  "adaptation" "Actual incidence Tor composition"]
def incidenceTorPairing : finiteCorrespondences f g →+
    finiteCorrespondences g h →+ finiteCorrespondences f h :=
  liftFiniteCorrespondence f g fun z hz =>
    liftFiniteCorrespondence g h fun w hw => incidenceTorCorrespondence f g h z w hz hw

/-- Signed prime coefficients multiply, with their signs retained. -/
@[simp]
theorem incidenceTorPairing_single
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (m n : ℤ) :
    incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz m)
      (singleFiniteCorrespondence g h w hw n) =
      (m * n) • incidenceTorCorrespondence f g h z w hz hw := by
  unfold incidenceTorPairing
  rw [liftFiniteCorrespondence_single]
  change m • (liftFiniteCorrespondence g h (A := finiteCorrespondences f h)
    (fun w hw => incidenceTorCorrespondence f g h z w hz hw)
    (singleFiniteCorrespondence g h w hw n)) = _
  rw [liftFiniteCorrespondence_single, smul_smul]

@[simp]
theorem incidenceTorPairing_single_one
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
      (singleFiniteCorrespondence g h w hw 1) = incidenceTorCorrespondence f g h z w hz hw := by
  rw [incidenceTorPairing_single, one_mul, one_smul]

theorem incidenceTorPairing_add_left (a b : finiteCorrespondences f g)
    (c : finiteCorrespondences g h) :
    incidenceTorPairing f g h (a + b) c =
      incidenceTorPairing f g h a c + incidenceTorPairing f g h b c := by
  exact congrArg (fun F : finiteCorrespondences g h →+ finiteCorrespondences f h => F c)
    ((incidenceTorPairing f g h).map_add a b)

theorem incidenceTorPairing_add_right (a : finiteCorrespondences f g)
    (b c : finiteCorrespondences g h) :
    incidenceTorPairing f g h a (b + c) =
      incidenceTorPairing f g h a b + incidenceTorPairing f g h a c :=
  (incidenceTorPairing f g h a).map_add b c

@[simp]
theorem incidenceTorPairing_zero_left (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h 0 b = 0 := by
  exact congrArg (fun F : finiteCorrespondences g h →+ finiteCorrespondences f h => F b)
    (incidenceTorPairing f g h).map_zero

@[simp]
theorem incidenceTorPairing_zero_right (a : finiteCorrespondences f g) :
    incidenceTorPairing f g h a 0 = 0 :=
  (incidenceTorPairing f g h a).map_zero

@[simp]
theorem incidenceTorPairing_neg_left (a : finiteCorrespondences f g)
    (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h (-a) b = -incidenceTorPairing f g h a b := by
  exact congrArg (fun F : finiteCorrespondences g h →+ finiteCorrespondences f h => F b)
    ((incidenceTorPairing f g h).map_neg a)

@[simp]
theorem incidenceTorPairing_neg_right (a : finiteCorrespondences f g)
    (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h a (-b) = -incidenceTorPairing f g h a b :=
  (incidenceTorPairing f g h a).map_neg b

theorem incidenceTorPairing_zsmul_left (n : ℤ) (a : finiteCorrespondences f g)
    (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h (n • a) b = n • incidenceTorPairing f g h a b := by
  exact congrArg (fun F : finiteCorrespondences g h →+ finiteCorrespondences f h => F b)
    ((incidenceTorPairing f g h).map_zsmul n a)

theorem incidenceTorPairing_zsmul_right (n : ℤ) (a : finiteCorrespondences f g)
    (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h a (n • b) = n • incidenceTorPairing f g h a b :=
  (incidenceTorPairing f g h a).map_zsmul n b

/-- Signed generator coefficients remain visible after evaluating the native output cycle. -/
theorem incidenceTorPairing_single_apply
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (m n : ℤ) (y : pullback (C := Scheme) f h) :
    (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz m)
      (singleFiniteCorrespondence g h w hw n)).val y =
      (m * n) * (incidenceTorCorrespondence f g h z w hz hw).val y := by
  exact congrArg (fun c : finiteCorrespondences f h => c.val y)
    (incidenceTorPairing_single f g h z w hz hw m n)

/-- Subtraction in the first input retains the actual signed Tor correspondence. -/
theorem incidenceTorPairing_sub_left (a b : finiteCorrespondences f g)
    (c : finiteCorrespondences g h) :
    incidenceTorPairing f g h (a - b) c =
      incidenceTorPairing f g h a c - incidenceTorPairing f g h b c := by
  exact congrArg (fun F : finiteCorrespondences g h →+ finiteCorrespondences f h => F c)
    ((incidenceTorPairing f g h).map_sub a b)

/-- Subtraction in the second input retains the actual signed Tor correspondence. -/
theorem incidenceTorPairing_sub_right (a : finiteCorrespondences f g)
    (b c : finiteCorrespondences g h) :
    incidenceTorPairing f g h a (b - c) =
      incidenceTorPairing f g h a b - incidenceTorPairing f g h a c :=
  (incidenceTorPairing f g h a).map_sub b c

/-- Agreement on actual prime Tor correspondences determines a biadditive pairing. -/
theorem incidenceTorPairing_unique
    (F : finiteCorrespondences f g →+ finiteCorrespondences g h →+ finiteCorrespondences f h)
    (hF : ∀ (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
      (w : pullback (C := Scheme) g h) (hw : IsFiniteCorrespondencePoint g h w),
      F (singleFiniteCorrespondence f g z hz 1) (singleFiniteCorrespondence g h w hw 1) =
        incidenceTorCorrespondence f g h z w hz hw) : F = incidenceTorPairing f g h := by
  apply finiteCorrespondences.biaddHom_ext f g h
  intro z hz w hw
  rw [hF z hz w hw, incidenceTorPairing_single_one]

end Stacks.Chow
