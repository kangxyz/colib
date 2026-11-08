/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.Pairing

/-! Source-only tests on the actual signed Tor pairing. No compiler has been run.
All fields are arbitrary; no connectedness or nonempty-factor instances are present. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]

example (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (m n : ℤ) :
    incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz m)
      (singleFiniteCorrespondence g h w hw n) =
      (m * n) • incidenceTorCorrespondence f g h z w hz hw :=
  incidenceTorPairing_single f g h z w hz hw m n

-- Concrete negative input signs are retained, rather than discarded by natural coefficients.
example (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz (-2))
      (singleFiniteCorrespondence g h w hw 3) =
      (-6 : ℤ) • incidenceTorCorrespondence f g h z w hz hw := by
  simpa using incidenceTorPairing_single f g h z w hz hw (-2) 3

example (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (m n : ℤ) (y : pullback (C := Scheme) f h) :
    (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz m)
      (singleFiniteCorrespondence g h w hw n)).val y =
      (m * n) * (incidenceTorCorrespondence f g h z w hz hw).val y :=
  incidenceTorPairing_single_apply f g h z w hz hw m n y

example (a : finiteCorrespondences f g) (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h (-a) b = -incidenceTorPairing f g h a b :=
  incidenceTorPairing_neg_left f g h a b

example (a : finiteCorrespondences f g) : incidenceTorPairing f g h a 0 = 0 :=
  incidenceTorPairing_zero_right f g h a

example (a : finiteCorrespondences f g) (b c : finiteCorrespondences g h) :
    incidenceTorPairing f g h a (b - c) =
      incidenceTorPairing f g h a b - incidenceTorPairing f g h a c :=
  incidenceTorPairing_sub_right f g h a b c

-- Cancellation is in the actual signed native correspondence group.
example (a : finiteCorrespondences f g) (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h (a + -a) b = 0 := by simp

-- The actual generator formula uniquely determines the biadditive pairing.
example
    (F : finiteCorrespondences f g →+ finiteCorrespondences g h →+ finiteCorrespondences f h)
    (hF : ∀ (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
      (w : pullback (C := Scheme) g h) (hw : IsFiniteCorrespondencePoint g h w),
      F (singleFiniteCorrespondence f g z hz 1) (singleFiniteCorrespondence g h w hw 1) =
        incidenceTorCorrespondence f g h z w hz hw) : F = incidenceTorPairing f g h :=
  incidenceTorPairing_unique f g h F hF

-- Empty smooth source factors are retained, not excluded by a connectedness convention.
example [IsEmpty X] (a : finiteCorrespondences f g) (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h a b = 0 := by
  have ha : a = 0 := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro z
    exact isEmptyElim (pullback.fst f g z)
  simp [ha]

-- Empty smooth final factors likewise give the zero pairing.
example [IsEmpty Z] (a : finiteCorrespondences f g) (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h a b = 0 := by
  have hb : b = 0 := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro w
    exact isEmptyElim (pullback.snd g h w)
  simp [hb]
