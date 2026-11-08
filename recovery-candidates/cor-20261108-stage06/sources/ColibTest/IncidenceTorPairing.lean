module

import Colib.AlgebraicGeometry.Correspondences.Composition.Pairing

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]

-- Newly reconstructed tests, current validation pending TorCycle recovery.
example (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (m n : ℤ) :
    incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz m)
      (singleFiniteCorrespondence g h w hw n) =
      (m * n) • incidenceTorCorrespondence f g h z w hz hw :=
  incidenceTorPairing_single f g h z w hz hw m n

example (a : finiteCorrespondences f g) (b : finiteCorrespondences g h) :
    incidenceTorPairing f g h (-a) b = -incidenceTorPairing f g h a b :=
  incidenceTorPairing_neg_left f g h a b

example (a : finiteCorrespondences f g) : incidenceTorPairing f g h a 0 = 0 :=
  incidenceTorPairing_zero_right f g h a
