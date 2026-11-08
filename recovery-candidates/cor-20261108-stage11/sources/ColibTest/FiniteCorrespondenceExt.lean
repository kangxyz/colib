module

import Colib.AlgebraicGeometry.Correspondences.Additive.Ext

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u v

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

-- New recovery regressions; historical four-example bytes are unavailable.
example (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) (n : ℤ) :
    singleFiniteCorrespondence f g z hz n = n • singleFiniteCorrespondence f g z hz 1 :=
  singleFiniteCorrespondence_eq_zsmul f g z hz n

example {A : Type v} [AddCommGroup A] (F G : finiteCorrespondences f g →+ A)
    (hFG : ∀ (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z),
      F (singleFiniteCorrespondence f g z hz 1) = G (singleFiniteCorrespondence f g z hz 1)) :
    F = G :=
  finiteCorrespondences.addHom_ext_one f g F G hFG
