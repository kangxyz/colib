module

import Colib.AlgebraicGeometry.Correspondences.Composition.Associativity

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  [IsSeparated g] [IsSeparated h] [IsSeparated i]

example (α : finiteCorrespondences f g) (β : finiteCorrespondences g h)
    (γ : finiteCorrespondences h i) :
    incidenceTorPairing f h i (incidenceTorPairing f g h α β) γ =
      incidenceTorPairing f g i α (incidenceTorPairing g h i β γ) :=
  incidenceTorPairing_assoc k f g h i α β γ

example (α : finiteCorrespondences f g) (β : finiteCorrespondences g h)
    (γ : finiteCorrespondences h i) (n : ℤ) :
    incidenceTorPairing f h i (incidenceTorPairing f g h (-α) (n • β)) γ =
      incidenceTorPairing f g i (-α) (incidenceTorPairing g h i (n • β) γ) :=
  incidenceTorPairing_assoc k f g h i (-α) (n • β) γ

example (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (v : pullback (C := Scheme) h i)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    incidenceTorPairing f h i
        (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
          (singleFiniteCorrespondence g h w hw 1)) (singleFiniteCorrespondence h i v hv 1) =
      incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
        (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw 1)
          (singleFiniteCorrespondence h i v hv 1)) :=
  incidenceTorPairing_assoc_single_one k f g h i z w v hz hw hv
