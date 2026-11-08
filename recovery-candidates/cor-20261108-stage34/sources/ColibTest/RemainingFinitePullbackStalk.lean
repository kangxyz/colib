module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFinitePullbackStalk

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.ModuleStalkSpecialization

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceLeftImageIncidence f g h i z w v)
  (q : correspondenceRemainingFiniteModel f g h i z w v x)
  (M : (correspondenceLeftIntermediateSupportProduct f g h i z w v).Modules)

example : Function.Bijective
    (correspondenceRemainingFinitePullbackStalkLinearEquiv f g h i z w v x q M) :=
  (correspondenceRemainingFinitePullbackStalkLinearEquiv f g h i z w v x q M).bijective

example {r : ℕ}
    (s : Fin r → (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceRemainingFiniteModelProjection f g h i z w v x q)) :
    IsIso (correspondenceRemainingFinitePullbackKoszulStalkIso f g h i z w v x q M s).hom :=
  inferInstance
