/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorBound

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

section

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]

-- No global dimension bound, perfect field, or arbitrary family-vanishing input is supplied.
example (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    ∃ d : ℕ, ∀ n : ℕ, d < n →
      IsZero (correspondenceRemainingFiniteTorModule f g h i z w v x n) :=
  exists_correspondenceRemainingFiniteTorModule_degreeBound k f g h i z w v hz hw x

end

#check Stacks.Chow.length_correspondenceRemainingFiniteTorSheaf_stalk_eq_zero_of_lt

#check Stacks.Chow.exists_correspondenceRemainingFiniteTorModule_degreeBound

#check Stacks.Chow.finite_nonzero_correspondenceRemainingFiniteTorModule
