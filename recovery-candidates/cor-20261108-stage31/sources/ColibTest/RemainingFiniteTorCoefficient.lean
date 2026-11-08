/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorCoefficient

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- The comparison uses the entire model and its actual prime; it has no reducedness hypothesis.
example [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x)) :
    letI := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
    (correspondenceRemainingFiniteGenericEquivMinPrime f g h i z w v hz hw x q).1 =
      (isAffineOpen_top
        (correspondenceRemainingFiniteModel f g h i z w v x)).primeIdealOf ⟨q.1, trivial⟩ :=
  correspondenceRemainingFiniteGenericEquivMinPrime_eq_primeIdealOf f g h i z w v hz hw x q

#check Stacks.Chow.correspondenceRemainingFiniteGenericEquivMinPrime_eq_primeIdealOf
#check Stacks.Chow.natCast_length_localized_correspondenceRemainingFiniteTorModule
#check Stacks.Chow.finsum_signed_length_localized_correspondenceRemainingFiniteTorModule
