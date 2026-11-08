/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStageExteriorBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceLeftIntermediateSupportProduct f g h i z w v)

example : IsPullback (correspondenceLeftIntermediateToTripleSupport f g h i z w v)
    (pullback.fst _ _ : correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶
      correspondenceIncidence f g h z w)
    (correspondenceTripleSupportProjection f g h i z w v)
    (correspondenceIncidenceToSupportProduct f g h z w) :=
  correspondenceLeftIntermediate_support_isPullback f g h i z w v

example [IsSeparated g] :
    RingHom.ker ((correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap x).hom =
      (RingHom.ker ((correspondenceIncidenceToSupportProduct f g h z w).stalkMap
        (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x)).hom).map
          (correspondenceLeftExteriorSupportStalkMap f g h i z w v x) :=
  correspondenceLeftIntermediate_support_stalkMap_ker f g h i z w v x

example [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)] :
    (correspondenceLeftExteriorSupportStalkMap f g h i z w v x).Flat :=
  flat_correspondenceLeftExteriorSupportStalkMap f g h i z w v x

#check correspondenceLeftExterior_originalMiddle_koszul_baseChange
#check correspondenceLeftIntermediate_support_stalk_isPushout
