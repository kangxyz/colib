/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorFiberMap

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- This is flat without assuming the original incidence-to-image finite map is flat.
example (t : correspondenceIncidence f g h z w) :
    Flat (correspondenceRemainingExteriorFiberMap f g h i z w v t) :=
  flat_correspondenceRemainingExteriorFiberMap f g h i z w v t

-- No genericity, reducedness, or injectivity of exterior labels is needed for this degree identity.
example (t : correspondenceIncidence f g h z w)
    (a : (correspondenceLeftExteriorProjection f g h i z w v).fiber t) :
    (correspondenceRemainingExteriorFiberMap f g h i z w v t).residueDegree a =
      (correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree
        ((correspondenceLeftExteriorProjection f g h i z w v).fiberι t a) :=
  correspondenceRemainingExteriorFiberMap_residueDegree f g h i z w v t a

#check Stacks.Chow.correspondenceRemainingExteriorFiberMap
#check Stacks.Chow.correspondenceRemainingExteriorFiberMap_isPullback
#check Stacks.Chow.finite_correspondenceOriginalImageResidueField
#check Stacks.Chow.isFinite_correspondenceRemainingExteriorFiberMap
#check Stacks.Chow.flat_correspondenceRemainingExteriorFiberMap
#check Stacks.Chow.correspondenceRemainingExteriorFiberMap_fiberι
#check Stacks.Chow.correspondenceRemainingExteriorFiberMap_residueDegree
#check Stacks.Chow.correspondenceRemainingExteriorFiberPointEquiv
#check Stacks.Chow.finsum_correspondenceRemainingExteriorFiber_eq
#check Stacks.Chow.correspondenceLeftExteriorFiberLength_eq_fiberStalkLength
