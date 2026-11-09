/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageGenericStalk

/-! Typed consumers of actual right geometry; no comparison hypothesis is supplied. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example [IsSeparated g]
    [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    IsIdealOfDefinition (RingHom.ker
      ((correspondenceRightImageIncidenceInclusion f g h i z w v).stalkMap x.1).hom) :=
  isIdealOfDefinition_correspondenceRightRemainingImageStalkKernel f g h i z w v x

example [IsSeparated g]
    (x : correspondenceRightImageIncidence f g h i z w v) :
    RingHom.ker ((correspondenceRightImageIncidenceInclusion f g h i z w v).stalkMap x).hom =
      (IdealSheafData.stalk (pullback.diagonal g).ker
        (correspondenceRightImageMiddlePair f g h i z w v
          (correspondenceRightImageIncidenceInclusion f g h i z w v x))).map
            (correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x) :=
  correspondenceRightRemainingImageStalkKernel_eq_map f g h i z w v x

example [IsSeparated g]
    [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    IsIdealOfDefinition (Ideal.span (Set.range (fun j =>
      correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1 (s j)))) :=
  isIdealOfDefinition_correspondenceRightRemainingImageMiddleList f g h i z w v x s hs

-- The local Noetherian hypothesis comes from the actual finite source-product geometry.
example [IsSeparated i] [LocallyOfFiniteType i] [IsLocallyNoetherian (pullback f g)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v) :=
  isLocallyNoetherian_correspondenceRightIntermediateImageProduct f g h i z w v hz hw hv

example [IsSeparated g] [IsSeparated i] [LocallyOfFiniteType i]
    [IsLocallyNoetherian (pullback f g)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) :
    letI := isLocallyNoetherian_correspondenceRightIntermediateImageProduct
      f g h i z w v hz hw hv
    IsIdealOfDefinition (RingHom.ker
      ((correspondenceRightImageIncidenceInclusion f g h i z w v).stalkMap x.1).hom) := by
  let := isLocallyNoetherian_correspondenceRightIntermediateImageProduct f g h i z w v hz hw hv
  exact isIdealOfDefinition_correspondenceRightRemainingImageStalkKernel f g h i z w v x
