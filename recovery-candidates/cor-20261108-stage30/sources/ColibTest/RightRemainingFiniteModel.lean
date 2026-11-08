/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteModel

/-! Typed consumers of actual right geometry; no comparison hypothesis is supplied. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- The entire model is exactly the native pullback, not a chosen stalk or residue field.
example (x : correspondenceRightImageIncidence f g h i z w v) :
    correspondenceRightRemainingFiniteModel f g h i z w v x =
      Stacks.FormalFunctions.stalkBaseChange (correspondenceRightIntermediateImageMap f g h i z w v)
        (correspondenceRightImageIncidenceInclusion f g h i z w v x) := rfl

example (x : correspondenceRightImageIncidence f g h i z w v) :
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x) =
      (correspondenceRightRemainingFiniteModelStructure f g h i z w v x).appTop.hom.comp
        (Scheme.ΓSpecIso (correspondenceRightRemainingImageStalk f g h i z w v x)).inv.hom :=
  algebraMap_correspondenceRightRemainingFiniteRing f g h i z w v x

example (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    correspondenceRightIntermediateImageMap f g h i z w v
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) =
      (correspondenceRightIntermediateImageProduct f g h i z w v).fromSpecStalk
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)
        (correspondenceRightRemainingFiniteModelStructure f g h i z w v x q) :=
  correspondenceRightRemainingFiniteModel_image_point f g h i z w v x q

example [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    IsFinite (correspondenceRightRemainingFiniteModelStructure f g h i z w v x) :=
  isFinite_correspondenceRightRemainingFiniteModelStructure f g h i z w v hw hv x

example [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    IsAffine (correspondenceRightRemainingFiniteModel f g h i z w v x) :=
  isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x

example [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    Module.Finite (correspondenceRightRemainingImageStalk f g h i z w v x)
      (correspondenceRightRemainingFiniteRing f g h i z w v x) :=
  moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x

example [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    Finite (MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) :=
  finite_maximalSpectrum_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x

example (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    IsIso ((correspondenceRightRemainingFiniteModelProjection f g h i z w v x).stalkMap q) :=
  isIso_correspondenceRightRemainingFiniteModelProjection_stalkMap f g h i z w v x q

example [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x)) :
    (correspondenceRightRemainingFinitePairGenericLabel f g h i z w v x q).1 =
      correspondenceRightExteriorProjection f g h i z w v
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1) :=
  correspondenceRightRemainingFinitePairGenericLabel_val f g h i z w v x q

example (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    (correspondenceRightRemainingFiniteModelStructure f g h i z w v x).residueDegree q =
      (correspondenceRightIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) :=
  residueDegree_correspondenceRightRemainingFiniteModelStructure f g h i z w v x q

-- Arbitrary fields discharge the only base flatness used in original-pair generic labels.
example (k : Type u) [Field k]
    (f' : X ⟶ Spec (.of k)) (g' : Y ⟶ Spec (.of k))
    (h' : Z ⟶ Spec (.of k)) (i' : W ⟶ Spec (.of k))
    (z' : pullback (C := Scheme) f' g') (w' : pullback (C := Scheme) g' h')
    (v' : pullback (C := Scheme) h' i')
    (x : correspondenceRightImageIncidence f' g' h' i' z' w' v')
    (q : genericPoints (correspondenceRightRemainingFiniteModel f' g' h' i' z' w' v' x)) :
    genericPoints (correspondenceIncidence g' h' i' w' v') :=
  correspondenceRightRemainingFinitePairGenericLabel f' g' h' i' z' w' v' x q
