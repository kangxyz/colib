/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImage

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- The full right square is Cartesian without smoothness, fields, reduction or flatness.
example :
    IsPullback (correspondenceRightTripleToImageIncidence f g h i z w v)
      (correspondenceRightTripleIncidenceToSupportProduct f g h i z w v)
      (correspondenceRightImageIncidenceInclusion f g h i z w v)
      (correspondenceRightIntermediateImageMap f g h i z w v) :=
  correspondenceRightTripleToImageIncidence_isPullback f g h i z w v

example [IsSeparated g] :
    (correspondenceRightTripleIncidenceToSupportProduct f g h i z w v).ker =
      (correspondenceRightImageIncidenceInclusion f g h i z w v).ker.comap
        (correspondenceRightIntermediateImageMap f g h i z w v) :=
  ker_correspondenceRightTripleIncidenceToSupportProduct f g h i z w v

-- Only the last pair is required to be admissible for the exterior finite map.
example [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceRightIntermediateImageMap f g h i z w v) :=
  isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv

-- No flatness of the first support over Y is used here either.
example [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceTripleToRightImageIncidence f g h i z w v) :=
  isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv

example :
    correspondenceTripleToRightImageIncidence f g h i z w v ≫
        correspondenceRightImageIncidenceMap f g h i z w v =
      correspondenceTripleIncidenceMap f g h i z w v :=
  correspondenceTripleToRightImageIncidence_map f g h i z w v

example [IsSeparated i] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceRightImageIncidenceSource f g h i z w v) :=
  isFinite_correspondenceRightImageIncidenceSource f g h i z w v hz hw hv

-- The cycle is arbitrary and signed; this does not assume a Tor comparison.
example [IsSeparated i] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (c : AlgebraicCycle (correspondenceTripleIncidence f g h i z w v) ℤ) :
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    letI := isFinite_correspondenceRightImageIncidenceMap f g h i z w v hz hw hv
    letI := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
    finiteCyclePushforward (correspondenceRightImageIncidenceMap f g h i z w v)
        (finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v) c) =
      finiteCyclePushforward (correspondenceTripleIncidenceMap f g h i z w v) c :=
  finiteCyclePushforward_tripleToRightImageIncidence f g h i z w v hz hw hv c

example [IsSeparated g] [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (c : AlgebraicCycle (correspondenceRightTripleIncidence f g h i z w v) ℤ) :
    letI := isFinite_correspondenceRightTripleToImageIncidence f g h i z w v hw hv
    letI := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
    finiteCyclePushforward (correspondenceRightImageIncidenceInclusion f g h i z w v)
        (finiteCyclePushforward (correspondenceRightTripleToImageIncidence f g h i z w v) c) =
      finiteCyclePushforward (correspondenceRightIntermediateImageMap f g h i z w v)
        (finiteCyclePushforward
          (correspondenceRightTripleIncidenceToSupportProduct f g h i z w v) c) :=
  finiteCyclePushforward_rightImageIncidence f g h i z w v hw hv c
