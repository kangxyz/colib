/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorStalk

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) (n : ℕ) :
    Module.length ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
        ((correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) =
      Module.length ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q))
        ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk
          (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q)) := by
  exact length_correspondenceRightRemainingFiniteTorSheaf_stalk
    f g h i z w v x q n

example [IsSeparated h] [IsSeparated i]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient g h i)]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) (n : ℕ) :
    letI := isAffine_correspondenceRightRemainingFiniteModel f g h i z w v hw hv x
    let p := (isAffineOpen_top
      (correspondenceRightRemainingFiniteModel f g h i z w v x)).primeIdealOf ⟨q, trivial⟩
    Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl
          (correspondenceRightRemainingFiniteTorModule f g h i z w v x n)) =
      Module.length ((correspondenceRightRemainingFiniteModel f g h i z w v x).presheaf.stalk q)
        ((correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) := by
  exact length_localized_correspondenceRightRemainingFiniteTorModule
    f g h i z w v hw hv x q n

end Stacks.Chow
