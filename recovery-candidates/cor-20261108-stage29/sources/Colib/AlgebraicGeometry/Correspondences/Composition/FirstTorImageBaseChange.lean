/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorModule
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorFiberLength
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction

/-!
# Original Tor direct image commutes with the full exterior base change

The actual whole exterior Cartesian square is supplied by the lower geometric
owner `RemainingImageExteriorSquare`. In every original Tor degree, native
affine base change identifies the
pushforward of the actual exterior Tor sheaf with the exterior pullback of its
original direct image. This is a global sheaf isomorphism with the canonical
base-change map, not a coefficient equality supplied by the caller.

No flatness is assumed for the finite incidence-to-image map. In fact this
ordinary affine base-change comparison does not require flatness of the third
support either. Flatness enters later when taking cycle multiplicities, where
both source and image exterior fibre lengths must be retained. This is the
exact sheaf square needed for regrouping split exterior labels by the original
pair image, not yet that weighted-cycle regrouping itself.

The native provider is Stacks 02KG at the pinned affine base-change owner.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The original Tor degree pushed to the full scheme-theoretic intermediate image. -/
abbrev correspondencePairImageTorSheaf (n : ℕ) :
    (correspondenceIntermediateImage f g h z w).Modules :=
  (Scheme.Modules.pushforward (correspondenceIncidenceMap f g h z w).toImage).obj
    (correspondencePairTorSheaf f g h z w n)

/-- Native affine base change for the actual original Tor degree and actual full image square.
The finite-map and exterior-map flatness hypotheses are both unnecessary for this isomorphism. -/
def correspondencePairImageTorSheafExteriorIso [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceIntersectionAmbient f g h)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) (n : ℕ) :
    (Scheme.Modules.pullback (correspondenceLeftImageExteriorProjection f g h i z w v)).obj
        (correspondencePairImageTorSheaf f g h z w n) ≅
      (Scheme.Modules.pushforward (correspondenceLeftIntermediateImageMap f g h i z w v)).obj
        (correspondenceLeftExteriorTorSheaf f g h i z w v n) := by
  let := isFinite_correspondenceIncidenceToImage f g h z w hz hw
  let := (isQuasicoherent_isFiniteType_correspondencePairTorSheaf f g h z w n).1
  let sq := correspondenceLeftIntermediateImageMap_isPullback f g h i z w v
  let := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    sq (correspondencePairTorSheaf f g h z w n)
  exact asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans sq.w).app
    (correspondencePairTorSheaf f g h z w n))

end Stacks.Chow
