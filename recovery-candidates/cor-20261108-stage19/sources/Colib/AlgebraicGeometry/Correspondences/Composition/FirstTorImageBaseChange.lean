/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorModule
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction

/-!
# Original Tor direct image commutes with the full exterior base change

The actual whole first-incidence exterior and the whole intermediate-image
exterior form a Cartesian square over the original finite incidence-to-image
map. In every original Tor degree, native affine base change identifies the
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

/-- The projection from the whole image exterior to the whole original intermediate image. -/
abbrev correspondenceLeftImageExteriorProjection :
    correspondenceLeftIntermediateImageProduct f g h i z w v ⟶
      correspondenceIntermediateImage f g h z w :=
  pullback.fst _ _

/-- The actual finite exterior map commutes with the two original projections. -/
@[reassoc]
theorem correspondenceLeftIntermediateImageMap_projection :
    correspondenceLeftIntermediateImageMap f g h i z w v ≫
        correspondenceLeftImageExteriorProjection f g h i z w v =
      correspondenceLeftExteriorProjection f g h i z w v ≫
        (correspondenceIncidenceMap f g h z w).toImage := by
  simp [correspondenceLeftIntermediateImageMap, correspondenceLeftImageExteriorProjection,
    correspondenceLeftExteriorProjection]

/-- The full image square is Cartesian, before any reduction or restriction to generic points. -/
theorem correspondenceLeftIntermediateImageMap_isPullback :
    IsPullback (correspondenceLeftExteriorProjection f g h i z w v)
      (correspondenceLeftIntermediateImageMap f g h i z w v)
      (correspondenceIncidenceMap f g h z w).toImage
      (correspondenceLeftImageExteriorProjection f g h i z w v) := by
  have hp : IsPullback
      (correspondenceLeftExteriorProjection f g h i z w v)
      (correspondenceLeftIntermediateImageMap f g h i z w v ≫ pullback.snd _ _)
      ((correspondenceIncidenceMap f g h z w).toImage ≫
        (correspondenceIntermediateImageTarget f g h z w ≫ h))
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) := by
    simpa only [correspondenceLeftExteriorProjection, correspondenceLeftIntermediateImageMap,
      pullback.map_snd, Category.comp_id, correspondenceIntermediateImageTarget,
      ← Category.assoc, Scheme.Hom.toImage_imageι, correspondenceIncidenceMap_snd] using
      (IsPullback.of_hasPullback (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))
  exact hp.of_bot (correspondenceLeftIntermediateImageMap_projection f g h i z w v).symm
    (IsPullback.of_hasPullback (correspondenceIntermediateImageTarget f g h z w ≫ h)
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))

/-- The full source exterior is locally Noetherian under the actual Euler hypotheses.
This follows from its finite map to the full image exterior, without another support hypothesis. -/
theorem isLocallyNoetherian_correspondenceLeftIntermediateSupportProduct_of_image
    [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v) := by
  let := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
  exact LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceLeftIntermediateImageMap f g h i z w v)

/-- The full exterior fibre factor is genuinely finite at every generic model label under
exactly the actual image-Euler hypotheses, not only an extended-length truncation. -/
theorem length_correspondenceRemainingExteriorFiber_ne_top [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : TopologicalSpace.genericPoints
      (correspondenceRemainingFiniteModel f g h i z w v x)) :
    let y := correspondenceRemainingFiniteModelProjection f g h i z w v x q.1
    Module.length
      ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk y)
      ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk y ⧸
        Ideal.map ((correspondenceLeftExteriorProjection f g h i z w v).stalkMap y).hom
          (IsLocalRing.maximalIdeal ((correspondenceIncidence f g h z w).presheaf.stalk
            (correspondenceLeftExteriorProjection f g h i z w v y)))) ≠ ⊤ := by
  let := isLocallyNoetherian_correspondenceLeftIntermediateSupportProduct_of_image
    f g h i z w v hz hw
  exact length_correspondenceLeftExteriorFiber_ne_top f g h i z w v
    (correspondenceRemainingFiniteGenericLabel f g h i z w v x q)

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
