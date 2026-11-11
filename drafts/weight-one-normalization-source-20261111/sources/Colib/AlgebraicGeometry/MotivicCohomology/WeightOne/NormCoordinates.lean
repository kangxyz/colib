/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.Norm
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.PointNormDictionary

/-!
# Spectrum coordinates for the actual global reduced norm

The canonical affine chart of `Spec R` is induced by the inverse of `ΓSpecIso`.
The original spectrum-section naturality therefore identifies the global norm
component with the concrete spectrum norm, after cancelling the actual unit
restriction isomorphism. No new norm, quotient, or affine presentation is chosen.

At the original field object, the same `ΓSpecIso` identifies the value on every
represented reduced class with its signed whole-support determinant norm.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers NativeTorusPolynomial

variable (k : Type u) [Field k]

section Spectrum

variable {R : Type u} [CommRing R]
variable (f : Spec (.of R) ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]
variable [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]

attribute [local instance] AffineSectionCoordinates.sections_isIntegrallyClosed
  AffineSectionCoordinates.sections_isNoetherianRing

/-- The actual global component on a spectrum is the original spectrum-section norm. -/
theorem reducedNorm_spec :
    (reducedNorm k).app (op (mk f)) = specSectionsReducedNorm f := by
  let : IsIntegral (mk f).left := inferInstanceAs (IsIntegral (Spec (.of R)))
  have hleft : (AffineSectionCoordinates.iso (mk f)).hom.left =
      Spec.map (CommRingCat.ofHom (Scheme.ΓSpecIso (.of R)).inv.hom) := by
    change (Spec (.of R)).isoSpec.inv = Spec.map (Scheme.ΓSpecIso (.of R)).inv
    rw [Scheme.isoSpec_Spec_inv]
  have hn := specSectionsReducedNorm_natural f
    (AffineSectionCoordinates.structureMap (mk f))
    (Scheme.ΓSpecIso (.of R)).inv.hom
    (AffineSectionCoordinates.iso (mk f)).hom hleft
  calc
    (reducedNorm k).app (op (mk f)) = affineReducedNorm (mk f) :=
      reducedNorm_app k (mk f)
    _ = (rawReducedTorus k).map (AffineSectionCoordinates.iso (mk f)).hom.op ≫
        specSectionsReducedNorm (AffineSectionCoordinates.structureMap (mk f)) ≫
          (affineSectionIso (mk f) (largeUnitsPresheaf (Spec (.of k)))).inv := rfl
    _ = specSectionsReducedNorm f ≫
        (largeUnitsPresheaf (Spec (.of k))).map
          (AffineSectionCoordinates.iso (mk f)).hom.op ≫
            (affineSectionIso (mk f) (largeUnitsPresheaf (Spec (.of k)))).inv := by
      rw [← Category.assoc, hn, Category.assoc]
    _ = specSectionsReducedNorm f := by
      change specSectionsReducedNorm f ≫
        (affineSectionIso (mk f) (largeUnitsPresheaf (Spec (.of k)))).hom ≫
          (affineSectionIso (mk f) (largeUnitsPresheaf (Spec (.of k)))).inv = _
      rw [Iso.hom_inv_id, Category.comp_id]

/-- The original affine counit takes the actual global component to the support norm. -/
@[reassoc] theorem reducedNorm_spec_units :
    (reducedNorm k).app (op (mk f)) ≫ (specUnitsIso f).hom = reducedNormApp f := by
  rw [reducedNorm_spec]
  simp only [specSectionsReducedNorm, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The same comparison on an arbitrary section of the original reduced torus. -/
theorem reducedNorm_spec_apply (z : (rawReducedTorus k).obj (op (mk f))) :
    (specUnitsIso f).hom ((reducedNorm k).app (op (mk f)) z) = reducedNormApp f z :=
  congrArg (fun h => h z) (reducedNorm_spec_units k f)

end Spectrum

/-- On the literal reduced class of every signed point cycle, the global norm is its norm. -/
theorem reducedNorm_point_toReduced (z : point k ⟶ pointTarget k) :
    (specUnitsIso (𝟙 (Spec (.of k)))).hom
      ((reducedNorm k).app (op (base (Spec (.of k))))
        ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up z))) =
      ULift.up (pointCycleNorm k z) := by
  calc
    (specUnitsIso (𝟙 (Spec (.of k)))).hom
        ((reducedNorm k).app (op (base (Spec (.of k))))
          ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up z))) =
        reducedNormApp (𝟙 (Spec (.of k)))
          ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up z)) :=
      reducedNorm_spec_apply k (𝟙 (Spec (.of k))) _
    _ = ULift.up (pointCycleNorm k z) := reducedPointNorm_toReduced k z

end AlgebraicGeometry.MotivicCohomology.WeightOne
