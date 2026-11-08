/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageExteriorSquare
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BaseChangeFiberMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Fixed original labels in the full exterior finite map

For an original incidence point `t`, the actual full exterior image square
induces a map from the source exterior fibre over `t` to the image exterior
fibre over `toImage t`. Native fibre base change proves that this is the base
change of the actual residue-field map at `t`. It is finite and flat even
though the original incidence-to-image map need not be flat.

The point equivalence retains both labels: the original incidence point and
the image exterior point. It does not assume that either projection is
injective, and it does not replace a scheme-theoretic fibre by its reduction.
Native fibre-stalk comparison also identifies the existing source fibre
factor with the length of the actual fibre local ring. These are geometric
inputs to the weighted branch formula, not an assumed regrouping identity.

References: Stacks 01JT (scheme-theoretic fibres), 01TF (residue-field
finiteness), and 02M0 (the later weighted length calculation).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "pSource" =>
  correspondenceLeftExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "pImage" =>
  correspondenceLeftImageExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "imageMap" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "originalMap" =>
  (correspondenceIncidenceMap f g h z w).toImage

/-- The map of full scheme-theoretic exterior fibres at one retained original point. -/
abbrev correspondenceRemainingExteriorFiberMap (t : correspondenceIncidence f g h z w) :
    (pSource).fiber t ⟶ (pImage).fiber (originalMap t) :=
  restrictedFiberMap pImage pSource imageMap originalMap
    (correspondenceLeftIntermediateImageMap_projection f g h i z w v) t

/-- The actual fibre map is the base change of the actual original residue-field map. -/
theorem correspondenceRemainingExteriorFiberMap_isPullback
    (t : correspondenceIncidence f g h z w) :
    IsPullback (correspondenceRemainingExteriorFiberMap f g h i z w v t)
      ((pSource).fiberToSpecResidueField t) ((pImage).fiberToSpecResidueField (originalMap t))
      (Spec.map ((originalMap).residueFieldMap t)) :=
  isPullback_fiberToSpecResidueField_of_isPullback
    (correspondenceLeftIntermediateImageMap_isPullback f g h i z w v).flip t

/-- The fixed original residue extension is finite by the actual incidence-to-image map. -/
theorem finite_correspondenceOriginalImageResidueField [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w) :
    letI := ((originalMap).residueFieldMap t).hom.toAlgebra
    Module.Finite
      ((correspondenceIntermediateImage f g h z w).residueField (originalMap t))
      ((correspondenceIncidence f g h z w).residueField t) := by
  let := isFinite_correspondenceIncidenceToImage f g h z w hz hw
  exact residueField_finite_of_locallyQuasiFinite originalMap t

/-- The whole fibre map is finite, without flatness of the original finite map. -/
theorem isFinite_correspondenceRemainingExteriorFiberMap [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w) :
    IsFinite (correspondenceRemainingExteriorFiberMap f g h i z w v t) := by
  have hf : IsFinite (Spec.map ((originalMap).residueFieldMap t)) :=
    (IsFinite.SpecMap_iff _).mpr (finite_correspondenceOriginalImageResidueField
      f g h z w hz hw t)
  exact MorphismProperty.of_isPullback
    (correspondenceRemainingExteriorFiberMap_isPullback f g h i z w v t).flip hf

/-- Flatness here belongs to a base change of fields, not to the original finite image map. -/
theorem flat_correspondenceRemainingExteriorFiberMap
    (t : correspondenceIncidence f g h z w) :
    Flat (correspondenceRemainingExteriorFiberMap f g h i z w v t) := by
  have hf : Flat (Spec.map ((originalMap).residueFieldMap t)) := by
    rw [Flat.SpecMap_iff]
    let := ((originalMap).residueFieldMap t).hom.toAlgebra
    change Module.Flat
      ((correspondenceIntermediateImage f g h z w).residueField (originalMap t))
      ((correspondenceIncidence f g h z w).residueField t)
    infer_instance
  exact MorphismProperty.of_isPullback
    (correspondenceRemainingExteriorFiberMap_isPullback f g h i z w v t).flip hf

/-- Inclusion into the full exterior commutes with the fibre map. -/
@[reassoc]
theorem correspondenceRemainingExteriorFiberMap_fiberι
    (t : correspondenceIncidence f g h z w) :
    correspondenceRemainingExteriorFiberMap f g h i z w v t ≫
        (pImage).fiberι (originalMap t) = (pSource).fiberι t ≫ imageMap :=
  restrictedFiberMap_fiberι ..

/-- The residue weight at a fibre point is exactly the original full exterior-map weight. -/
theorem correspondenceRemainingExteriorFiberMap_residueDegree
    (t : correspondenceIncidence f g h z w) (a : (pSource).fiber t) :
    (correspondenceRemainingExteriorFiberMap f g h i z w v t).residueDegree a =
      (imageMap).residueDegree ((pSource).fiberι t a) := by
  have he := congrArg (fun q => Scheme.Hom.residueDegree q a)
    (correspondenceRemainingExteriorFiberMap_fiberι f g h i z w v t)
  simpa only [residueDegree_comp, residueDegree_eq_one_of_isPreimmersion,
    mul_one, one_mul] using he

/-- Points of a fixed fibre-map fibre are precisely the full exterior points carrying both
fixed labels. Neither projection is assumed injective. -/
def correspondenceRemainingExteriorFiberPointEquiv
    (t : correspondenceIncidence f g h z w) (q : (pImage).fiber (originalMap t)) :
    {a : (pSource).fiber t // correspondenceRemainingExteriorFiberMap f g h i z w v t a = q} ≃
      {a : correspondenceLeftIntermediateSupportProduct f g h i z w v //
        imageMap a = (pImage).fiberι (originalMap t) q ∧ pSource a = t} where
  toFun a := ⟨(pSource).fiberι t a.1, by
    constructor
    · have he := congrArg (fun k => k a.1)
        (correspondenceRemainingExteriorFiberMap_fiberι f g h i z w v t)
      simpa only [Scheme.Hom.comp_apply, a.2] using he.symm
    · exact ((pSource).fiberHomeo t a.1).2⟩
  invFun a := ⟨((pSource).fiberHomeo t).symm ⟨a.1, a.2.2⟩, by
    apply ((pImage).fiberι (originalMap t)).isEmbedding.injective
    have he := congrArg (fun k => k (((pSource).fiberHomeo t).symm ⟨a.1, a.2.2⟩))
      (correspondenceRemainingExteriorFiberMap_fiberι f g h i z w v t)
    simp only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_fiberHomeo_symm] at he
    exact he.trans a.2.1⟩
  left_inv a := by
    apply Subtype.ext
    apply ((pSource).fiberι t).isEmbedding.injective
    exact (pSource).fiberι_fiberHomeo_symm t _
  right_inv a := Subtype.ext ((pSource).fiberι_fiberHomeo_symm t _)

/-- Reindexing by the proved point equivalence preserves every original branch weight. -/
theorem finsum_correspondenceRemainingExteriorFiber_eq
    (t : correspondenceIncidence f g h z w) (q : (pImage).fiber (originalMap t))
    {M : Type*} [AddCommMonoid M]
    (weight : correspondenceLeftIntermediateSupportProduct f g h i z w v → M) :
    (∑ᶠ a : {a : (pSource).fiber t //
        correspondenceRemainingExteriorFiberMap f g h i z w v t a = q},
      weight ((pSource).fiberι t a.1)) =
      ∑ᶠ a : {a : correspondenceLeftIntermediateSupportProduct f g h i z w v //
        imageMap a = (pImage).fiberι (originalMap t) q ∧ pSource a = t}, weight a.1 :=
  finsum_eq_of_bijective (correspondenceRemainingExteriorFiberPointEquiv f g h i z w v t q)
    (correspondenceRemainingExteriorFiberPointEquiv f g h i z w v t q).bijective (fun _ => rfl)

/-- The existing exterior fibre factor is the actual local-ring length of the full fibre.
This equality does not discard nilpotents or assert that this length is one. -/
theorem correspondenceLeftExteriorFiberLength_eq_fiberStalkLength
    (a : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    correspondenceLeftExteriorFiberLength f g h i z w v a =
      (Module.length (((pSource).fiber (pSource a)).presheaf.stalk ((pSource).asFiber a))
        (((pSource).fiber (pSource a)).presheaf.stalk ((pSource).asFiber a))).toNat := by
  unfold correspondenceLeftExteriorFiberLength
  congr 1
  rw [Module.length_eq_of_surjective
    (S := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk a)
    (Ideal.Quotient.mk_surjective (I := Ideal.map ((pSource).stalkMap a).hom
      (IsLocalRing.maximalIdeal
        ((correspondenceIncidence f g h z w).presheaf.stalk (pSource a)))))]
  exact Module.length_eq_of_ringEquiv (quotientStalkEquivFiberStalk pSource a)

end Stacks.Chow
