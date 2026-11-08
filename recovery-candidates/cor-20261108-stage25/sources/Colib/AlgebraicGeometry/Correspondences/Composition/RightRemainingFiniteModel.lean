/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageGenericStalk
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.PushforwardStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalBaseIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero

/-!
# The full native finite model for the actual right image map

Specialize the existing FormalFunctions.stalkBaseChange to the genuine finite
map id_F times incidence(G,H)-to-image(G,H), at an actual remaining right-image
incidence point. The model and its algebra are literally the native pullback
and pullbackFromSpecStalkAlgebra, not a separate semilocal or residue-field model.
All source branches and nilpotents are retained.

Finiteness uses only G and H in their given finite-over-source direction. The
localization projection is flat, a preimmersion, and stalkwise an isomorphism;
its actual generic labels and the original finite-map residue degrees are
preserved. Flatness of the finite original-to-image map is neither needed nor
asserted. The original-label equality explicitly uses the native structure point.

This supplies only right finite-model geometry. It does not reconstruct the
common global Tor-family/Euler suppliers or assume any right weighted bracket
comparison. Those families must later be pulled onto this entire native model,
not replaced by the stalk at a chosen point.

The native model proof pattern is reused from RemainingFiniteModel v5, with
the distinct actual right finite map. Source target:
motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Composition/Cycles/RightFirstStageWeightedRemainingCoefficient.lean,
blob 5771cc85d24a32f3610872f2a94d457154d1673b, scoped to its whole-fibre geometry.
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

/-- The whole original exterior above the spectrum of the actual image stalk. -/
abbrev correspondenceRightRemainingFiniteModel
    (x : correspondenceRightImageIncidence f g h i z w v) : Scheme.{u} :=
  FormalFunctions.stalkBaseChange (correspondenceRightIntermediateImageMap f g h i z w v)
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)

/-- Projection to the original full first-stage exterior. -/
abbrev correspondenceRightRemainingFiniteModelProjection
    (x : correspondenceRightImageIncidence f g h i z w v) :
    correspondenceRightRemainingFiniteModel f g h i z w v x ⟶
      correspondenceRightIntermediateSupportProduct f g h i z w v :=
  FormalFunctions.stalkBaseChangeι (correspondenceRightIntermediateImageMap f g h i z w v)
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)

/-- The finite structure morphism to the spectrum of the actual image stalk. -/
abbrev correspondenceRightRemainingFiniteModelStructure
    (x : correspondenceRightImageIncidence f g h i z w v) :
    correspondenceRightRemainingFiniteModel f g h i z w v x ⟶
      Spec (correspondenceRightRemainingImageStalk f g h i z w v x) :=
  FormalFunctions.stalkBaseChangeStructure
    (correspondenceRightIntermediateImageMap f g h i z w v)
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)

/-- The actual full finite ring. It is not replaced by a product of residue fields. -/
abbrev correspondenceRightRemainingFiniteRing
    (x : correspondenceRightImageIncidence f g h i z w v) :=
  Γ(correspondenceRightRemainingFiniteModel f g h i z w v x, ⊤)

/-- The native scalar action through the actual finite structure morphism. -/
@[instance_reducible]
def correspondenceRightRemainingFiniteAlgebra
    (x : correspondenceRightImageIncidence f g h i z w v) :
    Algebra (correspondenceRightRemainingImageStalk f g h i z w v x)
      (correspondenceRightRemainingFiniteRing f g h i z w v x) :=
  FormalFunctions.pullbackFromSpecStalkAlgebra
    (correspondenceRightIntermediateImageMap f g h i z w v)
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)

/-- The native algebra uses the actual structure map, including the inverse ΓSpecIso. -/
theorem algebraMap_correspondenceRightRemainingFiniteRing
    (x : correspondenceRightImageIncidence f g h i z w v) :
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
        (correspondenceRightRemainingFiniteRing f g h i z w v x) =
      (correspondenceRightRemainingFiniteModelStructure f g h i z w v x).appTop.hom.comp
        (Scheme.ΓSpecIso (correspondenceRightRemainingImageStalk f g h i z w v x)).inv.hom := by
  letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let π := correspondenceRightRemainingFiniteModelStructure f g h i z w v x
  change ((Scheme.ΓSpecIso (correspondenceRightRemainingImageStalk f g h i z w v x)).inv ≫
    π.appLE ⊤ ⊤ (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top π ⊤)).hom = _
  simp [Scheme.Hom.appLE]

/-- The original exterior image is the literal native model structure point. -/
theorem correspondenceRightRemainingFiniteModel_image_point
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    correspondenceRightIntermediateImageMap f g h i z w v
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) =
      (correspondenceRightIntermediateImageProduct f g h i z w v).fromSpecStalk
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)
        (correspondenceRightRemainingFiniteModelStructure f g h i z w v x q) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m q)
    (pullback.condition
      (f := correspondenceRightIntermediateImageMap f g h i z w v)
      (g := (correspondenceRightIntermediateImageProduct f g h i z w v).fromSpecStalk
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)))

/-- Finiteness is obtained from the actual finite map by base change. -/
theorem isFinite_correspondenceRightRemainingFiniteModelStructure [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    IsFinite (correspondenceRightRemainingFiniteModelStructure f g h i z w v x) := by
  let := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
  dsimp only [correspondenceRightRemainingFiniteModelStructure,
    FormalFunctions.stalkBaseChangeStructure]
  infer_instance

/-- The whole local base change is affine, even when the exterior is not affine. -/
theorem isAffine_correspondenceRightRemainingFiniteModel [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    IsAffine (correspondenceRightRemainingFiniteModel f g h i z w v x) := by
  let := isFinite_correspondenceRightRemainingFiniteModelStructure f g h i z w v hw hv x
  exact isAffine_of_isAffineHom (correspondenceRightRemainingFiniteModelStructure f g h i z w v x)

/-- The actual full ring is finite over the actual local image ring. -/
theorem moduleFinite_correspondenceRightRemainingFiniteRing [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    Module.Finite (correspondenceRightRemainingImageStalk f g h i z w v x)
      (correspondenceRightRemainingFiniteRing f g h i z w v x) := by
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let := isFinite_correspondenceRightRemainingFiniteModelStructure f g h i z w v hw hv x
  let π := correspondenceRightRemainingFiniteModelStructure f g h i z w v x
  have he : (Scheme.ΓSpecIso (correspondenceRightRemainingImageStalk f g h i z w v x)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).surjective
  have hfinite := (Scheme.Hom.finite_appTop π).comp he
  apply RingHom.finite_algebraMap.mp
  rw [algebraMap_correspondenceRightRemainingFiniteRing]
  exact hfinite

/-- All remaining fibre labels are retained in a finite maximal spectrum. -/
theorem finite_maximalSpectrum_correspondenceRightRemainingFiniteRing [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (x : correspondenceRightImageIncidence f g h i z w v) :
    Finite (MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) := by
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x
  exact Stacks.Length.finite_maximalSpectrum
    (A := correspondenceRightRemainingImageStalk f g h i z w v x)

/-- Flatness belongs to the localization projection, not to the finite map. -/
theorem flat_correspondenceRightRemainingFiniteModelProjection
    (x : correspondenceRightImageIncidence f g h i z w v) :
    Flat (correspondenceRightRemainingFiniteModelProjection f g h i z w v x) := by
  let := flat_fromSpecStalk (correspondenceRightIntermediateImageProduct f g h i z w v)
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)
  dsimp only [correspondenceRightRemainingFiniteModelProjection, FormalFunctions.stalkBaseChangeι]
  infer_instance

/-- The localization projection identifies every actual source local ring. -/
theorem isIso_correspondenceRightRemainingFiniteModelProjection_stalkMap
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    IsIso ((correspondenceRightRemainingFiniteModelProjection f g h i z w v x).stalkMap q) := by
  let := flat_correspondenceRightRemainingFiniteModelProjection f g h i z w v x
  exact isIso_stalkMap_of_flat_isPreimmersion
    (correspondenceRightRemainingFiniteModelProjection f g h i z w v x) q

/-- Every generic local label keeps its actual original exterior generic label. -/
def correspondenceRightRemainingFiniteGenericLabel
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x)) :
    genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v) := by
  let := flat_correspondenceRightRemainingFiniteModelProjection f g h i z w v x
  exact ⟨correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1,
    AlgebraicGeometry.mem_genericPoints_of_flat
      (correspondenceRightRemainingFiniteModelProjection f g h i z w v x) q.2⟩

/-- The original G,H generic label is retained when the first support is flat over the base.
Distinct native model labels are not identified even if this projection has collisions. -/
def correspondenceRightRemainingFinitePairGenericLabel
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x)) :
    genericPoints (correspondenceIncidence g h i w v) := by
  have : Flat (correspondenceRightExteriorProjection f g h i z w v) := by
    dsimp only [correspondenceRightExteriorProjection]
    infer_instance
  let η := correspondenceRightRemainingFiniteGenericLabel f g h i z w v x q
  exact ⟨correspondenceRightExteriorProjection f g h i z w v η.1,
    AlgebraicGeometry.mem_genericPoints_of_flat
      (correspondenceRightExteriorProjection f g h i z w v) η.2⟩

/-- The original pair label is the literal composite of the two actual projections. -/
@[simp]
theorem correspondenceRightRemainingFinitePairGenericLabel_val
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x)) :
    (correspondenceRightRemainingFinitePairGenericLabel f g h i z w v x q).1 =
      correspondenceRightExteriorProjection f g h i z w v
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q.1) := rfl

/-- Localization on both sides preserves the original finite-map residue degree. -/
theorem residueDegree_correspondenceRightRemainingFiniteModelStructure
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x) :
    (correspondenceRightRemainingFiniteModelStructure f g h i z w v x).residueDegree q =
      (correspondenceRightIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceRightRemainingFiniteModelProjection f g h i z w v x q) := by
  let ρ := correspondenceRightRemainingFiniteModelProjection f g h i z w v x
  let π := correspondenceRightRemainingFiniteModelStructure f g h i z w v x
  let j := (correspondenceRightIntermediateImageProduct f g h i z w v).fromSpecStalk
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)
  let := isIso_correspondenceRightRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  let : IsIso (ρ.residueFieldMap q) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (ρ.stalkMap q)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  let : Flat j := flat_fromSpecStalk _ _
  let := isIso_stalkMap_of_flat_isPreimmersion j (π q)
  let : IsIso (j.residueFieldMap (π q)) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (j.stalkMap (π q))).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  calc
    π.residueDegree q = (π ≫ j).residueDegree q :=
      (residueDegree_comp_of_bijective_residueFieldMap π j q
        (ConcreteCategory.bijective_of_isIso _)).symm
    _ = (ρ ≫ correspondenceRightIntermediateImageMap f g h i z w v).residueDegree q := by
      rw [show π ≫ j = ρ ≫ correspondenceRightIntermediateImageMap f g h i z w v from
        pullback.condition.symm]
    _ = _ := residueDegree_of_bijective_residueFieldMap_comp ρ
      (correspondenceRightIntermediateImageMap f g h i z w v) q
      (ConcreteCategory.bijective_of_isIso _)

end Stacks.Chow
