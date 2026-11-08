/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageGenericStalk
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.PushforwardStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalBaseIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero

/-!
# The full finite model over the actual remaining-image local ring

The original first-stage exterior is base changed to the spectrum of the actual
image-exterior stalk. Its ring of global functions is finite over that stalk,
with the native `pullbackFromSpecStalkAlgebra` action. This is the whole affine
base change, not one source stalk. Its maximal spectrum is therefore finite.

The projection to the original exterior is a flat preimmersion and is an
isomorphism on every stalk. Generic labels map to original generic labels,
and the original finite morphism's residue degrees are preserved by this
localization. None of this asserts flatness of the finite original-to-image map.

The scheme, projections, and scalar action reuse the native formal-functions
base-change objects. Their existence is distinct from realizing the first Tor
homology family over this full finite algebra, which remains a separate step.
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
abbrev correspondenceRemainingFiniteModel
    (x : correspondenceLeftImageIncidence f g h i z w v) : Scheme.{u} :=
  FormalFunctions.stalkBaseChange (correspondenceLeftIntermediateImageMap f g h i z w v)
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x)

/-- Projection to the original full first-stage exterior. -/
abbrev correspondenceRemainingFiniteModelProjection
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    correspondenceRemainingFiniteModel f g h i z w v x ⟶
      correspondenceLeftIntermediateSupportProduct f g h i z w v :=
  FormalFunctions.stalkBaseChangeι (correspondenceLeftIntermediateImageMap f g h i z w v)
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x)

/-- The finite structure morphism to the spectrum of the actual image stalk. -/
abbrev correspondenceRemainingFiniteModelStructure
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    correspondenceRemainingFiniteModel f g h i z w v x ⟶
      Spec (correspondenceRemainingImageStalk f g h i z w v x) :=
  FormalFunctions.stalkBaseChangeStructure
    (correspondenceLeftIntermediateImageMap f g h i z w v)
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x)

/-- The actual full finite ring. It is not replaced by a product of residue fields. -/
abbrev correspondenceRemainingFiniteRing
    (x : correspondenceLeftImageIncidence f g h i z w v) :=
  Γ(correspondenceRemainingFiniteModel f g h i z w v x, ⊤)

/-- The native scalar action through the actual finite structure morphism. -/
@[instance_reducible]
def correspondenceRemainingFiniteAlgebra
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    Algebra (correspondenceRemainingImageStalk f g h i z w v x)
      (correspondenceRemainingFiniteRing f g h i z w v x) :=
  FormalFunctions.pullbackFromSpecStalkAlgebra
    (correspondenceLeftIntermediateImageMap f g h i z w v)
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x)

/-- Finiteness is obtained from the actual finite map by base change. -/
theorem isFinite_correspondenceRemainingFiniteModelStructure [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    IsFinite (correspondenceRemainingFiniteModelStructure f g h i z w v x) := by
  let := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
  dsimp only [correspondenceRemainingFiniteModelStructure,
    FormalFunctions.stalkBaseChangeStructure]
  infer_instance

/-- The whole local base change is affine, even when the exterior is not affine. -/
theorem isAffine_correspondenceRemainingFiniteModel [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    IsAffine (correspondenceRemainingFiniteModel f g h i z w v x) := by
  let := isFinite_correspondenceRemainingFiniteModelStructure f g h i z w v hz hw x
  exact isAffine_of_isAffineHom (correspondenceRemainingFiniteModelStructure f g h i z w v x)

/-- The actual full ring is finite over the actual local image ring. -/
theorem moduleFinite_correspondenceRemainingFiniteRing [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    Module.Finite (correspondenceRemainingImageStalk f g h i z w v x)
      (correspondenceRemainingFiniteRing f g h i z w v x) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let := isFinite_correspondenceRemainingFiniteModelStructure f g h i z w v hz hw x
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  have he : (Scheme.ΓSpecIso (correspondenceRemainingImageStalk f g h i z w v x)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).surjective
  have hfinite := (Scheme.Hom.finite_appTop π).comp he
  have heq : algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
      (correspondenceRemainingFiniteRing f g h i z w v x) =
      π.appTop.hom.comp
        (Scheme.ΓSpecIso (correspondenceRemainingImageStalk f g h i z w v x)).inv.hom := by
    change ((Scheme.ΓSpecIso (correspondenceRemainingImageStalk f g h i z w v x)).inv ≫
      π.appLE ⊤ ⊤
        (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top π ⊤)).hom = _
    simp [Scheme.Hom.appLE]
  apply RingHom.finite_algebraMap.mp
  rw [heq]
  exact hfinite

/-- All remaining fibre labels are retained in a finite maximal spectrum. -/
theorem finite_maximalSpectrum_correspondenceRemainingFiniteRing [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    Finite (MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x
  exact Stacks.Length.finite_maximalSpectrum
    (A := correspondenceRemainingImageStalk f g h i z w v x)

/-- Flatness belongs to the localization projection, not to the finite map. -/
theorem flat_correspondenceRemainingFiniteModelProjection
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    Flat (correspondenceRemainingFiniteModelProjection f g h i z w v x) := by
  let := flat_fromSpecStalk (correspondenceLeftIntermediateImageProduct f g h i z w v)
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x)
  dsimp only [correspondenceRemainingFiniteModelProjection, FormalFunctions.stalkBaseChangeι]
  infer_instance

/-- The localization projection identifies every actual source local ring. -/
theorem isIso_correspondenceRemainingFiniteModelProjection_stalkMap
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    IsIso ((correspondenceRemainingFiniteModelProjection f g h i z w v x).stalkMap q) := by
  let := flat_correspondenceRemainingFiniteModelProjection f g h i z w v x
  exact isIso_stalkMap_of_flat_isPreimmersion
    (correspondenceRemainingFiniteModelProjection f g h i z w v x) q

/-- Every generic local label keeps its actual original exterior generic label. -/
def correspondenceRemainingFiniteGenericLabel
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x)) :
    genericPoints (correspondenceLeftIntermediateSupportProduct f g h i z w v) := by
  let := flat_correspondenceRemainingFiniteModelProjection f g h i z w v x
  exact ⟨correspondenceRemainingFiniteModelProjection f g h i z w v x q.1,
    AlgebraicGeometry.mem_genericPoints_of_flat
      (correspondenceRemainingFiniteModelProjection f g h i z w v x) q.2⟩

/-- Localization on both sides preserves the original finite-map residue degree. -/
theorem residueDegree_correspondenceRemainingFiniteModelStructure
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    (correspondenceRemainingFiniteModelStructure f g h i z w v x).residueDegree q =
      (correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q) := by
  let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  let j := (correspondenceLeftIntermediateImageProduct f g h i z w v).fromSpecStalk
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x)
  let := isIso_correspondenceRemainingFiniteModelProjection_stalkMap f g h i z w v x q
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
    _ = (ρ ≫ correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree q := by
      rw [show π ≫ j = ρ ≫ correspondenceLeftIntermediateImageMap f g h i z w v from
        pullback.condition.symm]
    _ = _ := residueDegree_of_bijective_residueFieldMap_comp ρ
      (correspondenceLeftIntermediateImageMap f g h i z w v) q
      (ConcreteCategory.bijective_of_isIso _)

end Stacks.Chow
