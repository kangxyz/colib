/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleAmbient
public import Colib.RingTheory.Koszul.CoefficientFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.LocalRingPushout
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange

/-!
# Actual first-stage exterior base change on support stalks

The square formed by the original pair incidence, the original pair support product, and
both full exterior products with the third support is Cartesian. Native closed-immersion
stalk base change gives its actual local-ring pushout. The support projection is flat when
the third support is flat over the base, in particular over every field.

For an ordered list in the original Y self-product stalk, native flat Koszul base change
identifies the full-exterior support homology with the scalar extension of the original pair
support homology. All maps are actual scheme stalk maps, including the necessary point
transport. The coefficient is the full support ring, without a reduction or a flatness
assumption on its embedding in the sixfold ambient.

The module comparison still has to be joined to the original ambient pair Tor comparison
and to the quotient-induced first-incidence scalar action. The local-ring pushout here is
the native input to that scalar descent; it is not a postulated comparison or a replacement
of the full exterior fibre length by one.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The projection of the full three-support product to the original two-support product. -/
abbrev correspondenceTripleSupportProjection :
    correspondenceTripleSupportProduct f g h i z w v ⟶ correspondenceSupportProduct f g h z w :=
  pullback.fst _ _

/-- Full exterior support projection is flat by base change of the third support. -/
instance flat_correspondenceTripleSupportProjection
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)] :
    Flat (correspondenceTripleSupportProjection f g h i z w v) := by
  dsimp only [correspondenceTripleSupportProjection]
  infer_instance

/-- The first-stage support square is the actual product base change of the original incidence. -/
theorem correspondenceLeftIntermediate_support_isPullback :
    IsPullback (correspondenceLeftIntermediateToTripleSupport f g h i z w v)
      (pullback.fst _ _ : correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶
        correspondenceIncidence f g h z w)
      (correspondenceTripleSupportProjection f g h i z w v)
      (correspondenceIncidenceToSupportProduct f g h z w) := by
  have hp : IsPullback
      (pullback.fst _ _ : correspondenceLeftIntermediateSupportProduct f g h i z w v ⟶
        correspondenceIncidence f g h z w)
      (correspondenceLeftIntermediateToTripleSupport f g h i z w v ≫ pullback.snd _ _)
      (correspondenceIncidenceToSupportProduct f g h z w ≫
        (correspondenceSupportProductTarget f g h z w ≫ h))
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) := by
    simpa only [correspondenceLeftIntermediateToTripleSupport_snd,
      correspondenceSupportProductTarget, Category.assoc,
      correspondenceIncidenceToSupportProduct_snd_assoc, correspondenceIncidenceRight] using
      (IsPullback.of_hasPullback (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))
  exact (hp.of_bot
    (correspondenceLeftIntermediateToTripleSupport_fst f g h i z w v).symm
    (IsPullback.of_hasPullback (correspondenceSupportProductTarget f g h z w ≫ h)
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))).flip

/-- The first-stage inclusion in the full exterior support retains its full closed subscheme. -/
instance isClosedImmersion_correspondenceLeftIntermediateToTripleSupport [IsSeparated g] :
    IsClosedImmersion (correspondenceLeftIntermediateToTripleSupport f g h i z w v) :=
  MorphismProperty.of_isPullback
    (correspondenceLeftIntermediate_support_isPullback f g h i z w v).flip inferInstance

/-- The two presentations of the original pair-support point agree by the actual square. -/
theorem correspondenceLeftIntermediate_support_point_eq
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    correspondenceIncidenceToSupportProduct f g h z w (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x) =
      correspondenceTripleSupportProjection f g h i z w v
        (correspondenceLeftIntermediateToTripleSupport f g h i z w v x) := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun m => m x)
      (correspondenceLeftIntermediate_support_isPullback f g h i z w v).w.symm

/-- The actual support-stalk scalar map, transported from the original pair-incidence label. -/
def correspondenceLeftExteriorSupportStalkMap
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    (correspondenceSupportProduct f g h z w).presheaf.stalk
      (correspondenceIncidenceToSupportProduct f g h z w (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x)) →+*
    (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceLeftIntermediateToTripleSupport f g h i z w v x) :=
  (((correspondenceSupportProduct f g h z w).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceLeftIntermediate_support_point_eq f g h i z w v x))).hom ≫
      (correspondenceTripleSupportProjection f g h i z w v).stalkMap
        (correspondenceLeftIntermediateToTripleSupport f g h i z w v x)).hom

/-- Flatness includes the actual point transport, rather than identifying stalk points silently. -/
theorem flat_correspondenceLeftExteriorSupportStalkMap
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    (correspondenceLeftExteriorSupportStalkMap f g h i z w v x).Flat := by
  apply RingHom.Flat.comp
  · exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  · exact Flat.stalkMap (correspondenceTripleSupportProjection f g h i z w v) _

/-- The actual first-incidence support kernel is the extension of the original pair kernel. -/
theorem correspondenceLeftIntermediate_support_stalkMap_ker [IsSeparated g]
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    RingHom.ker ((correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap x).hom =
      (RingHom.ker ((correspondenceIncidenceToSupportProduct f g h z w).stalkMap
        (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x)).hom).map
          (correspondenceLeftExteriorSupportStalkMap f g h i z w v x) :=
  Stacks.Flatness.ker_stalkMap_of_isPullback
    (correspondenceLeftIntermediate_support_isPullback f g h i z w v) x
    (correspondenceLeftIntermediate_support_point_eq f g h i z w v x)

/-- The four original local rings form a genuine algebra pushout with their actual stalk maps. -/
theorem correspondenceLeftIntermediate_support_stalk_isPushout [IsSeparated g]
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    let D₀ := (correspondenceSupportProduct f g h z w).presheaf.stalk
      (correspondenceIncidenceToSupportProduct f g h z w (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x))
    let P₀ := (correspondenceIncidence f g h z w).presheaf.stalk (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x)
    let D := (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceLeftIntermediateToTripleSupport f g h i z w v x)
    let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk x
    let η₀ := ((correspondenceIncidenceToSupportProduct f g h z w).stalkMap
      (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x)).hom
    let η := ((correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap x).hom
    let φ := correspondenceLeftExteriorSupportStalkMap f g h i z w v x
    letI : Algebra D₀ P₀ := η₀.toAlgebra
    letI : Algebra D₀ D := φ.toAlgebra
    letI : Algebra D₀ P := (η.comp φ).toAlgebra
    letI : Algebra P₀ P := ((pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
      (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)).stalkMap x).hom.toAlgebra
    letI : Algebra D P := η.toAlgebra
    haveI : IsScalarTower D₀ D P := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower D₀ P₀ P := IsScalarTower.of_algebraMap_eq' (by
      exact congrArg (fun a => a.hom)
        (Stacks.Cohomology.StalkPushout.stalkMap_comm_of_isPullback
          (correspondenceLeftIntermediate_support_isPullback f g h i z w v) x
          (correspondenceLeftIntermediate_support_point_eq f g h i z w v x)).symm)
    Algebra.IsPushout D₀ P₀ D P :=
  Stacks.Cohomology.StalkPushout.isPushout_stalkMap_toAlgebra_of_isPullback
    (correspondenceLeftIntermediate_support_isPullback f g h i z w v) x
    (correspondenceLeftIntermediate_support_point_eq f g h i z w v x)

/-- Native flat base change for a list from the original middle self-product stalk,
with the full exterior support ring as coefficient. -/
theorem correspondenceLeftExterior_originalMiddle_koszul_baseChange
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : correspondenceLeftIntermediateSupportProduct f g h i z w v) :
    let e₀ := correspondenceIncidenceToSupportProduct f g h z w (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x)
    let D₀ := (correspondenceSupportProduct f g h z w).presheaf.stalk e₀
    let D := (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceLeftIntermediateToTripleSupport f g h i z w v x)
    let m := correspondenceSupportProductInclusion f g h z w ≫ correspondenceMiddlePair f g h
    let θ := (m.stalkMap e₀).hom
    let φ := correspondenceLeftExteriorSupportStalkMap f g h i z w v x
    letI : Algebra D₀ D := φ.toAlgebra
    ∀ {r : ℕ} (t : Fin r → (pullback g g).presheaf.stalk (m e₀)) (n : ℕ),
      Nonempty (((Koszul.seqComplexTensor (fun a => φ (θ (t a))) D).homology n) ≃ₗ[D]
        (D ⊗[D₀] ((Koszul.seqComplexTensor (fun a => θ (t a)) D₀).homology n))) := by
  dsimp only
  intro r t n
  let D₀ := (correspondenceSupportProduct f g h z w).presheaf.stalk
    (correspondenceIncidenceToSupportProduct f g h z w (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x))
  let D := (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceLeftIntermediateToTripleSupport f g h i z w v x)
  let φ := correspondenceLeftExteriorSupportStalkMap f g h i z w v x
  let : Algebra D₀ D := φ.toAlgebra
  have : Module.Flat D₀ D := flat_correspondenceLeftExteriorSupportStalkMap f g h i z w v x
  let a := fun j => ((correspondenceSupportProductInclusion f g h z w ≫
    correspondenceMiddlePair f g h).stalkMap
      (correspondenceIncidenceToSupportProduct f g h z w (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) x))).hom (t j)
  let b := fun j => φ (a j)
  let e := (Koszul.seqComplexTensorFunctor b).mapIso
    (TensorProduct.AlgebraTensorModule.rid D₀ D D).symm.toModuleIso
  obtain ⟨e'⟩ := KoszulC.homology_baseChange_linearEquiv (S := D) a D₀ n
  exact ⟨((HomologicalComplex.homologyFunctor _ _ n).mapIso e).toLinearEquiv.trans e'⟩

end Stacks.Chow
