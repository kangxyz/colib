/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageGeometry
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor
public import Colib.RingTheory.Koszul.CoefficientFunctor
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.LocalRingPushout
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange

/-!
# Actual right support base change for the original last-pair Tor

Native pullback associativity gives the Cartesian square between the actual
right exterior, the original last-pair incidence, and their full support schemes.
The native local-ring pushout and flat Koszul base-change theorems then identify
support coefficient homology with the actual last-pair Tor tensor, retaining
its original incidence action. Flatness is only over the original base S.

The common sixfold coefficient module has a separately proved stalk transport
to this actual support stalk. This file supplies the support-side comparison,
not a remaining Euler or weighted bracket equality.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The native right support projection is flat when the first support is flat over S. -/
instance flat_correspondenceTripleSupportRightProjection
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)] :
    Flat (correspondenceTripleSupportRightProjection f g h i z w v) :=
  MorphismProperty.of_isPullback
    (correspondenceTripleSupport_right_isPullback f g h i z w v) inferInstance

/-- The actual right first stage is the full exterior base change of the last-pair incidence. -/
theorem correspondenceRightIntermediate_support_isPullback :
    IsPullback (correspondenceRightIntermediateToTripleSupport f g h i z w v)
      (correspondenceRightExteriorProjection f g h i z w v)
      (correspondenceTripleSupportRightProjection f g h i z w v)
      (correspondenceIncidenceToSupportProduct g h i w v) := by
  have hp : IsPullback
      (correspondenceRightExteriorProjection f g h i z w v)
      (correspondenceRightIntermediateToTripleSupport f g h i z w v ≫
        correspondenceTripleSupportFirstProjection f g h i z w v)
      (correspondenceIncidenceToSupportProduct g h i w v ≫
        (correspondenceSupportProductSource g h i w v ≫ g))
      (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g) := by
    simpa only [correspondenceRightIntermediateToTripleSupport_firstFactor,
      correspondenceRightExteriorProjection, correspondenceSupportProductSource,
      Category.assoc, correspondenceIncidenceToSupportProduct_fst_assoc,
      correspondenceIncidenceLeft] using
      (IsPullback.of_hasPullback
        (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
        (correspondenceIncidenceLeft g h i w v ≫ g)).flip
  exact (hp.of_bot
    (correspondenceRightIntermediateToTripleSupport_rightPair f g h i z w v).symm
    (correspondenceTripleSupport_right_isPullback f g h i z w v).flip).flip

/-- This is the full closed support immersion, not a reduction of its image. -/
instance isClosedImmersion_correspondenceRightIntermediateToTripleSupport [IsSeparated h] :
    IsClosedImmersion (correspondenceRightIntermediateToTripleSupport f g h i z w v) :=
  MorphismProperty.of_isPullback
    (correspondenceRightIntermediate_support_isPullback f g h i z w v).flip inferInstance

/-- The original last-pair support point is the actual common-support projection. -/
theorem correspondenceRightIntermediate_support_point_eq
    (x : correspondenceRightIntermediateSupportProduct f g h i z w v) :
    correspondenceIncidenceToSupportProduct g h i w v
        (correspondenceRightExteriorProjection f g h i z w v x) =
      correspondenceTripleSupportRightProjection f g h i z w v
        (correspondenceRightIntermediateToTripleSupport f g h i z w v x) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m x)
    (correspondenceRightIntermediate_support_isPullback f g h i z w v).w.symm

/-- The original last-pair support scalar map includes its actual equality of points. -/
def correspondenceRightExteriorSupportStalkMap
    (x : correspondenceRightIntermediateSupportProduct f g h i z w v) :
    (correspondenceSupportProduct g h i w v).presheaf.stalk
      (correspondenceIncidenceToSupportProduct g h i w v
        (correspondenceRightExteriorProjection f g h i z w v x)) →+*
    (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceRightIntermediateToTripleSupport f g h i z w v x) :=
  (((correspondenceSupportProduct g h i w v).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceRightIntermediate_support_point_eq f g h i z w v x))).hom ≫
      (correspondenceTripleSupportRightProjection f g h i z w v).stalkMap
        (correspondenceRightIntermediateToTripleSupport f g h i z w v x)).hom

/-- Flatness survives the actual stalk transport. -/
theorem flat_correspondenceRightExteriorSupportStalkMap
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (x : correspondenceRightIntermediateSupportProduct f g h i z w v) :
    (correspondenceRightExteriorSupportStalkMap f g h i z w v x).Flat := by
  apply RingHom.Flat.comp
  · exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  · exact Flat.stalkMap (correspondenceTripleSupportRightProjection f g h i z w v) _

variable (x : correspondenceRightIntermediateSupportProduct f g h i z w v)

local notation3 (prettyPrint := false) "π" =>
  correspondenceRightExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "D₀" =>
  (correspondenceSupportProduct g h i w v).presheaf.stalk
    (correspondenceIncidenceToSupportProduct g h i w v (π x))
local notation3 (prettyPrint := false) "P₀" =>
  (correspondenceIncidence g h i w v).presheaf.stalk (π x)
local notation3 (prettyPrint := false) "D" =>
  (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceRightIntermediateToTripleSupport f g h i z w v x)
local notation3 (prettyPrint := false) "P" =>
  (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk x
local notation3 (prettyPrint := false) "φ" =>
  correspondenceRightExteriorSupportStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "η₀" =>
  ((correspondenceIncidenceToSupportProduct g h i w v).stalkMap (π x)).hom
local notation3 (prettyPrint := false) "η" =>
  ((correspondenceRightIntermediateToTripleSupport f g h i z w v).stalkMap x).hom
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion g h i w v (π x)
local notation3 (prettyPrint := false) "R₀" =>
  (pullback h h).presheaf.stalk (correspondenceMiddlePair g h i p₀)
local notation3 (prettyPrint := false) "β" => ((correspondenceMiddlePair g h i).stalkMap p₀).hom
local notation3 (prettyPrint := false) "ρ" => correspondenceIncidenceSupportStalkMap g h i w v (π x)

/-- The four actual right support stalks form the native local-ring pushout. -/
theorem correspondenceRightIntermediate_support_stalk_isPushout [IsSeparated h] :
    letI : Algebra D₀ P₀ := η₀.toAlgebra
    letI : Algebra D₀ D := φ.toAlgebra
    letI : Algebra D₀ P := (η.comp φ).toAlgebra
    letI : Algebra P₀ P := (π.stalkMap x).hom.toAlgebra
    letI : Algebra D P := η.toAlgebra
    haveI : IsScalarTower D₀ D P := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower D₀ P₀ P := IsScalarTower.of_algebraMap_eq' (by
      exact congrArg (fun a => a.hom)
        (Stacks.Cohomology.StalkPushout.stalkMap_comm_of_isPullback
          (correspondenceRightIntermediate_support_isPullback f g h i z w v) x
          (correspondenceRightIntermediate_support_point_eq f g h i z w v x)).symm)
    Algebra.IsPushout D₀ P₀ D P :=
  Stacks.Cohomology.StalkPushout.isPushout_stalkMap_toAlgebra_of_isPullback
    (correspondenceRightIntermediate_support_isPullback f g h i z w v) x
    (correspondenceRightIntermediate_support_point_eq f g h i z w v x)

/-- Actual right support homology is the scalar extension of the actual last-pair Tor.
The original incidence action on that Tor module is retained. -/
theorem correspondenceRightExterior_originalPairTor_baseChange
    [Flat g] [Flat i] [IsSeparated h]
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    {r : ℕ} (s : Fin r → R₀) (hs : IsRegular R₀ (List.ofFn s))
    (hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s)) (n : ℕ) :
    letI := correspondenceIncidenceTorModule g h i w v (π x) n
    letI : Algebra P₀ P := (π.stalkMap x).hom.toAlgebra
    letI : Algebra D P := η.toAlgebra
    Nonempty (((Koszul.seqComplexTensor (fun j => φ (ρ (β (s j)))) D).homology n) ≃ₗ[D]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π x) n)) := by
  let : Algebra D₀ D := φ.toAlgebra
  let : Algebra D₀ P₀ := η₀.toAlgebra
  let : Algebra D₀ P := (η.comp φ).toAlgebra
  let : Algebra P₀ P := (π.stalkMap x).hom.toAlgebra
  let : Algebra D P := η.toAlgebra
  have : IsScalarTower D₀ D P := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower D₀ P₀ P := IsScalarTower.of_algebraMap_eq' (by
    exact congrArg (fun a => a.hom)
      (Stacks.Cohomology.StalkPushout.stalkMap_comm_of_isPullback
        (correspondenceRightIntermediate_support_isPullback f g h i z w v) x
        (correspondenceRightIntermediate_support_point_eq f g h i z w v x)).symm)
  have : Algebra.IsPushout D₀ P₀ D P :=
    correspondenceRightIntermediate_support_stalk_isPushout f g h i z w v x
  have : Algebra.IsPushout D₀ D P₀ P := Algebra.IsPushout.symm inferInstance
  have : Module.Flat D₀ D := flat_correspondenceRightExteriorSupportStalkMap f g h i z w v x
  let T := correspondenceIncidenceAmbientTor g h i w v (π x) n
  let := correspondenceIncidenceTorModule g h i w v (π x) n
  let := correspondenceIncidenceTorSupportModule g h i w v (π x) n
  have : IsScalarTower D₀ P₀ T := IsScalarTower.of_compHom D₀ P₀ T
  let a : Fin r → D₀ := fun j => ρ (β (s j))
  let eunit := (Koszul.seqComplexTensorFunctor (fun j => φ (a j))).mapIso
    (TensorProduct.AlgebraTensorModule.rid D₀ D D).symm.toModuleIso
  obtain ⟨eflat⟩ := KoszulC.homology_baseChange_linearEquiv (S := D) a D₀ n
  let eoriginal := correspondenceIncidenceTorOriginalSupportLinearEquiv
    g h i w v (π x) s hs hks n
  exact ⟨((HomologicalComplex.homologyFunctor _ _ n).mapIso eunit).toLinearEquiv.trans
    (eflat.trans ((TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl D D) eoriginal.symm).trans
        (Algebra.IsPushout.cancelBaseChange D₀ D P₀ P T).symm))⟩

end Stacks.Chow
