/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.GenericPointsOfGeometricallyIrreducible
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceIso
public import StacksFrontier.Topology.Sober.Generization

/-!
# Generic points of the full exterior incidence

The original incidence is an arbitrary scheme here, not a smooth-site object.
The literal product projection and the actual native parameter-forgetting map
both induce the native component/generic-point correspondence. Their Cartesian
squares retain every component and every nilpotent of the original incidence.
Empty and disconnected incidences are allowed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)

/-- The parameter-forgetting map on the literal full incidence product. -/
abbrev exteriorIncidenceProductProjection : exteriorIncidenceProduct X Y Z T z w ⟶
    correspondenceIncidence X.hom Y.hom Z.hom z w :=
  pullback.fst (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) T.hom

/-- Generic-point correspondence on the literal product, with no smoothness assumption on
`correspondenceIncidence`. -/
def exteriorIncidenceProductGenericsEquiv :
    genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w) ≃
      genericPoints (exteriorIncidenceProduct X Y Z T z w) :=
  (exteriorIncidenceProductProjection X Y Z T z w).genericPointsEquivOfGeometricallyIrreducible
      (exteriorIncidenceProductProjection X Y Z T z w).isOpenMap

@[simp]
theorem exteriorIncidenceProductGenericsEquiv_projection
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    exteriorIncidenceProductProjection X Y Z T z w
      (exteriorIncidenceProductGenericsEquiv X Y Z T z w η).val = η.val :=
  (exteriorIncidenceProductProjection
    X Y Z T z w).genericPointsEquivOfGeometricallyIrreducible_apply _ η

/-- The complete component is the literal preimage, rather than a reduced chosen support. -/
theorem exteriorIncidenceProductGenericsEquiv_closure
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    closure ({(exteriorIncidenceProductGenericsEquiv X Y Z T z w η).val} :
      Set (exteriorIncidenceProduct X Y Z T z w)) =
      (exteriorIncidenceProductProjection X Y Z T z w) ⁻¹'
        closure ({η.val} : Set (correspondenceIncidence X.hom Y.hom Z.hom z w)) :=
  (exteriorIncidenceProductProjection
    X Y Z T z w).genericPointsEquivOfGeometricallyIrreducible_closure _ η

variable (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

/-- Geometric integrality belongs to the actual projection, not to its possibly nonreduced
source or target. -/
instance nativeExteriorIncidenceOriginal_geometricallyIntegral :
    GeometricallyIntegral (nativeExteriorIncidenceOriginal X Y Z T z w hz hw) :=
  MorphismProperty.of_isPullback
    (nativeExteriorIncidenceOriginal_isPullback X Y Z T z w hz hw).flip inferInstance

/-- Native generic-point correspondence for the actual full exterior incidence. -/
def nativeExteriorIncidenceGenericsEquiv :
    genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w) ≃
      genericPoints (nativeExteriorIncidence X Y Z T z w hz hw) :=
  (nativeExteriorIncidenceOriginal X Y Z T z w hz hw).genericPointsEquivOfGeometricallyIrreducible
      (nativeExteriorIncidenceOriginal X Y Z T z w hz hw).isOpenMap

@[simp]
theorem nativeExteriorIncidenceGenericsEquiv_original
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    nativeExteriorIncidenceOriginal X Y Z T z w hz hw
      (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val = η.val :=
  (nativeExteriorIncidenceOriginal
    X Y Z T z w hz hw).genericPointsEquivOfGeometricallyIrreducible_apply _ η

/-- The actual native exterior component is the full parameter-forgetting preimage. -/
theorem nativeExteriorIncidenceGenericsEquiv_closure
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    closure ({(nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val} :
      Set (nativeExteriorIncidence X Y Z T z w hz hw)) =
      (nativeExteriorIncidenceOriginal X Y Z T z w hz hw) ⁻¹'
        closure ({η.val} : Set (correspondenceIncidence X.hom Y.hom Z.hom z w)) :=
  (nativeExteriorIncidenceOriginal
    X Y Z T z w hz hw).genericPointsEquivOfGeometricallyIrreducible_closure _ η

/-- The native and literal-product generic correspondences are carried into one another by
the actual full-incidence isomorphism, not by an arbitrary set bijection. -/
theorem nativeExteriorIncidenceIso_inv_generics
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    (nativeExteriorIncidenceIso X Y Z T z w hz hw).inv
      (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val =
      (exteriorIncidenceProductGenericsEquiv X Y Z T z w η).val := by
  let e := nativeExteriorIncidenceIso X Y Z T z w hz hw
  let ξ := nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η
  have hξ : e.inv ξ.val ∈ genericPoints (exteriorIncidenceProduct X Y Z T z w) := by
    apply mem_genericPoints_of_forall_specializes_eq
    intro a ha
    apply e.hom.isEmbedding.injective
    have h := forall_specializes_eq_of_mem_genericPoints ξ.property (e.hom a)
      (by simpa using ha.map e.hom.continuous)
    simpa using h
  have hpoint : exteriorIncidenceProductProjection X Y Z T z w (e.inv ξ.val) = η.val := by
    change (nativeExteriorIncidenceToProduct X Y Z T z w hz hw ≫ pullback.fst _ _) ξ.val = _
    rw [nativeExteriorIncidenceToProduct_fst]
    exact nativeExteriorIncidenceGenericsEquiv_original X Y Z T z w hz hw η
  have heq : (⟨e.inv ξ.val, hξ⟩ : genericPoints (exteriorIncidenceProduct X Y Z T z w)) =
      exteriorIncidenceProductGenericsEquiv X Y Z T z w η := by
    apply (exteriorIncidenceProductProjection
      X Y Z T z w).genericPoints_injective_of_geometricallyIrreducible
        (exteriorIncidenceProductProjection X Y Z T z w).isOpenMap
    exact hpoint.trans (exteriorIncidenceProductGenericsEquiv_projection X Y Z T z w η).symm
  exact congrArg Subtype.val heq

end Stacks.Chow
