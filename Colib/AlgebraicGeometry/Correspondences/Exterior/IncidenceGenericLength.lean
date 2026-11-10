/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceGenerics
public import Colib.AlgebraicGeometry.Scheme.GenericFiberLength

/-!
# Actual generic local lengths for the full exterior incidence

The local algebra map is the parameter-forgetting stalk map, preceded by the
specified point-transport isomorphism. Smoothness gives flatness and geometric
integrality gives reduced fibers. The general full-scheme theorem then proves
the maximal-ideal equality and closed-fiber length one for this actual map.

All lengths are Mathlib's extended-natural module lengths. The statements apply
to arbitrary modules over the original incidence stalk, not only finite ones.
They do not identify ambient Tor modules or assert any finite residue degree is
one; those are separate obligations for exterior-composition compatibility.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct
open AlgebraicGeometry.Scheme

universe u v
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)

/-- The literal-product local map keeps the named original generic stalk. -/
def exteriorIncidenceProductGenericStalkMap
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    (correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val →+*
      (exteriorIncidenceProduct X Y Z T z w).presheaf.stalk
        (exteriorIncidenceProductGenericsEquiv X Y Z T z w η).val :=
  (exteriorIncidenceProductProjection X Y Z T z w).stalkMapOverPoint
    (exteriorIncidenceProductGenericsEquiv X Y Z T z w η).val η.val
    (exteriorIncidenceProductGenericsEquiv_projection X Y Z T z w η)

/-- On the literal full product, arbitrary module lengths are preserved by the actual
point-transported projection map. -/
theorem length_baseChange_exteriorIncidenceProductGenericStalkMap
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w))
    (M : Type v) [AddCommGroup M]
    [Module ((correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val) M] :
    letI := (exteriorIncidenceProductGenericStalkMap X Y Z T z w η).toAlgebra
    Module.length
      ((exteriorIncidenceProduct X Y Z T z w).presheaf.stalk
        (exteriorIncidenceProductGenericsEquiv X Y Z T z w η).val)
      (((exteriorIncidenceProduct X Y Z T z w).presheaf.stalk
        (exteriorIncidenceProductGenericsEquiv X Y Z T z w η).val) ⊗[
          (correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val] M) =
      Module.length
        ((correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val) M :=
  (exteriorIncidenceProductProjection X Y Z T z w).length_baseChange_stalkMapOverPoint
    _ _ (exteriorIncidenceProductGenericsEquiv_projection X Y Z T z w η)
    (exteriorIncidenceProductGenericsEquiv X Y Z T z w η).property M

variable (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

/-- The actual native incidence local map, with the original generic point named explicitly. -/
def nativeExteriorIncidenceGenericStalkMap
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    (correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val →+*
      (nativeExteriorIncidence X Y Z T z w hz hw).presheaf.stalk
        (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val :=
  (nativeExteriorIncidenceOriginal X Y Z T z w hz hw).stalkMapOverPoint
    (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val η.val
    (nativeExteriorIncidenceGenericsEquiv_original X Y Z T z w hz hw η)

instance nativeExteriorIncidenceGenericStalkMap_isLocalHom
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    IsLocalHom (nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η) := by
  dsimp only [nativeExteriorIncidenceGenericStalkMap]
  infer_instance

/-- Flatness is proved for the entire transported map, including the named base stalk. -/
theorem nativeExteriorIncidenceGenericStalkMap_flat
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    (nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η).Flat :=
  (nativeExteriorIncidenceOriginal X Y Z T z w hz hw).stalkMapOverPoint_flat _ _ _

/-- The maximal-ideal equality follows from the actual reduced fiber and its canonical
quotient-stalk identification. It is not a coefficient-provider assumption. -/
theorem map_maximalIdeal_nativeExteriorIncidenceGenericStalkMap
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    Ideal.map (nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η)
      (IsLocalRing.maximalIdeal
        ((correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val)) =
      IsLocalRing.maximalIdeal
        ((nativeExteriorIncidence X Y Z T z w hz hw).presheaf.stalk
          (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val) :=
  (nativeExteriorIncidenceOriginal X Y Z T z w hz hw).map_maximalIdeal_stalkMapOverPoint
    _ _ (nativeExteriorIncidenceGenericsEquiv_original X Y Z T z w hz hw η)
    (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).property

/-- The closed-fiber factor in the actual generic local length formula equals one. -/
theorem length_quotient_nativeExteriorIncidenceGenericStalkMap
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    Module.length
      ((nativeExteriorIncidence X Y Z T z w hz hw).presheaf.stalk
        (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val)
      (((nativeExteriorIncidence X Y Z T z w hz hw).presheaf.stalk
        (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val) ⧸
        Ideal.map (nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η)
          (IsLocalRing.maximalIdeal
            ((correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val))) = 1 :=
  (nativeExteriorIncidenceOriginal
    X Y Z T z w hz hw).length_quotient_map_maximalIdeal_stalkMapOverPoint _ _
      (nativeExteriorIncidenceGenericsEquiv_original X Y Z T z w hz hw η)
      (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).property

/-- The native exterior-incidence local map preserves the length of every scalar-extended
original incidence-stalk module, including infinite length. -/
theorem length_baseChange_nativeExteriorIncidenceGenericStalkMap
    (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w))
    (M : Type v) [AddCommGroup M]
    [Module ((correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val) M] :
    letI := (nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η).toAlgebra
    Module.length
      ((nativeExteriorIncidence X Y Z T z w hz hw).presheaf.stalk
        (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val)
      (((nativeExteriorIncidence X Y Z T z w hz hw).presheaf.stalk
        (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val) ⊗[
          (correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val] M) =
      Module.length
        ((correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val) M :=
  (nativeExteriorIncidenceOriginal X Y Z T z w hz hw).length_baseChange_stalkMapOverPoint
    _ _ (nativeExteriorIncidenceGenericsEquiv_original X Y Z T z w hz hw η)
    (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).property M

end Stacks.Chow
