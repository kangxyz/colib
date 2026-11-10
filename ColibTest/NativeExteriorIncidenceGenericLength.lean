/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceGenericLength

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct
open AlgebraicGeometry.Scheme Stacks.Chow

noncomputable section
universe u v

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w))

example : (nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η).Flat :=
  nativeExteriorIncidenceGenericStalkMap_flat X Y Z T z w hz hw η

example : Ideal.map (nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η)
    (IsLocalRing.maximalIdeal
      ((correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val)) =
    IsLocalRing.maximalIdeal
      ((nativeExteriorIncidence X Y Z T z w hz hw).presheaf.stalk
        (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val) :=
  map_maximalIdeal_nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η

example : Module.length
    ((nativeExteriorIncidence X Y Z T z w hz hw).presheaf.stalk
      (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val)
    (((nativeExteriorIncidence X Y Z T z w hz hw).presheaf.stalk
      (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val) ⧸
      Ideal.map (nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η)
        (IsLocalRing.maximalIdeal
          ((correspondenceIncidence X.hom Y.hom Z.hom z w).presheaf.stalk η.val))) = 1 :=
  length_quotient_nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η

example (M : Type v) [AddCommGroup M]
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
  length_baseChange_nativeExteriorIncidenceGenericStalkMap X Y Z T z w hz hw η M
