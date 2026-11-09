/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenSupport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenComparison
public import Colib.KTheory.Waldhausen.ExactEquivalence
public import Colib.KTheory.Waldhausen.Fibration.LongExactSequence

/-!
# The actual supported bounded-flat relative fiber and boundary

The original inclusion and canonical K-maps are retained through the exact equivalence
with union support. Actual restriction proves the coarse extension axiom, and the original
identity-cone second endpoint discharges the full canonical fiber theorem. No compactness
assumption is imposed on the scheme or either open.

Adapted from Quillen `BoundedFlat/SupportedOpenFibration.lean:197-293` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration Topology

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The literal inclusion forgets only acyclicity on the localization open. -/
def boundedAboveFlatPerfectSupportedUnionInclusion :
    (boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory ⥤
      (boundedAboveFlatPerfectSupported T.ι).FullSubcategory :=
  ObjectProperty.ιOfLE (show boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι ≤
    boundedAboveFlatPerfectSupported T.ι from fun K h =>
      ((boundedAboveFlatPerfectSupported_sup_opensRange_iff j T K).1 h).1)

/-- The actual supported inclusion preserves the original fine exact structures. -/
theorem boundedAboveFlatPerfectSupportedUnionInclusion_isExact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).weq
      (boundedAboveFlatPerfectSupportedWaldhausen T.ι).cof
      (boundedAboveFlatPerfectSupportedWaldhausen T.ι).weq
      (boundedAboveFlatPerfectSupportedUnionInclusion j T) :=
  (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T).comp
    (acyclicInclusion_exact (boundedAboveFlatPerfectSupportedOpenNested j T))

/-- The original supported inclusion K-map. -/
def boundedAboveFlatPerfectSupportedUnionKMap (n : ℕ) :
    BoundedAboveFlatPerfectSupportedK (T ⊔ j.opensRange).ι n →*
      BoundedAboveFlatPerfectSupportedK T.ι n :=
  KMap (boundedAboveFlatPerfectSupportedUnionInclusion_isExact j T) n

/-- Exact flattening gives the original all-degree supported K-equivalence. -/
@[colib_tag "COL-0384",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenFibration.lean:213-218"
    "adaptation" "Exact acyclic-to-union K-equivalence without compactness assumptions"]
def boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv (n : ℕ) :
    (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T)).K n ≃*
      BoundedAboveFlatPerfectSupportedK (T ⊔ j.opensRange).ι n :=
  KEquivOfExactEquivalence
    (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedEquivalence j T)
    (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_exact j T)
    (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T) n

/-- Its forward homomorphism is the original exact flattening K-map. -/
theorem boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_forward (n : ℕ) :
    (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      KMap (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_exact j T) n := rfl

/-- Its inverse is the original exact inverse K-map, with independent chosen zeros. -/
theorem boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_inverse (n : ℕ) :
    (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.toMonoidHom =
      KMap (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T) n := rfl

/-- The actual inclusion K-map is retained after exact flattening. -/
theorem boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_inclusion (n : ℕ) :
    (boundedAboveFlatPerfectSupportedUnionKMap j T n).comp
        (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      KMap (acyclicInclusion_exact (boundedAboveFlatPerfectSupportedOpenNested j T)) n :=
  KMap_comp_KMap (boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_exact j T)
    (boundedAboveFlatPerfectSupportedUnionInclusion_isExact j T) n

/-- The inverse transport also retains the original supported inclusion K-map. -/
theorem boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_symm_inclusion (n : ℕ) :
    (KMap (acyclicInclusion_exact (boundedAboveFlatPerfectSupportedOpenNested j T)) n).comp
        (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.toMonoidHom =
      boundedAboveFlatPerfectSupportedUnionKMap j T n :=
  KMap_comp_KMap (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T)
    (acyclicInclusion_exact (boundedAboveFlatPerfectSupportedOpenNested j T)) n

/-- Actual restriction discharges the source coarse extension axiom. -/
theorem boundedAboveFlatPerfectSupportedOpenWaldhausen_extensionAxiom :
    ExtensionAxiom (boundedAboveFlatPerfectSupportedOpenWaldhausen j T) :=
  Structure.withInverseImageWeak_extensionAxiom
    ((boundedAboveFlatPerfectSupportedInclusion_isExact T.ι).comp
      (perfectSupportedRestrict_exact j T))
    (CofibrationClosedSubcategory.extensionAxiom _ _
      (perfectSupported_cofibrationClosed (j ⁻¹ᵁ T).ι) complexes_extensionAxiom)

/-- The original identity-cone second endpoint is a section of its actual projection. -/
theorem boundedAboveFlatPerfectSupportedOpenJointData_secondEndpointSection :
    RowFactorization.SecondEndpointSection (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpenJointData j T) :=
  complexJointDataOfNested_secondEndpointSection (boundedAboveFlatPerfectSupported T.ι)
    (fun hK hL f => boundedAboveFlatPerfectSupported_mappingCone T.ι hK hL f)
    (fun _ hK => boundedAboveFlatPerfectSupported_shift_one T.ι hK)
    (boundedAboveFlatPerfectSupportedOpenNested j T)

/-- The original canonical coarse-fiber comparison is weak with all premises discharged. -/
@[colib_tag "COL-0384",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenFibration.lean:264-284"
    "adaptation" "Actual extension and cylinder data prove the original canonical fiber map weak"]
theorem boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (canonicalFiberMap (boundedAboveFlatPerfectSupportedOpenNested j T)) :=
  canonicalFiberMap_isWeakHomotopyEquivalence_general
    (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpenWaldhausen_extensionAxiom j T)
    (boundedAboveFlatPerfectSupportedOpenJointData j T)
    (boundedAboveFlatPerfectSupportedOpenJointData_secondEndpointSection j T)

/-- The original connecting map lands in supported bounded-flat K-theory
on the complement of the union. -/
@[colib_tag "COL-0384",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedOpenFibration.lean:288-293"
    "adaptation" "Original connecting homomorphism transported to actual union support"]
def boundedAboveFlatPerfectSupportedOpenConnectingHom (n : ℕ) :
    BoundedAboveFlatPerfectSupportedOpenK j T (n + 1) →*
      BoundedAboveFlatPerfectSupportedK (T ⊔ j.opensRange).ι n :=
  (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom.comp
    (changeWeakConnectingHom (boundedAboveFlatPerfectSupportedOpenNested j T)
      (boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n)

/-- The actual union-supported K-map into the original canonical homotopy fiber. -/
def boundedAboveFlatPerfectSupportedUnionFiberKMap (n : ℕ) :
    BoundedAboveFlatPerfectSupportedK (T ⊔ j.opensRange).ι n →*
      HomotopyGroup.Pi (n + 1)
        (HomotopyFiber (changeWeakMap (boundedAboveFlatPerfectSupportedOpenNested j T))
          (boundedAboveFlatPerfectSupportedOpenNested j T).coarse.kBasepoint)
        (HomotopyFiber.basepoint (changeWeakMap (boundedAboveFlatPerfectSupportedOpenNested j T))
          (boundedAboveFlatPerfectSupportedOpenNested j T).coarse.kBasepoint
          (boundedAboveFlatPerfectSupportedWaldhausen T.ι).kBasepoint
          (changeWeakMap_basepoint (boundedAboveFlatPerfectSupportedOpenNested j T))) :=
  (canonicalFiberKMap (boundedAboveFlatPerfectSupportedOpenNested j T) n).comp
    (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.toMonoidHom

/-- The actual fiber K-map is bijective in every natural degree, including zero. -/
theorem boundedAboveFlatPerfectSupportedUnionFiberKMap_bijective (n : ℕ) :
    Function.Bijective (boundedAboveFlatPerfectSupportedUnionFiberKMap j T n) :=
  (canonicalFiberKMap_bijective_of_weak (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n).comp
    (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm.bijective

/-- Projection is precisely the original supported inclusion K-map. -/
theorem boundedAboveFlatPerfectSupportedUnionFiberKMap_projection (n : ℕ) :
    (HomotopyGroup.piMap n
      (HomotopyFiber.projection (changeWeakMap (boundedAboveFlatPerfectSupportedOpenNested j T))
        (boundedAboveFlatPerfectSupportedOpenNested j T).coarse.kBasepoint)
      (HomotopyFiber.projection_basepoint _ _
        (boundedAboveFlatPerfectSupportedWaldhausen T.ι).kBasepoint
        (changeWeakMap_basepoint (boundedAboveFlatPerfectSupportedOpenNested j T)))).comp
      (boundedAboveFlatPerfectSupportedUnionFiberKMap j T n) =
        boundedAboveFlatPerfectSupportedUnionKMap j T n := by
  rw [boundedAboveFlatPerfectSupportedUnionFiberKMap, ← MonoidHom.comp_assoc]
  erw [canonicalFiberKMap_projection]
  exact boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv_symm_inclusion j T n

/-- The transported boundary retains the actual canonical homotopy-fiber boundary. -/
theorem boundedAboveFlatPerfectSupportedUnionFiberKMap_connecting (n : ℕ)
    (a : BoundedAboveFlatPerfectSupportedOpenK j T (n + 1)) :
    boundedAboveFlatPerfectSupportedUnionFiberKMap j T n
        (boundedAboveFlatPerfectSupportedOpenConnectingHom j T n a) =
      HomotopyFiber.connectingHom (changeWeakMap (boundedAboveFlatPerfectSupportedOpenNested j T))
        (boundedAboveFlatPerfectSupportedOpenNested j T).coarse.kBasepoint
        (boundedAboveFlatPerfectSupportedWaldhausen T.ι).kBasepoint
        (changeWeakMap_basepoint (boundedAboveFlatPerfectSupportedOpenNested j T)) n a := by
  change canonicalFiberKMap (boundedAboveFlatPerfectSupportedOpenNested j T) n
    ((boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n).symm
      (boundedAboveFlatPerfectSupportedOpenAcyclicSupportedKEquiv j T n
        (changeWeakConnectingHom (boundedAboveFlatPerfectSupportedOpenNested j T)
          (boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T)
          n a))) = _
  rw [MulEquiv.symm_apply_apply]
  exact canonicalFiberKMap_connecting
    (boundedAboveFlatPerfectSupportedOpenNested j T)
    (boundedAboveFlatPerfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T) n a

end AlgebraicGeometry.Scheme.Modules
