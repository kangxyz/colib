/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopComponentTransport
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberKOneNormalization

/-! # Actual scalar-cofiber component transport

The original fine identity-cofiber suffix supplies the component equivalence.
Its whole image is the original coarse suffix. The unchanged canonical fiber
point is exactly the image of its original constant-component transpose.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFiberComponent.lean:33-108`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native perfect complexes retain
ambient monomorphism cofibrations, quasi-isomorphisms, and the actual signed cone.
The original maps, path coordinates, basepoints, and signs are unchanged. -/

@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology HomotopyGroup
open CategoryTheory.Waldhausen.Fibration
open Topology.HomotopyFiber.LoopComponentTransport
open scoped Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem transport_map_cast {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} {y z : Y} (h : f x = y) (p : Path y z) (n : ℕ)
    (a : HomotopyGroup.Pi n X x) :
    pathTransport (p.cast h rfl) n (HomotopyGroup.map f rfl a) =
      pathTransport p n (HomotopyGroup.map f h a) := by
  cases h
  rfl

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))

/-- The genuine equivalence uses the original object loops and fine identity-cofiber suffix. -/
def perfectScalarFiberComponentEquiv :=
  fiberComponentEquiv (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j)) ((RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace).kZeroObjectLoop K)
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
    ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).identityCofiberSuffixPath K)

/-- The full image suffix is precisely the original coarse identity-cofiber suffix. -/
theorem perfectScalarImageSuffix :
    imageSuffix (changeWeakMap (perfectOpenNested j))
      (changeWeakMap_basepoint (perfectOpenNested j)) ((RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace).kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
        (perfectOpenNested j).zero_eq.symm K)
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).identityCofiberSuffixPath K) =
    ((perfectOpenNested j).coarse.identityCofiberSuffixPath K).cast
      (loopLeftTranslationEquiv_apply _ _) rfl := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  exact identityCofiberSuffixPath_changeWeak (perfectOpenNested j) K s t

/-- The complete canonical fiber point is the actual translated original transpose. -/
theorem perfectScalarFiberComponentEquiv_canonical (A : AcyclicCategory (perfectOpenNested j)) :
    perfectScalarFiberComponentEquiv j K (canonicalFiberObjectLoopTranspose (perfectOpenNested j) A)
      =
      canonicalFiberObjectPrefixTransport (perfectOpenNested j) K A := by
  apply Subtype.ext
  apply Prod.ext
  · change (fiberComponentEquiv _ _ _ _ _ _ _).val.1 = _
    rw [fiberComponentEquiv_source, canonicalFiberObjectLoopTranspose_source]
    rfl
  · change (fiberComponentEquiv _ _ _ _ _ _ _).val.2 = _
    rw [fiberComponentEquiv_path, perfectScalarImageSuffix,
      canonicalFiberObjectPrefixTransport_path]
    rfl

/-- The original translated double loop, with the actual coarse suffix retained. -/
def perfectScalarComponentLoop
    (β : Path (Path.refl (perfectOpenNested j).coarse.kBasepoint)
      (Path.refl (perfectOpenNested j).coarse.kBasepoint)) :=
  componentLoop (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j)) ((RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace).kZeroObjectLoop K)
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
    ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).identityCofiberSuffixPath K) β

/-- The actual component loop has exactly the preexisting identity-cofiber equivalence class. -/
theorem perfectScalarComponentLoop_class
    (β : Path (Path.refl (perfectOpenNested j).coarse.kBasepoint)
      (Path.refl (perfectOpenNested j).coarse.kBasepoint)) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
      ((perfectOpenNested j).coarse.identityCofiberComponentEquiv K 1
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm (FundamentalGroup.fromPath ⟦β⟧))) =
      (FundamentalGroup.fromPath ⟦perfectScalarComponentLoop j K β⟧) := by
  have hc := componentLoop_class (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j)) ((RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace).kZeroObjectLoop K)
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
    ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).identityCofiberSuffixPath K) β
  rw [perfectScalarImageSuffix, transport_map_cast] at hc
  exact hc

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFiberComponent.lean:44-108" "adaptation"
  "The original fine identity-cofiber suffix transports the full canonical-fiber point and retains
    the original coarse component equivalence"]
  perfectScalarFiberComponentEquiv_canonical perfectScalarComponentLoop_class

end AlgebraicGeometry.Scheme.Modules
