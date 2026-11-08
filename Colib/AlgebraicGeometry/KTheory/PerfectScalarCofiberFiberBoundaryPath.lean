/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberBoundaryOrientation

/-!
# The original scalar boundary loop inside the actual localization loop fiber

Projecting the existing explicit iterated-fiber deformation gives a prescribed path from the
original loop inclusion to the translated canonical-fiber point. The separately proved scalar
orientation concerns the reversed original scalar square. This is still at the
specified object-loop component; the Laurent unit's constant-component normalization remains
separate.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFiberBoundaryPath.lean:37-59`
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
open scoped Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))

/-- The original explicit iterated-fiber deformation retains the actual canonical-fiber point. -/
def perfectScalarCofiberFiberBoundaryPath :
    Path
      (HomotopyFiber.loopInclusion
        (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _))
        ((perfectOpenNested j).coarse.kZeroObjectLoop K)
        ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop K)
        (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
          (perfectOpenNested j).zero_eq.symm K)
        (perfectScalarCofiberBoundaryLoop j r q hq K))
      (canonicalFiberObjectPrefixTransport (perfectOpenNested j) K
        (perfectOpenScalarCofiberAcyclic r j q hq K)) := by
  let H := HomotopyFiber.iteratedLeftInverseHomotopy
    (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _))
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
  let z := perfectScalarCofiberIteratedFiber j r q hq K
  exact {
    toFun s := (H (s, z)).val.1
    continuous_toFun := by fun_prop
    source' := congrArg (fun w ↦ w.val.1) (H.apply_zero z)
    target' := congrArg (fun w ↦ w.val.1) (H.apply_one z) }

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFiberBoundaryPath.lean:37-59"
    "adaptation"
  "The original iterated-fiber deformation supplies the actual path to the original transported
    canonical fiber point"]
  perfectScalarCofiberFiberBoundaryPath

end AlgebraicGeometry.Scheme.Modules
