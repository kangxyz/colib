/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFiberComponent
public import Colib.Topology.HomotopyFiber.ConnectingLoopPathClass
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberObjectClass
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenLongExactSequence

/-! # Boundary of the original normalized forward scalar loop

The inverse orientation of the original scalar-cofiber loop and the negative
coordinate-transpose sign cancel. The actual original connecting homomorphism
therefore sends the forward scalar loop to its original supported cofiber class.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarForwardRelativeBoundary.lean:36-162`
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
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))

/-- The actual normalized path is the inverse of the original component equivalence. -/
theorem perfectScalarNormalizedPath_component
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      ((FundamentalGroup.fromPath ⟦perfectOpenObjectLoopNormalizedPath j K α⟧) : FundamentalGroup _
        (Path.refl _)) =
    ((perfectOpenNested j).coarse.identityCofiberComponentEquiv K 1).symm
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm (FundamentalGroup.fromPath ⟦α⟧)) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [MulEquiv.apply_symm_apply]
  have hc := perfectOpenObjectLoopKOneNormalization_path j K α
  rw [perfectOpenObjectLoopKOneNormalization_component, MulEquiv.apply_symm_apply] at hc
  exact hc.symm

/-- Undoing the loop shift of the actual normalized path is exactly the existing K-one class. -/
theorem perfectScalarNormalizedPath_class
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    (loopShiftMulEquiv 0).symm
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        ((FundamentalGroup.fromPath ⟦perfectOpenObjectLoopNormalizedPath j K α⟧) : FundamentalGroup
          _ (Path.refl _))) =
      loopKOneNormalization ((perfectOpenNested j).coarse.kZeroObjectLoop K)
        (FundamentalGroup.fromPath ⟦α⟧) := by
  apply (loopShiftMulEquiv 0).injective
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact (perfectOpenObjectLoopKOneNormalization_path j K α).symm

/-- Translating the actual normalized loop recovers the original object-component class. -/
theorem perfectScalarComponentLoop_normalized
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    ((FundamentalGroup.fromPath ⟦perfectScalarComponentLoop j K (perfectOpenObjectLoopNormalizedPath
      j K α)⟧) :
      FundamentalGroup _ ((perfectOpenNested j).coarse.kZeroObjectLoop K)) =
        (FundamentalGroup.fromPath ⟦α⟧) := by
  rw [← perfectScalarComponentLoop_class, perfectScalarNormalizedPath_component,
    Equiv.apply_symm_apply, MulEquiv.apply_symm_apply]

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The original normalized boundary loop lies in the original cofiber's actual fiber component. -/
theorem perfectScalarNormalizedFiber_joined :
    Joined
      (HomotopyFiber.loopInclusion
        (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _))
        (Path.refl (perfectOpenNested j).coarse.kBasepoint)
        (Path.refl (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kBasepoint)
          (basedLoopMap_refl _ _)
        (perfectOpenObjectLoopNormalizedPath j K (perfectScalarCofiberBoundaryLoop j r q hq K)))
      (canonicalFiberObjectLoopTranspose (perfectOpenNested j)
        (perfectOpenScalarCofiberAcyclic r j q hq K)) := by
  let β := perfectScalarCofiberBoundaryLoop j r q hq K
  let β₀ := perfectOpenObjectLoopNormalizedPath j K β
  let e := perfectScalarFiberComponentEquiv j K
  apply joined_of_equiv e
  have p₁ := componentLoopFiberPath (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j)) ((RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace).kZeroObjectLoop K)
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
    ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).identityCofiberSuffixPath K) β₀
  obtain ⟨H⟩ := Quotient.exact
    (congrArg End.asHom (perfectScalarComponentLoop_normalized j K β))
  let p₂ := (pathOfPathHomotopy H).map
    (HomotopyFiber.loopInclusion
      (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _))
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop K)
      (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
        (perfectOpenNested j).zero_eq.symm K)).continuous
  let p₃ := perfectScalarCofiberFiberBoundaryPath j r q hq K
  exact ⟨(p₁.symm.trans (p₂.trans p₃)).cast rfl
    (perfectScalarFiberComponentEquiv_canonical j K _)⟩

/-- The original fiber-loop homeomorphism retains the normalized cofiber loop class. -/
theorem perfectScalarNormalizedFiber_loopClass :
    ((FundamentalGroup.fromPath ⟦HomotopyFiber.loopConnectingMap (changeWeakMap (perfectOpenNested
      j))
      (changeWeakMap_basepoint _)
      (perfectOpenObjectLoopNormalizedPath j K (perfectScalarCofiberBoundaryLoop j r q hq K))⟧) :
      FundamentalGroup _ (HomotopyFiber.basepoint _ _ _ (changeWeakMap_basepoint _))) =
    (FundamentalGroup.fromPath ⟦canonicalFiberObjectLoop (perfectOpenNested j)
      (perfectOpenScalarCofiberAcyclic r j q hq K)⟧) := by
  obtain ⟨p⟩ := perfectScalarNormalizedFiber_joined j K r q hq
  let e := HomotopyFiber.loopFiberHomeomorph (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint _)
  let p' := p.map e.continuous
  apply End.ext
  apply Quotient.sound
  exact ⟨pathHomotopyOfPath (p'.cast rfl (e.apply_symm_apply _).symm)⟩

/-- The actual topological connecting map of the original forward scalar loop is its cofiber. -/
theorem perfectScalarForward_fiberBoundary :
    HomotopyFiber.connectingHom (changeWeakMap (perfectOpenNested j))
      (perfectOpenNested j).coarse.kBasepoint (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace).kBasepoint
      (changeWeakMap_basepoint _) 0 (perfectScalarForwardKOneClass j K r q hq) =
    canonicalFiberKMap (perfectOpenNested j) 0
      ((acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCofiberAcyclic r j q hq K)) := by
  have hs := connectingHom_loop_path (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint _)
    (perfectOpenObjectLoopNormalizedPath j K (perfectScalarCofiberBoundaryLoop j r q hq K))
  rw [perfectScalarNormalizedPath_class] at hs
  change _ = HomotopyFiber.connectingHom _ _ _ _ 0
    (perfectScalarCofiberBoundaryKOneClass j K r q hq)⁻¹ at hs
  rw [perfectScalarCofiberBoundaryKOneClass_eq_inv, inv_inv] at hs
  rw [← hs, canonicalFiberKMap_object, perfectScalarNormalizedFiber_loopClass]

/-- No boundary compatibility is assumed: the original relative boundary is the cofiber class. -/
theorem perfectScalarForward_changeWeakBoundary :
    changeWeakConnectingHom (perfectOpenNested j)
      (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) 0
      (perfectScalarForwardKOneClass j K r q hq) =
    (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
      (perfectOpenScalarCofiberAcyclic r j q hq K) := by
  apply (canonicalFiberKMap_bijective_of_weak (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) 0).injective
  rw [canonicalFiberKMap_connecting, perfectScalarForward_fiberBoundary]

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarForwardRelativeBoundary.lean:36-162"
    "adaptation"
  "The actual normalized scalar path and proved double-loop transpose inverse cancel to give the
    positive original relative cofiber class"]
  perfectScalarForward_fiberBoundary perfectScalarForward_changeWeakBoundary

end AlgebraicGeometry.Scheme.Modules
