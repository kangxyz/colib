/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleNativeEndpoint
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleParameterAW

/-! # The original coordinate map at native étale cochain endpoints

The concrete insertion/pairing map is extended and sheafified exactly as in the
coordinate roof. Its target is then compared in the forward direction with
parameter sections of the native target. This is not an inverse to the topology
comparison and does not redefine the motivic parameter or its signed placement.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "P" => SmoothEtaleIntegralPresheaves k
local notation "S" => SmoothEtaleIntegralSheaves k
local notation "a" => smoothEtaleIntegralSheafify k
local notation "J" => SmoothSite.etaleTopology (Spec (CommRingCat.of k))
local notation "R" => SmoothSite.Contraction.parameterProduct
  (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
local notation "F" => reducedTorusIntegralEtaleParameterFunctor k
local notation "e" => ComplexShape.embeddingUpIntLE 0

set_option maxHeartbeats 500000 in
-- The endpoint comparison reduces the ordinary-chain and sheafified-chain presentations.
/-- The actual coordinate map followed by the directed reindexing tail is the
original native integral parameter cochain map, conjugated only at its source. -/
theorem reducedTorusEtaleNativeParameterSquare (q : ℕ) :
    let T := (reducedTorusIntegralParameterReindex k).mapHomologicalComplex (.down ℕ)
    let L := reducedTorusOrdinaryIntegralChains k (q + 1)
    let f := reducedTorusChainCoordinateInsertion k q ≫
      T.map (reducedTorusPresheafChainPairing k q)
    let δ := (NatTrans.mapHomologicalComplex
      ((R).sheafifyReindexComparison J J (ModuleCat.{u + 1} ℤ)) (.down ℕ)).app L
    ((a).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat) ≫
      ((smoothEtaleIntegralNativeExtensionIso k).app (T.obj L)).hom ≫
      ((e).extendFunctor S).map δ ≫
      (Stacks.DerivedIndexing.mapExtendIso F e
        (((a).mapHomologicalComplex (.down ℕ)).obj L)).hom =
    (reducedTorusEtaleNativeOrdinaryEndpointIso k q).hom ≫
      reducedTorusIntegralEtaleParameterCochain k q := by
  intro T L f δ
  let U := (a).mapHomologicalComplex (.up ℤ)
  let D := (a).mapHomologicalComplex (.down ℕ)
  let B := (e).extendFunctor S
  let c := (Stacks.DerivedIndexing.mapExtendIso F e (D.obj L)).hom
  let x := (reducedTorusEtaleNativeOrdinaryEndpointIso k q).hom
  let y := ((smoothEtaleIntegralNativeExtensionIso k).app (T.obj L)).hom
  have h : U.map (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat) ≫ y =
      x ≫ B.map (D.map f) :=
    smoothEtaleIntegralNativeExtensionIso_naturality k f
  change U.map (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat) ≫
      y ≫ B.map δ ≫ c = x ≫ B.map (D.map f ≫ δ) ≫ c
  let d : D.obj (T.obj L) ⟶ ((F).mapHomologicalComplex (.down ℕ)).obj (D.obj L) := δ
  have hcomp : B.map (D.map f ≫ d) = B.map (D.map f) ≫ B.map d :=
    B.map_comp (D.map f) d
  calc
    _ = (U.map (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat) ≫ y) ≫
        (B.map δ ≫ c) := (Category.assoc _ _ _).symm
    _ = (x ≫ B.map (D.map f)) ≫ (B.map δ ≫ c) := congrArg (fun g => g ≫ (B.map δ ≫ c)) h
    _ = x ≫ (B.map (D.map f) ≫ B.map d) ≫ c :=
      (Category.assoc x (B.map (D.map f)) (B.map d ≫ c)).trans
        (congrArg (fun g => x ≫ g) (Category.assoc (B.map (D.map f)) (B.map d) c).symm)
    _ = x ≫ B.map (D.map f ≫ δ) ≫ c := congrArg (fun g => x ≫ g ≫ c) hcomp.symm

end AlgebraicGeometry.PresheafWithTransfers
