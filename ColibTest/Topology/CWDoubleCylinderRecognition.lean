/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.CWWhitehead

/-! # QuillenTest for exact original-map recognition into the actual cylinder -/
@[expose] public section

open Topology

open TopCat.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory Set
open scoped unitInterval
universe u
namespace ColibTest.Topology.CWDoubleCylinderRecognition

variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]
variable {D : TopCat.{u}} (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
variable {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (TopCat.intervalEndpoints (TopCat.of A)) (endMap f g) l e)
variable {W : Type u} [TopologicalSpace W] [T2Space W]
variable (K : Set W) [CWComplex K] (k : C(K, D)) (hk : IsWeakHomotopyEquivalence k)

/-- The recognized forward map is definitionally the given original map. -/
theorem originalForward : (cwHomotopyEquivOfWeakMap A B C f g sq K k hk).toFun = k := rfl

/-- The inverse is exactly projection of the constructed actual section. -/
theorem projectedInverse : (cwHomotopyEquivOfWeakMap A B C f g sq K k hk).invFun =
    (MappingPath.source k).comp (cwMappingPathSection A B C f g sq K k hk) := rfl

omit [T2Space W] [CWComplex K] in
/-- The section projects to the unchanged original point of D. -/
theorem strictSection (d : D) :
    MappingPath.endpoint k (cwMappingPathSection A B C f g sq K k hk d) = d :=
  ContinuousMap.congr_fun (cwMappingPathSection_endpoint A B C f g sq K k hk) d

/-- Both source homotopy endpoints are the required original maps. -/
theorem leftEndpoints (x : K) :
    cwWeakMapLeftHomotopy A B C f g sq K k hk (0, x) =
      cwWeakMapInverse A B C f g sq K k hk (k x) ∧
    cwWeakMapLeftHomotopy A B C f g sq K k hk (1, x) = x :=
  ⟨(cwWeakMapLeftHomotopy A B C f g sq K k hk).map_zero_left x,
    (cwWeakMapLeftHomotopy A B C f g sq K k hk).map_one_left x⟩

omit [T2Space W] [CWComplex K] in
/-- Both target homotopy endpoints are the required original maps. -/
theorem rightEndpoints (d : D) :
    cwWeakMapRightHomotopy A B C f g sq K k hk (0, d) =
      k (cwWeakMapInverse A B C f g sq K k hk d) ∧
    cwWeakMapRightHomotopy A B C f g sq K k hk (1, d) = d :=
  ⟨(cwWeakMapRightHomotopy A B C f g sq K k hk).map_zero_left d,
    (cwWeakMapRightHomotopy A B C f g sq K k hk).map_one_left d⟩

omit [T2Space W] [CWComplex K] in
/-- The full original stored section path is retained at every time. -/
theorem originalStoredPath (t : I) (d : D) :
    cwWeakMapRightHomotopy A B C f g sq K k hk (t, d) =
      (cwMappingPathSection A B C f g sq K k hk d).val.2 t := rfl

/-- The endpoint specialization retains the actual pushout leg by rfl. -/
theorem originalLeftLeg
    (h : IsWeakHomotopyEquivalence
      (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e)) :
    (cwLeftEndpointHomotopyEquiv A B C f g sq h).toFun =
      gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e := rfl

end ColibTest.Topology.CWDoubleCylinderRecognition
