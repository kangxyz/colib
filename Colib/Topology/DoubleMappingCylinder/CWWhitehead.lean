/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.CWLifting
public import Colib.Topology.CWComplex.Whitehead

/-!
# Weak-map recognition for the actual double cylinder target

The target is the literal TopCat pushout of arbitrary maps of Hausdorff classical
CW subtypes. Its constructed lifting theorem supplies the mapping-path section.
Prescribed-endpoint lifting on the original CW source supplies the other inverse
homotopy. No CW structure, Hausdorff instance, domination, or covering data on
the pushout is assumed. Actual weakness of the specified map remains a premise.
-/
@[expose] public section

open Topology
noncomputable section
open CategoryTheory Limits MonoidalCategory Set
open scoped unitInterval
universe u
namespace TopCat.DoubleCylinder
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

/-- The constructed cylinder lifting theorem gives an actual endpoint section
for the original weak map, without target CW or domination data. -/
def cwMappingPathSection : C(D, MappingPath k) :=
  cwLift A B C f g sq (MappingPath.endpoint k)
    ((isWeakHomotopyEquivalence_iff_mappingPath_boundaryLifting k).mp hk) (ContinuousMap.id D)

omit [T2Space W] [CWComplex K] in
/-- The mapping-path section lies strictly over the identity of the actual pushout. -/
theorem cwMappingPathSection_endpoint :
    (MappingPath.endpoint k).comp (cwMappingPathSection A B C f g sq K k hk) =
      ContinuousMap.id D :=
  cwLift_comp A B C f g sq (MappingPath.endpoint k)
    ((isWeakHomotopyEquivalence_iff_mappingPath_boundaryLifting k).mp hk) (ContinuousMap.id D)

/-- Project the actual section to obtain the inverse of the original weak map. -/
def cwWeakMapInverse : C(D, K) :=
  (MappingPath.source k).comp (cwMappingPathSection A B C f g sq K k hk)

/-- The section's actual stored paths give the full right inverse homotopy. -/
def cwWeakMapRightHomotopy :
    (k.comp (cwWeakMapInverse A B C f g sq K k hk)).Homotopy (ContinuousMap.id D) where
  toFun z := (cwMappingPathSection A B C f g sq K k hk z.2).val.2 z.1
  continuous_toFun := by fun_prop
  map_zero_left d := (cwMappingPathSection A B C f g sq K k hk d).property
  map_one_left d := ContinuousMap.congr_fun
    (cwMappingPathSection_endpoint A B C f g sq K k hk) d

/-- Lift the constant base homotopy between the original inclusion and the
section-composite on the CW source, then project and reverse it. -/
def cwWeakMapLeftHomotopy :
    ((cwWeakMapInverse A B C f g sq K k hk).comp k).Homotopy (ContinuousMap.id K) := by
  let p := MappingPath.endpoint k
  let a₀ := MappingPath.inclusion k
  let a₁ := (cwMappingPathSection A B C f g sq K k hk).comp k
  have h₀ : p.comp a₀ = k := rfl
  have h₁ : p.comp a₁ = k := by
    apply ContinuousMap.ext
    intro x
    exact ContinuousMap.congr_fun (cwMappingPathSection_endpoint A B C f g sq K k hk) (k x)
  let H : (p.comp a₀).Homotopy (p.comp a₁) :=
    (ContinuousMap.Homotopy.refl k).cast h₀.symm h₁.symm
  let L := Topology.CWComplex.homotopyLift K p
    ((isWeakHomotopyEquivalence_iff_mappingPath_boundaryLifting k).mp hk) a₀ a₁ H
  exact (((ContinuousMap.Homotopy.refl (MappingPath.source k)).comp L).symm).cast rfl rfl

/-- Actual weak-map recognition with an original CW source and this literal
cylinder target; the forward map is definitionally the specified original map. -/
def cwHomotopyEquivOfWeakMap : ContinuousMap.HomotopyEquiv K D where
  toFun := k
  invFun := cwWeakMapInverse A B C f g sq K k hk
  left_inv := ⟨cwWeakMapLeftHomotopy A B C f g sq K k hk⟩
  right_inv := ⟨cwWeakMapRightHomotopy A B C f g sq K k hk⟩

/-- The construction preserves the exact original forward map. -/
theorem cwHomotopyEquivOfWeakMap_toFun :
    (cwHomotopyEquivOfWeakMap A B C f g sq K k hk).toFun = k := rfl

include A B C f g sq hk in
/-- Existence of an actual inverse follows from original weakness and the
proved geometric lifting construction, with no comparison-map certificate. -/
theorem exists_cwHomotopyEquivOfWeakMap :
    ∃ q : ContinuousMap.HomotopyEquiv K D, q.toFun = k :=
  ⟨cwHomotopyEquivOfWeakMap A B C f g sq K k hk, rfl⟩

/-- In particular the original left endpoint, when weak, is a homotopy equivalence. -/
def cwLeftEndpointHomotopyEquiv (h : IsWeakHomotopyEquivalence (gapLeftEndpoint (B := TopCat.of B)
      (C := TopCat.of C) e)) :
    ContinuousMap.HomotopyEquiv B D :=
  cwHomotopyEquivOfWeakMap A B C f g sq B (gapLeftEndpoint (B := TopCat.of B)
      (C := TopCat.of C) e) h

/-- The endpoint recognition result keeps the original left leg literally. -/
theorem cwLeftEndpointHomotopyEquiv_toFun
    (h : IsWeakHomotopyEquivalence (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e)) :
    (cwLeftEndpointHomotopyEquiv A B C f g sq h).toFun = gapLeftEndpoint (B := TopCat.of B)
      (C := TopCat.of C) e := rfl

end TopCat.DoubleCylinder
