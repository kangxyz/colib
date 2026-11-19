/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.HomotopyLifting
public import Colib.Topology.HELP.FiniteCharacterization

/-!
# Whitehead for the exact original map between classical CW subtypes

The original mapping-path endpoint of a weak map has genuine finite boundary
lifting. Global CW lifting constructs a section over the target. The stored
mapping path gives the right inverse homotopy. Prescribed-endpoint CW homotopy
lifting joins the original constant-path inclusion to the section composed with
the map, and source projection gives the left inverse homotopy.

Both ambient spaces lie in the same universe because the canonical MappingPath
and finite-cube characterization have that restriction. No arbitrary-universe
transport, singular-realization counit, compact HELP, domination, covering
space, or conversion of CW notions is assumed.

Adapted from `Quillen/Topology/CWComplex/Whitehead.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open Topology
noncomputable section
open Set
open scoped unitInterval
universe u
namespace Topology.CWComplex
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [T2Space X] [T2Space Y]
variable (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D]
variable (f : C(C, D)) (hf : IsWeakHomotopyEquivalence f)

omit [T2Space X] [T2Space Y] [CWComplex C] [CWComplex D] in
include hf in
/-- The original mapping-path endpoint has actual finite cube boundary lifting. -/
theorem mappingPath_boundaryLifting : CubicalSubdivision.BoundaryLifting (MappingPath.endpoint f) :=
  (isWeakHomotopyEquivalence_iff_mappingPath_boundaryLifting f).mp hf

/-- Global lifting of the identity on the actual target constructs a genuine
section of the original mapping-path endpoint. -/
def mappingPathSection : C(D, MappingPath f) :=
  globalLift D (MappingPath.endpoint f) (mappingPath_boundaryLifting C D f hf)
    (ContinuousMap.id D)

omit [T2Space X] [CWComplex C] in
/-- The section equation is strict on the original target subtype. -/
theorem mappingPathSection_endpoint :
    (MappingPath.endpoint f).comp (mappingPathSection C D f hf) = ContinuousMap.id D :=
  globalLift_comp D (MappingPath.endpoint f) (mappingPath_boundaryLifting C D f hf)
    (ContinuousMap.id D)

/-- The inverse candidate is projection of the constructed actual section. -/
def weakMapInverse : C(D, C) :=
  (MappingPath.source f).comp (mappingPathSection C D f hf)

/-- The section's original stored paths supply the entire right inverse homotopy. -/
def weakMapRightHomotopy : (f.comp (weakMapInverse C D f hf)).Homotopy (ContinuousMap.id D) where
  toFun z := (mappingPathSection C D f hf z.2).val.2 z.1
  continuous_toFun := by fun_prop
  map_zero_left y := (mappingPathSection C D f hf y).property
  map_one_left y := ContinuousMap.congr_fun (mappingPathSection_endpoint C D f hf) y

/-- The original inclusion and section-composite are joined over the constant
base homotopy; projection back to the source gives the actual left inverse homotopy. -/
def weakMapLeftHomotopy : ((weakMapInverse C D f hf).comp f).Homotopy (ContinuousMap.id C) := by
  let p := MappingPath.endpoint f
  let a₀ := MappingPath.inclusion f
  let a₁ := (mappingPathSection C D f hf).comp f
  have h₀ : p.comp a₀ = f := rfl
  have h₁ : p.comp a₁ = f := by
    apply ContinuousMap.ext
    intro x
    exact ContinuousMap.congr_fun (mappingPathSection_endpoint C D f hf) (f x)
  let H : (p.comp a₀).Homotopy (p.comp a₁) :=
    (ContinuousMap.Homotopy.refl f).cast h₀.symm h₁.symm
  let K := homotopyLift C p (mappingPath_boundaryLifting C D f hf) a₀ a₁ H
  exact (((ContinuousMap.Homotopy.refl (MappingPath.source f)).comp K).symm).cast rfl rfl

/-- A weak equivalence between actual Hausdorff classical CW subtypes has an
actual homotopy inverse, with forward map literally the original f. -/
def homotopyEquivOfWeakHomotopyEquivalence : ContinuousMap.HomotopyEquiv C D where
  toFun := f
  invFun := weakMapInverse C D f hf
  left_inv := ⟨weakMapLeftHomotopy C D f hf⟩
  right_inv := ⟨weakMapRightHomotopy C D f hf⟩

/-- The constructed homotopy equivalence retains the specified original map. -/
theorem homotopyEquivOfWeakHomotopyEquivalence_toFun :
    (homotopyEquivOfWeakHomotopyEquivalence C D f hf).toFun = f := rfl

include hf in
/-- Same-universe classical CW Whitehead, with the exact original forward map. -/
theorem exists_homotopyEquiv_of_isWeakHomotopyEquivalence :
    ∃ e : ContinuousMap.HomotopyEquiv C D, e.toFun = f :=
  ⟨homotopyEquivOfWeakHomotopyEquivalence C D f hf, rfl⟩

/-- The converse uses the existing original-map weak-equivalence theorem. -/
theorem isWeakHomotopyEquivalence_iff_exists_homotopyEquiv :
    IsWeakHomotopyEquivalence f ↔ ∃ e : ContinuousMap.HomotopyEquiv C D, e.toFun = f := by
  constructor
  · intro h
    exact ⟨homotopyEquivOfWeakHomotopyEquivalence C D f h, rfl⟩
  · rintro ⟨e, he⟩
    rw [← he]
    exact isWeakHomotopyEquivalence_of_homotopyEquiv e

end Topology.CWComplex
