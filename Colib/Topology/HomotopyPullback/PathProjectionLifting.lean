/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.PathProjection
public import Colib.Topology.CubicalSubdivision.BoundaryWeakEquivalence

/-!
# Finite boundary lifting for the two-endpoint path projection

A boundary lifting problem for `HomotopyPullback.pathProjection p` is a lifting
problem for `p` on the full boundary of a cube cylinder. The existing genuine
side/caps pushout and its next-cube boundary identification supply that problem.
The resulting lift preserves the entire given lateral path family, both original
endpoint maps, and the full projected base path. Dimension zero is included.

Only the current literal finite `BoundaryLifting p` is assumed. No compact HELP,
weak singular counit, CW conversion, or target-dependent extension certificate
is inserted.

Adapted from `Quillen/Topology/HomotopyPullback/PathProjectionLifting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology TopCat

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
namespace Topology.CubicalSubdivision
open HomotopyPullback
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}

/-- Finite cube boundary lifting is inherited by the actual two-endpoint
compact-open path projection, with the original lateral map retained exactly. -/
theorem BoundaryLifting.pathProjection (hp : BoundaryLifting p) :
    BoundaryLifting (HomotopyPullback.pathProjection p) := by
  intro n a b hab
  have hstart (z : Boundary n) : a z 0 = (b z.val).val.2.1 :=
    congrArg (fun z : HomotopyPullback p p ↦ z.val.2.1) (hab z)
  have hfinish (z : Boundary n) : a z 1 = (b z.val).val.1 :=
    congrArg (fun z : HomotopyPullback p p ↦ z.val.1) (hab z)
  have hpath (z : Boundary n) (t : I) : p (a z t) = (b z.val).val.2.2 t :=
    congrArg (fun z : HomotopyPullback p p ↦ z.val.2.2 t) (hab z)
  let P := CubicalTests.boundaryPresentation.{u} n
  let e := CubicalTests.boundaryPresentationUnliftedHomeomorph.{u} n
  let side : TopCat.of (P.space × I) ⟶ TopCat.of E :=
    TopCat.ofHom ⟨fun z ↦ a (e z.1) z.2, by fun_prop⟩
  let caps : TopCat.of (CubicalTests.cube.{u} n ⊕ CubicalTests.cube.{u} n) ⟶
      TopCat.of E :=
    TopCat.ofHom ⟨Sum.elim (fun z ↦ (b z.down).val.2.1) (fun z ↦ (b z.down).val.1),
      Continuous.sumElim (by fun_prop) (by fun_prop)⟩
  have w : CylinderBoundary.cylinderBoundaryEnds P.space ≫ side =
      CylinderBoundary.cylinderBoundarySumMap P.map ≫ caps := by
    ext z
    rcases z with z | z
    · exact hstart (e z)
    · exact hfinish (e z)
  let d : CylinderBoundary P.map ⟶ TopCat.of E := pushout.desc side caps w
  have hside : CylinderBoundary.cylinderBoundarySide P.map ≫ d = side :=
    pushout.inl_desc _ _ _
  have hcaps : CylinderBoundary.cylinderBoundaryCaps P.map ≫ d = caps :=
    pushout.inr_desc _ _ _
  let k : C(CubicalTests.cube.{u} n × I, B) :=
    ⟨fun z ↦ (b z.1.down).val.2.2 z.2, by fun_prop⟩
  have hw : d ≫ TopCat.ofHom p =
      CylinderBoundary.cylinderBoundaryMap P.map ≫ TopCat.ofHom k := by
    apply (CylinderBoundary.cylinderBoundary_isPushout P.map).hom_ext
    · rw [← Category.assoc, hside, ← Category.assoc,
        CylinderBoundary.cylinderBoundarySide_map]
      ext ⟨z, t⟩
      exact hpath (e z) t
    · rw [← Category.assoc, hcaps, ← Category.assoc,
        CylinderBoundary.cylinderBoundaryCaps_map]
      ext z
      rcases z with z | z
      · exact (b z.down).property.1.symm
      · exact (b z.down).property.2.symm
  obtain ⟨c, hc, he⟩ := hp.cylinder n d.hom k (fun z ↦ ConcreteCategory.congr_hom hw z)
  have hcside (z : P.space) (t : I) : c (P.map z, t) = a (e z) t := by
    have h := hc (CylinderBoundary.cylinderBoundarySide P.map (z, t))
    have hs := ConcreteCategory.congr_hom
      (CylinderBoundary.cylinderBoundarySide_map P.map) (z, t)
    have hd := ConcreteCategory.congr_hom hside (z, t)
    exact (congrArg c hs).symm.trans (h.trans hd)
  have hczero (z : CubicalTests.cube.{u} n) : c (z, 0) = (b z.down).val.2.1 := by
    have h := hc (CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inl z))
    have hs := ConcreteCategory.congr_hom
      (CylinderBoundary.cylinderBoundaryCaps_map P.map) (Sum.inl z)
    have hd := ConcreteCategory.congr_hom hcaps (Sum.inl z)
    exact (congrArg c hs).symm.trans (h.trans hd)
  have hcone (z : CubicalTests.cube.{u} n) : c (z, 1) = (b z.down).val.1 := by
    have h := hc (CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inr z))
    have hs := ConcreteCategory.congr_hom
      (CylinderBoundary.cylinderBoundaryCaps_map P.map) (Sum.inr z)
    have hd := ConcreteCategory.congr_hom hcaps (Sum.inr z)
    exact (congrArg c hs).symm.trans (h.trans hd)
  let l : C(Cube n, C(I, E)) :=
    ⟨fun x ↦ ⟨fun t ↦ c (ULift.up x, t), by fun_prop⟩, by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : Cube n × I ↦ c (ULift.up z.1, z.2))
      fun_prop⟩
  refine ⟨l, ?_, ?_⟩
  · intro z
    apply ContinuousMap.ext
    intro t
    have h := hcside (e.symm z) t
    have hz : P.map (e.symm z) = ULift.up z.val := by
      apply ULift.ext
      exact congrArg Subtype.val (e.apply_symm_apply z)
    change c (ULift.up z.val, t) = a z t
    simpa only [hz, Homeomorph.apply_symm_apply] using h
  · apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · exact hcone (ULift.up x)
    · apply Prod.ext
      · exact hczero (ULift.up x)
      · apply ContinuousMap.ext
        intro t
        exact ContinuousMap.congr_fun he (ULift.up x, t)

end Topology.CubicalSubdivision
