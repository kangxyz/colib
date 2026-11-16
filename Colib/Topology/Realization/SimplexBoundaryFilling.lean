/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.BoundaryHomotopyExtension
public import Colib.Topology.Cube.SimplexPair
public import Colib.Topology.HELP.WeakCubeFilling

/-!
# Prescribed simplex boundary homotopies

The original cube-simplex boundary pair transports the side and both endpoint
maps to the actual cubical boundary. Singleton homotopy in the simplex's own
dimension fills that boundary without changing any of the supplied maps.

Adapted from `Quillen/Topology/Realization/SimplexBoundaryFilling.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology
open scoped Topology unitInterval

universe u

namespace Convexity.StdSimplex

variable {Z : Type u} [TopologicalSpace Z]

/-- Actual simplex-boundary homotopy filling with both endpoints prescribed.
Only the homotopy set in dimension `d` is used. In particular dimension zero
is included, and higher homotopy groups are never assumed to vanish. -/
theorem exists_simplex_homotopy_of_boundary (d : ℕ)
    (hs : ∀ z : Z, Subsingleton (HomotopyGroup.Pi d Z z))
    (f g : C(StdSimplex ℝ (Fin (d + 1)), Z))
    (H : C(boundary d × I, Z))
    (hzero : ∀ b : boundary d, H (b, 0) = f b.val)
    (hone : ∀ b : boundary d, H (b, 1) = g b.val) :
    ∃ K : f.Homotopy g, ∀ (b : boundary d) (t : I),
      K (t, b.val) = H (b, t) := by
  let e := Cube.simplexHomeomorph d
  let f' : C(Unit × StdSimplex ℝ (Fin (d + 1)), Z) :=
    ⟨fun x ↦ f x.2, by fun_prop⟩
  let H' : C((Unit × boundary d) × I, Z) :=
    ⟨fun x ↦ H (x.1.2, x.2), by fun_prop⟩
  have hzero' : ∀ x b, H' ((x, b), 0) = f' (x, b.val) :=
    fun _ b ↦ hzero b
  let G := closedCylinderGlue (boundary d) (isClosed_boundary d)
    f' H' hzero'
  let q : C(CubicalTests.Horn.{u} d, Unit × closedCylinderUnion (boundary d)) := {
    toFun x := ((), ⟨(e x.val.1.down, x.val.2), by
      rcases x.property with hx | ht
      · exact Or.inl ((Cube.simplexHomeomorph_mem_boundary_iff d _).mpr hx)
      · exact Or.inr ht⟩)
    continuous_toFun := by fun_prop }
  let a : C(CubicalTests.Horn.{u} d, Z) := G.comp q
  have ha_side (x : CubicalTests.boundary.{u} d) (t : I) :
      a ⟨(x.val, t), Or.inl x.property⟩ =
        H (⟨e x.val.down, (Cube.simplexHomeomorph_mem_boundary_iff d _).mpr x.property⟩, t) := by
    exact closedCylinderGlueFun_side (boundary d) f' H' ()
      ⟨e x.val.down, (Cube.simplexHomeomorph_mem_boundary_iff d _).mpr x.property⟩ t
  have ha_bottom (x : CubicalTests.cube.{u} d) :
      a ⟨(x, 0), Or.inr rfl⟩ = f (e x.down) := by
    exact closedCylinderGlueFun_bottom (boundary d) f' H' hzero' () (e x.down)
  let b : C(CubicalTests.cube.{u} d, Z) := ⟨fun x ↦ g (e x.down), by fun_prop⟩
  have w : CubicalTests.boundaryInclusion d ≫ TopCat.ofHom b =
      CubicalTests.topRim d ≫ TopCat.ofHom a := by
    ext x : 1
    exact ((ha_side x 1).trans (hone _)).symm
  let α : C(CubicalTests.ProductBoundary.{u} d, Z) :=
    (CubicalTests.hornTopDesc (TopCat.ofHom b) (TopCat.ofHom a) w).hom
  have hα_top (x : CubicalTests.cube.{u} d) :
      α (CubicalTests.topFace d x) = g (e x.down) :=
    ConcreteCategory.congr_hom (CubicalTests.topFace_desc
      (TopCat.ofHom b) (TopCat.ofHom a) w) x
  have hα_horn (x : CubicalTests.Horn.{u} d) :
      α (CubicalTests.hornInclusion d x) = a x :=
    ConcreteCategory.congr_hom (CubicalTests.hornInclusion_desc
      (TopCat.ofHom b) (TopCat.ofHom a) w) x
  obtain ⟨c, hc⟩ := CubicalTests.exists_extend_productBoundary d hs α
  have hcbottom (x : CubicalTests.cube.{u} d) : c (x, 0) = f (e x.down) :=
    (ContinuousMap.congr_fun hc (CubicalTests.hornInclusion d ⟨(x, 0), Or.inr rfl⟩)).trans
      ((hα_horn _).trans (ha_bottom x))
  have hctop (x : CubicalTests.cube.{u} d) : c (x, 1) = g (e x.down) :=
    (ContinuousMap.congr_fun hc (CubicalTests.topFace d x)).trans (hα_top x)
  have hcside (x : CubicalTests.boundary.{u} d) (t : I) :
      c (x.val, t) =
        H (⟨e x.val.down, (Cube.simplexHomeomorph_mem_boundary_iff d _).mpr x.property⟩, t) :=
    (ContinuousMap.congr_fun hc
      (CubicalTests.hornInclusion d ⟨(x.val, t), Or.inl x.property⟩)).trans
        ((hα_horn _).trans (ha_side x t))
  let K : f.Homotopy g := {
    toFun x := c (ULift.up (e.symm x.2), x.1)
    continuous_toFun := by fun_prop
    map_zero_left x := (hcbottom ⟨e.symm x⟩).trans (congrArg f (e.apply_symm_apply x))
    map_one_left x := (hctop ⟨e.symm x⟩).trans (congrArg g (e.apply_symm_apply x)) }
  refine ⟨K, fun x t ↦ ?_⟩
  let y : CubicalTests.boundary.{u} d :=
    ⟨ULift.up (e.symm x.val), (Cube.simplexHomeomorph_mem_boundary_iff d _).mp
      (by
        change e (e.symm x.val) ∈ boundary d
        rw [e.apply_symm_apply]
        exact x.property)⟩
  have hy : (⟨e y.val.down,
      (Cube.simplexHomeomorph_mem_boundary_iff d _).mpr y.property⟩ : boundary d) = x :=
    Subtype.ext (e.apply_symm_apply x.val)
  exact (hcside y t).trans (congrArg (fun z ↦ H (z, t)) hy)

end Convexity.StdSimplex
