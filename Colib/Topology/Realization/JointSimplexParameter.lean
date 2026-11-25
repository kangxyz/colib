/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/

module

public import Colib.Topology.Realization.ProductSimplex

/-!
# Realization with two independent simplex parameters

The two actual product homeomorphisms identify a joint simplicial parameter map with its
value at each independent pair of realized coordinates.

Adapted from `Quillen/Topology/Realization/JointSimplexParameter.lean:20-67`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology
universe u
namespace SSet

/-- The actual two successive finite-simplex product comparisons. -/
def realizationDoubleSimplexIso (X : SSet.{u}) (p q : ℕ) :
    |(X ⊗ Δ[p]) ⊗ Δ[q]| ≅ (|X| ⊗ |(Δ[p] : SSet.{u})|) ⊗ |(Δ[q] : SSet.{u})| :=
  realizationProductSimplexIso (X ⊗ Δ[p]) q ≪≫
    (MonoidalCategory.tensorRight |(Δ[q] : SSet.{u})|).mapIso
      (realizationProductSimplexIso X p)

/-- The actual product homeomorphisms commute with a joint simplicial parameter map. -/
theorem realization_joint_parameter (X : SSet.{u}) {p q d : ℕ}
    (f : (Δ[p] ⊗ Δ[q] : SSet.{u}) ⟶ Δ[d]) :
    SSet.toTop.map ((α_ X Δ[p] Δ[q]).hom ≫ X ◁ f) ≫
        (realizationProductSimplexIso X d).hom =
      (realizationDoubleSimplexIso X p q).hom ≫
        (α_ |X| |(Δ[p] : SSet.{u})| |(Δ[q] : SSet.{u})|).hom ≫
          (|X| ◁ ((realizationProductSimplexIso Δ[p] q).inv ≫ SSet.toTop.map f)) := by
  have h := productComparison_associativity SSet.toTop X Δ[p] Δ[q]
  have hi := congrArg (fun t ↦ t ≫
    (|X| ◁ (realizationProductSimplexIso Δ[p] q).inv)) h
  change (SSet.toTop.map (α_ X Δ[p] Δ[q]).hom ≫
      prodComparison SSet.toTop X (Δ[p] ⊗ Δ[q]) ≫
      (|X| ◁ (realizationProductSimplexIso Δ[p] q).hom)) ≫
        (|X| ◁ (realizationProductSimplexIso Δ[p] q).inv) = _ at hi
  simp only [Category.assoc, ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id] at hi
  rw [Functor.map_comp, Category.assoc, realizationProductSimplexIso_hom,
    prodComparison_natural_whiskerLeft]
  rw [← Category.assoc, hi]
  simp only [realizationDoubleSimplexIso, Iso.trans_hom, Functor.mapIso_hom,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rfl

/-- The same compatibility at every independent pair of original realization parameters. -/
theorem realization_joint_parameter_apply (X : SSet.{u}) {p q d : ℕ}
    (f : (Δ[p] ⊗ Δ[q] : SSet.{u}) ⟶ Δ[d])
    (x : |X|) (z : |(Δ[p] : SSet.{u})|) (w : |(Δ[q] : SSet.{u})|) :
    SSet.toTop.map ((α_ X Δ[p] Δ[q]).hom ≫ X ◁ f)
      ((realizationProductSimplexIso (X ⊗ Δ[p]) q).inv
        ((realizationProductSimplexIso X p).inv (x, z), w)) =
      (realizationProductSimplexIso X d).inv
        (x, SSet.toTop.map f ((realizationProductSimplexIso Δ[p] q).inv (z, w))) := by
  apply (TopCat.homeoOfIso (realizationProductSimplexIso X d)).injective
  have h := ConcreteCategory.congr_hom (realization_joint_parameter X f)
    ((realizationDoubleSimplexIso X p q).inv ((x, z), w))
  change (realizationProductSimplexIso X d).hom _ =
    (realizationProductSimplexIso X d).hom ((realizationProductSimplexIso X d).inv _)
  rw [Iso.inv_hom_id_apply]
  simp only [TopCat.comp_app, Iso.inv_hom_id_apply] at h
  exact h

end SSet
