/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantHom
import Colib.CategoryTheory.Sites.Simplicial.FiberCylinderHomotopy
import Colib.Topology.Realization.HomotopyBridge

/-!
# Detection of stalkwise weak equivalences between fibrant objects

The inverse in the stalkwise localization has a strict representative.
The inverse identities become cylinder homotopies after realization.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}

private theorem homotopic_realization_of_cylinderEqvGen (Φ : J.Point.{w})
    {X Y : PointedSimplicialPresheaf.{w} C} {f g : X ⟶ Y}
    (h : Relation.EqvGen CylinderHomotopic f g) :
    (SSet.toTop.map ((fiberAtPoint C Φ).map f)).hom.Homotopic
      (SSet.toTop.map ((fiberAtPoint C Φ).map g)).hom := by
  induction h with
  | rel _ _ h =>
    obtain ⟨H⟩ := nonempty_fiberSimplicialHomotopy_of_cylinderHomotopic Φ h
    exact ⟨(SSet.realizationSimplicialHomotopy H).symm⟩
  | refl => exact ContinuousMap.Homotopic.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

private theorem cylinderEqvGen_of_stalkwiseMap_eq
    {X Y : PointedSimplicialPresheaf.{w} C} (hY : IsStalkwiseInjectiveFibrant C J Y)
    {f g : X ⟶ Y} (h : (toStalkwiseHomotopyCategory C J).map f =
      (toStalkwiseHomotopyCategory C J).map g) :
    Relation.EqvGen CylinderHomotopic f g := by
  have e := congrArg (stalkwiseFibrantHomEquiv J hY X) h
  rw [stalkwiseFibrantHomEquiv_map, stalkwiseFibrantHomEquiv_map] at e
  exact _root_.Quotient.exact e

/-- A map of stalkwise injective fibrant objects that becomes an
isomorphism in the stalkwise localization is stalkwise weak. -/
theorem stalkwiseWeakEquivalences_of_isIso_toStalkwiseHomotopyCategory_map
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (hX : IsStalkwiseInjectiveFibrant C J X) (hY : IsStalkwiseInjectiveFibrant C J Y)
    (hf : IsIso ((toStalkwiseHomotopyCategory C J).map f)) :
    stalkwiseWeakEquivalences C J f := by
  let Q := toStalkwiseHomotopyCategory.{w} C J
  let : IsIso (Q.map f) := hf
  obtain ⟨g, hg⟩ := surjective_stalkwise_map_of_isStalkwiseInjectiveFibrant J hX Y
    (inv (Q.map f))
  change Q.map g = inv (Q.map f) at hg
  have hx : Q.map (f ≫ g) = Q.map (𝟙 X) := by rw [Q.map_comp, hg, IsIso.hom_inv_id, Q.map_id]
  have hy : Q.map (g ≫ f) = Q.map (𝟙 Y) := by rw [Q.map_comp, hg, IsIso.inv_hom_id, Q.map_id]
  intro Φ
  let F := fiberAtPoint C Φ ⋙ SSet.toTop
  have h₁ := homotopic_realization_of_cylinderEqvGen Φ (cylinderEqvGen_of_stalkwiseMap_eq hX hx)
  have h₂ := homotopic_realization_of_cylinderEqvGen Φ (cylinderEqvGen_of_stalkwiseMap_eq hY hy)
  change (F.map (f ≫ g)).hom.Homotopic (F.map (𝟙 X)).hom at h₁
  change (F.map (g ≫ f)).hom.Homotopic (F.map (𝟙 Y)).hom at h₂
  rw [F.map_comp, F.map_id, TopCat.hom_comp, TopCat.hom_id] at h₁ h₂
  let e : ContinuousMap.HomotopyEquiv (F.obj X) (F.obj Y) := {
    toFun := (F.map f).hom
    invFun := (F.map g).hom
    left_inv := h₁
    right_inv := h₂ }
  exact Topology.isWeakHomotopyEquivalence_of_homotopyEquiv e

end CategoryTheory.PointedSimplicialPresheaf
