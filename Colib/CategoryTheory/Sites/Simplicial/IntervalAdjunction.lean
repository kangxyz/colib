/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.HomCongr

/-!
# Adjunctions and interval-local tests

An endofunctor on pointed presheaves with a left adjoint action on the stalkwise
homotopy category preserves interval weak equivalences if its cylinder
projections pass the interval-local tests. The right adjoint takes an
interval-local object to an interval-local object by the same tests.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)

local notation "Qₛ" => toStalkwiseHomotopyCategory C J

variable {F : PointedSimplicialPresheaf.{w} C ⥤ PointedSimplicialPresheaf.{w} C}
  {L R : StalkwiseHomotopyCategory.{w} C J ⥤ StalkwiseHomotopyCategory.{w} C J}
  (α : toStalkwiseHomotopyCategory.{w} C J ⋙ L ≅ F ⋙ toStalkwiseHomotopyCategory C J)
  (adj : L ⊣ R)

private def adjunctionTestEquiv (X : PointedSimplicialPresheaf.{w} C)
    (T : StalkwiseHomotopyCategory.{w} C J) :
    ((Qₛ).obj (F.obj X) ⟶ T) ≃ ((Qₛ).obj X ⟶ R.obj T) :=
  ((α.app X).symm.homCongr (Iso.refl T)).trans (adj.homEquiv ((Qₛ).obj X) T)

private theorem adjunctionTestEquiv_precomp {X Y : PointedSimplicialPresheaf.{w} C}
    (f : X ⟶ Y) {T : StalkwiseHomotopyCategory.{w} C J} (g : (Qₛ).obj (F.obj Y) ⟶ T) :
    adjunctionTestEquiv C J α adj X T ((Qₛ).map (F.map f) ≫ g) =
      (Qₛ).map f ≫ adjunctionTestEquiv C J α adj Y T g := by
  have h : L.map ((Qₛ).map f) ≫ α.hom.app Y =
      α.hom.app X ≫ (Qₛ).map (F.map f) := α.hom.naturality f
  simp only [adjunctionTestEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Iso.app_hom, Category.comp_id]
  rw [← Category.assoc, ← h, Category.assoc, adj.homEquiv_naturality_left]

include α adj in
private theorem bijective_precomp_rightAdjoint_iff {X Y : PointedSimplicialPresheaf.{w} C}
    (f : X ⟶ Y) (T : StalkwiseHomotopyCategory.{w} C J) :
    Function.Bijective (fun g : (Qₛ).obj Y ⟶ R.obj T ↦ (Qₛ).map f ≫ g) ↔
      Function.Bijective (fun g : (Qₛ).obj (F.obj Y) ⟶ T ↦ (Qₛ).map (F.map f) ≫ g) := by
  let eX := adjunctionTestEquiv C J α adj X T
  let eY := adjunctionTestEquiv C J α adj Y T
  let q := fun g : (Qₛ).obj (F.obj Y) ⟶ T ↦ (Qₛ).map (F.map f) ≫ g
  have h : (fun g : (Qₛ).obj Y ⟶ R.obj T ↦ (Qₛ).map f ≫ g) = eX ∘ q ∘ eY.symm := by
    funext g
    change (Qₛ).map f ≫ g = eX ((Qₛ).map (F.map f) ≫ eY.symm g)
    rw [adjunctionTestEquiv_precomp, Equiv.apply_symm_apply]
  rw [h, Function.Bijective.of_comp_iff' eX.bijective,
    Function.Bijective.of_comp_iff _ eY.symm.bijective]

variable (I : Cᵒᵖ ⥤ SSet.{w})

include α adj in
/-- A right adjoint to a stalkwise endofunctor preserves interval locality if
the corresponding presheaf functor sends cylinder projections to interval weak equivalences. -/
theorem isIntervalLocal_rightAdjoint
    (hπ : ∀ X, intervalWeakEquivalences C J I (F.map (cylinderProjection X I)))
    {T : StalkwiseHomotopyCategory.{w} C J} (hT : IsIntervalLocal C J I T) :
    IsIntervalLocal C J I (R.obj T) := by
  intro X
  exact (bijective_precomp_rightAdjoint_iff C J α adj (cylinderProjection X I) T).2
    (hπ X T hT)

include α adj in
/-- Under the stalkwise adjunction, preservation of the cylinder tests gives
preservation of the actual interval weak equivalences. -/
theorem intervalWeakEquivalences_map_of_stalkwiseAdjunction
    (hπ : ∀ X, intervalWeakEquivalences C J I (F.map (cylinderProjection X I)))
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (hf : intervalWeakEquivalences C J I f) :
    intervalWeakEquivalences C J I (F.map f) := by
  intro T hT
  exact (bijective_precomp_rightAdjoint_iff C J α adj f T).1
    (hf (R.obj T) (isIntervalLocal_rightAdjoint C J α adj I hπ hT))

end CategoryTheory.PointedSimplicialPresheaf
