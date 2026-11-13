/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.FilteredRealization.StrictLift
public import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Filtered.FinallySmall
import Mathlib.CategoryTheory.Whiskering

/-!
# Strict lifting at an actual site fiber

Every strict compact lifting square at a site point is represented on
an original neighborhood. A strict lift at the fiber of an original
square is represented after refining that same neighborhood.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped Simplicial Topology

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} (Φ : J.Point.{w})
  {P Q : Cᵒᵖ ⥤ SSet.{w}} (f : P ⟶ Q)
  {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [CompactSpace A] [CompactSpace B]

/-- A strict square at an actual site point has a strict representative
in one original neighborhood. -/
theorem exists_strictSquare_toPresheafFiber
    (i : C(A, B)) (a : C(A, |Φ.presheafFiber.obj P|)) (b : C(B, |Φ.presheafFiber.obj Q|))
    (h : (SSet.toTop.map (Φ.presheafFiber.map f)).hom.comp a = b.comp i) :
    ∃ (U : C) (x : Φ.fiber.obj U) (a₀ : C(A, |P.obj (op U)|)) (b₀ : C(B, |Q.obj (op U)|)),
      (SSet.toTop.map (Φ.toPresheafFiber U x P)).hom.comp a₀ = a ∧
      (SSet.toTop.map (Φ.toPresheafFiber U x Q)).hom.comp b₀ = b ∧
      (SSet.toTop.map (f.app (op U))).hom.comp a₀ = b₀.comp i := by
  let E := FinallySmall.fromFilteredFinalModel.{w} Φ.fiber.Elementsᵒᵖ
  let π := E ⋙ (Functor.Elements.π Φ.fiber).op
  let c : Cocone (π ⋙ P) := (Φ.presheafFiberCocone P).whisker E
  let d : Cocone (π ⋙ Q) := (Φ.presheafFiberCocone Q).whisker E
  have hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv E _).symm
    (Φ.isColimitPresheafFiberCocone P)
  have hd : IsColimit d := (Functor.Final.isColimitWhiskerEquiv E _).symm
    (Φ.isColimitPresheafFiberCocone Q)
  have hf (j : _) : c.ι.app j ≫ Φ.presheafFiber.map f =
      (Functor.whiskerLeft π f).app j ≫ d.ι.app j := Φ.toPresheafFiber_naturality f _ _
  obtain ⟨j, a₁, ha₁⟩ := FilteredRealization.compact_factors (π ⋙ P) c hc a
  obtain ⟨k, p, b₀, hb₀, h₀⟩ := FilteredRealization.compact_strictSquare_factors
    (Functor.whiskerLeft π f) c d (Φ.presheafFiber.map f) hf hd j i a₁ b
    ((congrArg (ContinuousMap.comp (SSet.toTop.map (Φ.presheafFiber.map f)).hom) ha₁).trans h)
  refine ⟨(E.obj k).unop.1, (E.obj k).unop.2,
    (SSet.toTop.map ((π ⋙ P).map p)).hom.comp a₁, b₀, ?_, hb₀, h₀⟩
  change (SSet.toTop.map (c.ι.app k)).hom.comp
    ((SSet.toTop.map ((π ⋙ P).map p)).hom.comp a₁) = a
  rw [← ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← Functor.map_comp, c.w, ha₁]

/-- A strict lift at the actual fiber of a square over `U` descends
through a neighborhood refining the given germ at `U`. -/
theorem exists_refinement_of_strictLift_toPresheafFiber
    {U : C} (x : Φ.fiber.obj U) (i : C(A, B))
    (a : C(A, |P.obj (op U)|)) (b : C(B, |Q.obj (op U)|))
    (h : StrictHomotopyLift (SSet.toTop.map (Φ.presheafFiber.map f)).hom i
      ((SSet.toTop.map (Φ.toPresheafFiber U x P)).hom.comp a)
      ((SSet.toTop.map (Φ.toPresheafFiber U x Q)).hom.comp b)) :
    ∃ (V : C) (q : V ⟶ U) (y : Φ.fiber.obj V), Φ.fiber.map q y = x ∧
      StrictHomotopyLift (SSet.toTop.map (f.app (op V))).hom i
        ((SSet.toTop.map (P.map q.op)).hom.comp a) ((SSet.toTop.map (Q.map q.op)).hom.comp b) := by
  let E := FinallySmall.fromFilteredFinalModel.{w} Φ.fiber.Elementsᵒᵖ
  let π := E ⋙ (Functor.Elements.π Φ.fiber).op
  let c : Cocone (π ⋙ P) := (Φ.presheafFiberCocone P).whisker E
  let d : Cocone (π ⋙ Q) := (Φ.presheafFiberCocone Q).whisker E
  have hc : IsColimit c := (Functor.Final.isColimitWhiskerEquiv E _).symm
    (Φ.isColimitPresheafFiberCocone P)
  have hd : IsColimit d := (Functor.Final.isColimitWhiskerEquiv E _).symm
    (Φ.isColimitPresheafFiberCocone Q)
  have hf (j : _) : c.ι.app j ≫ Φ.presheafFiber.map f =
      (Functor.whiskerLeft π f).app j ≫ d.ι.app j := Φ.toPresheafFiber_naturality f _ _
  let e := op (Φ.fiber.elementsMk U x)
  let j := Functor.Final.lift E e
  let q := Functor.Final.homToLift E e
  let p : (E.obj j).unop.1 ⟶ U := q.unop.hom
  have hp : Φ.fiber.map p (E.obj j).unop.2 = x := q.unop.map_val
  let a₁ : C(A, |(π ⋙ P).obj j|) := (SSet.toTop.map (P.map p.op)).hom.comp a
  let b₁ : C(B, |(π ⋙ Q).obj j|) := (SSet.toTop.map (Q.map p.op)).hom.comp b
  have he (T : Cᵒᵖ ⥤ SSet.{w}) :
      (SSet.toTop.map (Φ.toPresheafFiber (E.obj j).unop.1 (E.obj j).unop.2 T)).hom.comp
        (SSet.toTop.map (T.map p.op)).hom =
          (SSet.toTop.map (Φ.toPresheafFiber U x T)).hom := by
    rw [← TopCat.hom_comp, ← Functor.map_comp, Φ.toPresheafFiber_w, hp]
  have h' : StrictHomotopyLift (SSet.toTop.map (Φ.presheafFiber.map f)).hom i
      ((SSet.toTop.map (c.ι.app j)).hom.comp a₁) ((SSet.toTop.map (d.ι.app j)).hom.comp b₁) := by
    dsimp only [a₁, b₁]
    change StrictHomotopyLift _ i
      ((SSet.toTop.map (Φ.toPresheafFiber _ _ P)).hom.comp
        ((SSet.toTop.map (P.map p.op)).hom.comp a))
      ((SSet.toTop.map (Φ.toPresheafFiber _ _ Q)).hom.comp
        ((SSet.toTop.map (Q.map p.op)).hom.comp b))
    rw [← ContinuousMap.comp_assoc, he P, ← ContinuousMap.comp_assoc, he Q]
    exact h
  obtain ⟨k, s, hs⟩ := FilteredRealization.compact_strictLift_eventually
    (Functor.whiskerLeft π f) c d (Φ.presheafFiber.map f) hf hc hd j i a₁ b₁ h'
  let p' : (E.obj k).unop.1 ⟶ U := (q ≫ E.map s).unop.hom
  have hp' : Φ.fiber.map p' (E.obj k).unop.2 = x := (q ≫ E.map s).unop.map_val
  refine ⟨(E.obj k).unop.1, p', (E.obj k).unop.2, hp', ?_⟩
  have hp'' : p' = (E.map s).unop.hom ≫ p := rfl
  rw [hp'', op_comp, P.map_comp, Q.map_comp, Functor.map_comp, Functor.map_comp,
    TopCat.hom_comp, TopCat.hom_comp, ContinuousMap.comp_assoc, ContinuousMap.comp_assoc]
  exact hs

end CategoryTheory.GrothendieckTopology.Point
