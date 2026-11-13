/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.SmashHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Colib.CategoryTheory.Sites.Simplicial.ReducedConeContraction
import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber

/-!
# Realizing pointed cylinder homotopies at a site point

The original quotient map of the pointed cylinder, after taking a
site fiber, gives a native simplicial homotopy with the same two maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} (Φ : J.Point.{w})

/-- The original pointed cylinder homotopy gives a simplicial homotopy of
the original fiber maps. Its zero endpoint is the vertex at face index one. -/
theorem nonempty_fiberSimplicialHomotopy_of_cylinderHomotopic
    {A B : PointedSimplicialPresheaf.{w} C} {f g : A ⟶ B} (h : CylinderHomotopic f g) :
    Nonempty (SSet.Homotopy ((fiberAtPoint C Φ).map g) ((fiberAtPoint C Φ).map f)) := by
  obtain ⟨H, h₀, h₁⟩ := h
  let F := Φ.presheafFiber (A := SSet.{w})
  let e := Sites.constantPresheafFiberNatIso (D := SSet.{w}) Φ
  let K := interval.{w} C
  let p := pushout.inl (intervalAxis A K) (terminal.from K)
  let b := (CartesianMonoidalCategory.tensorLeftIsoProd A.right).app K
  let c := intervalCylinderComparison F e A.right
  let T := F.map (b.hom ≫ p ≫ H.right)
  have bf : b.hom ≫ prod.fst = fst A.right K :=
    IsLimit.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct A.right K)
      (limit.isLimit _) (⟨WalkingPair.left⟩ : Discrete WalkingPair)
  have bs : b.hom ≫ prod.snd = snd A.right K :=
    IsLimit.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct A.right K)
      (limit.isLimit _) (⟨WalkingPair.right⟩ : Discrete WalkingPair)
  have hb (i : Fin 2) : intervalEndpointSlice C A.right i ≫ b.hom =
      prod.lift (𝟙 A.right) (terminal.from A.right ≫ intervalEndpoint C i) := by
    apply prod.hom_ext
    · rw [Category.assoc, bf, intervalEndpointSlice, lift_fst, prod.lift_fst]
    · rw [Category.assoc, bs, intervalEndpointSlice, lift_snd, prod.lift_snd]
  have hs (i : Fin 2) :
      intervalEndpointSlice C A.right i ≫ b.hom ≫ p =
        (cylinderSection A (intervalEndpoint C i)).right := by
    rw [← Category.assoc, hb]
    rfl
  have he (i : Fin 2) (a : A ⟶ B)
      (ha : cylinderSection A (intervalEndpoint C i) ≫ H = a) :
      F.map (intervalEndpointSlice C A.right i) ≫ T = F.map a.right := by
    dsimp only [T]
    rw [← F.map_comp]
    apply congrArg F.map
    calc
      _ = (intervalEndpointSlice C A.right i ≫ b.hom ≫ p) ≫ H.right :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ H.right) (Category.assoc _ _ _))
      _ = (cylinderSection A (intervalEndpoint C i)).right ≫ H.right :=
        congrArg (· ≫ H.right) (hs i)
      _ = _ := congrArg Under.Hom.right ha
  refine ⟨{ h := c.inv ≫ T, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
  · have hi := map_intervalEndpointSlice_comp_comparison F e A.right (1 : Fin 2)
    rw [SSet.stdSimplex.δ_one_eq_const, SSet.comp_const] at hi
    change _ = SSet.ι₀ at hi
    change SSet.ι₀ ≫ c.inv ≫ T = F.map g.right
    rw [← hi, Category.assoc, Iso.hom_inv_id_assoc]
    exact he 1 g h₁
  · have hi := map_intervalEndpointSlice_comp_comparison F e A.right (0 : Fin 2)
    rw [SSet.stdSimplex.δ_zero_eq_const, SSet.comp_const] at hi
    change _ = SSet.ι₁ at hi
    change SSet.ι₁ ≫ c.inv ≫ T = F.map f.right
    rw [← hi, Category.assoc, Iso.hom_inv_id_assoc]
    exact he 0 f h₀
  · ext n z
    exact z.1.property.elim

end CategoryTheory.PointedSimplicialPresheaf
