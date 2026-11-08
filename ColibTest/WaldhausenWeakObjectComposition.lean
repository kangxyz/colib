/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectCompositionTrack
import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectNaturality

/-! # Prepared full-coordinate weak-object composition regressions

Source-only, UNCOMPILED. Independent category universes and three unrelated objects are kept.
Every selected API is exercised with its full original type. Additional statements retain
both half intervals, affine interpolation, actual inverse comparisons and strict naturality
at two independent times. No assumptions equating the three objects are added.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Waldhausen Convexity unitInterval Topology SSet
open scoped Simplicial Topology
universe u v
namespace ColibTest.WaldhausenWeakObjectComposition

section Composition
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

/-- Complete original API: `weakObjectCompositionRealization_first`. -/
example
    (t z : StdSimplex ℝ (Fin 2)) :
    W.weakObjectCompositionRealization f g hf hg (t, z.map (SimplexCategory.δ 2)) =
      bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex f hf).property) (t, z) :=
  W.weakObjectCompositionRealization_first f g hf hg t z

/-- Complete original API: `weakObjectCompositionRealization_second`. -/
example
    (t z : StdSimplex ℝ (Fin 2)) :
    W.weakObjectCompositionRealization f g hf hg (t, z.map (SimplexCategory.δ 0)) =
      bisimplexRealization W (W.weakObjectSimplex g hg).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex g hg).property) (t, z) :=
  W.weakObjectCompositionRealization_second f g hf hg t z

/-- Complete original API: `weakObjectCompositionRealization_composite`. -/
example
    (t z : StdSimplex ℝ (Fin 2)) :
    W.weakObjectCompositionRealization f g hf hg (t, z.map (SimplexCategory.δ 1)) =
      bisimplexRealization W (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).property) (t, z) :=
  W.weakObjectCompositionRealization_composite f g hf hg t z

/-- Complete original API: `weakObjectCompositionRealization_vertex`. -/
example (e : Fin 2) (z : StdSimplex ℝ (Fin 3)) :
    W.weakObjectCompositionRealization f g hf hg (StdSimplex.single e, z) = W.kBasepoint :=
  W.weakObjectCompositionRealization_vertex f g hf hg e z

include f g hf hg in
/-- Complete original API: `weakObjectCompositionCube`. -/
example : C(unitInterval × (unitInterval × unitInterval), W.Delooping) :=
  W.weakObjectCompositionCube f g hf hg

/-- Complete original API: `weakObjectCompositionRealization_edge`. -/
example (k : Fin 3) (s t : unitInterval) :
    W.weakObjectCompositionRealization f g hf hg
      (StdSimplex.homeomorphI.symm t,
        SimplexCategory.toTopHomeo ⦋2⦌
          (SSet.toTop.map (SSet.stdSimplex.δ k) (realizationInterval.{max u v} s))) =
      W.weakObjectCompositionRealization f g hf hg
        (StdSimplex.homeomorphI.symm t,
          (StdSimplex.homeomorphI.symm s).map (SimplexCategory.δ k)) :=
  W.weakObjectCompositionRealization_edge f g hf hg k s t

/-- Complete original API: `weakObjectCompositionCube_one`. -/
example (s t : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (1, s, t) =
      bisimplexRealization W
        (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          (W.weakObjectSimplex (f ≫ g) (W.weq.comp_mem _ _ hf hg)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) :=
  W.weakObjectCompositionCube_one f g hf hg s t

/-- Complete original API: `weakObjectCompositionCube_zero`. -/
example (s t : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (0, s, t) =
      if h : (s : ℝ) ≤ 1 / 2 then
        bisimplexRealization W (W.weakObjectSimplex f hf).val
          ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
          (StdSimplex.homeomorphI.symm t,
            StdSimplex.homeomorphI.symm
              ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩)
      else
        bisimplexRealization W (W.weakObjectSimplex g hg).val
          ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex g hg).property)
          (StdSimplex.homeomorphI.symm t,
            StdSimplex.homeomorphI.symm
              ⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩) :=
  W.weakObjectCompositionCube_zero f g hf hg s t

/-- Complete original API: `weakObjectCompositionCube_loop_zero`. -/
example (r s : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, s, 0) = W.kBasepoint :=
  W.weakObjectCompositionCube_loop_zero f g hf hg r s

/-- Complete original API: `weakObjectCompositionCube_loop_one`. -/
example (r s : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, s, 1) = W.kBasepoint :=
  W.weakObjectCompositionCube_loop_one f g hf hg r s

include f g hf hg in
/-- Complete original API: `weakObjectCompositionLoops`. -/
example :
    C(unitInterval × unitInterval, Path W.kBasepoint W.kBasepoint) :=
  W.weakObjectCompositionLoops f g hf hg

/-- Complete original API: `weakObjectCompositionLoops_apply`. -/
example (r s t : unitInterval) :
    W.weakObjectCompositionLoops f g hf hg (r, s) t =
      W.weakObjectCompositionCube f g hf hg (r, s, t) :=
  W.weakObjectCompositionLoops_apply f g hf hg r s t

/-- Complete original API: `weakObjectCompositionCube_nerve_zero`. -/
example (r t : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, 0, t) = W.kZeroObjectLoop A t :=
  W.weakObjectCompositionCube_nerve_zero f g hf hg r t

/-- Complete original API: `weakObjectCompositionCube_nerve_one`. -/
example (r t : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, 1, t) = W.kZeroObjectLoop D t :=
  W.weakObjectCompositionCube_nerve_one f g hf hg r t

/-- Complete original API: `weakObjectSquareCompositionTrack`. -/
example :
    ((W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg)).Homotopy
      (W.weakObjectSquareLoopPath (f ≫ g) (W.weq.comp_mem _ _ hf hg)) :=
  W.weakObjectSquareCompositionTrack f g hf hg

/-- Complete original API: `weakObjectSquareCompositionTrack_apply`. -/
example (r s t : unitInterval) :
    W.weakObjectSquareCompositionTrack f g hf hg (r, s) t =
      W.weakObjectCompositionCube f g hf hg (r, s, t) :=
  W.weakObjectSquareCompositionTrack_apply f g hf hg r s t

/-- The actual inverse product-simplex comparison retains both barycentric inputs. -/
example (t : StdSimplex ℝ (Fin 2)) (z : StdSimplex ℝ (Fin 3)) :
    W.weakObjectCompositionRealization f g hf hg (t, z) =
      SSet.toTop.map (bisimplexFamily W (W.weakObjectCompositionPrism f g hf hg)
        (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg))
        ((realizationProductSimplexHomeomorph 1 2).symm (t, z)) := rfl

/-- Comparison r, nerve s and object-loop t retain the actual affine simplex homotopy. -/
example (r s t : unitInterval) :
    W.weakObjectSquareCompositionTrack f g hf hg (r, s) t =
      W.weakObjectCompositionRealization f g hf hg
        (StdSimplex.homeomorphI.symm t,
          SimplexCategory.toTopHomeo ⦋2⦌ (realizationStdSimplexPathHomotopy
            ((realizationEdgePath (simplexEdge.{max u v} 2 0 1 (by decide))).trans
              (realizationEdgePath (simplexEdge.{max u v} 2 1 2 (by decide))))
            (realizationEdgePath (simplexEdge.{max u v} 2 0 2 (by decide))) (r, s))) := rfl

/-- The first half uses the original source-to-middle square, including the midpoint. -/
example (s t : unitInterval) (hs : (s : ℝ) ≤ 1 / 2) :
    W.weakObjectCompositionCube f g hf hg (0, s, t) =
      bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm
          ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩) := by
  simpa only [dite_eq_left hs] using W.weakObjectCompositionCube_zero f g hf hg s t

/-- The second half uses the original middle-to-target square with independent loop time. -/
example (s t : unitInterval) (hs : ¬ (s : ℝ) ≤ 1 / 2) :
    W.weakObjectCompositionCube f g hf hg (0, s, t) =
      bisimplexRealization W (W.weakObjectSimplex g hg).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex g hg).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm
          ⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩) := by
  simpa only [dite_eq_right hs] using W.weakObjectCompositionCube_zero f g hf hg s t

/-- Every comparison time fixes the entire source object loop. -/
example (r : unitInterval) :
    W.weakObjectSquareCompositionTrack f g hf hg (r, 0) = W.kZeroObjectLoop A :=
  Path.Homotopy.source _ r

/-- Every comparison time fixes the entire target object loop. -/
example (r : unitInterval) :
    W.weakObjectSquareCompositionTrack f g hf hg (r, 1) = W.kZeroObjectLoop D :=
  Path.Homotopy.target _ r

/-- The comparison-zero path is literally the concatenation of the two original paths. -/
example (s : unitInterval) :
    W.weakObjectSquareCompositionTrack f g hf hg (0, s) =
      (W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg) s :=
  ContinuousMap.HomotopyWith.apply_zero _ s

/-- The comparison-one path is literally the square of the composite arrow. -/
example (s : unitInterval) :
    W.weakObjectSquareCompositionTrack f g hf hg (1, s) =
      W.weakObjectSquareLoopPath (f ≫ g) (W.weq.comp_mem _ _ hf hg) s :=
  ContinuousMap.HomotopyWith.apply_one _ s

end Composition

section Square
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Complete original API: `weakObjectSquareLoopPath_id`. -/
example (A : C) :
    W.weakObjectSquareLoopPath (𝟙 A) (W.weq.id_mem A) = Path.refl (W.kZeroObjectLoop A) :=
  W.weakObjectSquareLoopPath_id A

/-- Complete original API: `weakObjectSquareLoopPath_congr`. -/
example {A B : C} {f g : A ⟶ B}
    (h : f = g) (hf : W.weq f) (hg : W.weq g) :
    W.weakObjectSquareLoopPath f hf = W.weakObjectSquareLoopPath g hg :=
  W.weakObjectSquareLoopPath_congr h hf hg

/-- Identity is the actual constant path at every nerve and object-loop time. -/
example (A : C) (s t : unitInterval) :
    W.weakObjectSquareLoopPath (𝟙 A) (W.weq.id_mem A) s t = W.kZeroObjectLoop A t := by
  exact congrArg (fun p ↦ p s t) (W.weakObjectSquareLoopPath_id A)

/-- The genuine curried square retains both independently supplied coordinates. -/
example {A B : C} (f : A ⟶ B) (hf : W.weq f) (s t : unitInterval) :
    W.weakObjectSquareLoopPath f hf s t =
      bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) := rfl

end Square

section Exact
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- Complete original API: `bisimplexRealization_postcompose`. -/
example {n m : ℕ}
    (G : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hG : IsSimplex₂ V.cof V.weq G)
    (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    deloopingMap hF (bisimplexRealization V G hG (z, t)) =
      bisimplexRealization W (G ⋙ F) (hG.postcomp V.cof V.weq hF) (z, t) :=
  bisimplexRealization_postcompose hF G hG z t

/-- Complete original API: `objectLoopMapEq`. -/
example (h0 : F.obj V.zero = W.zero) (A : C) :
    basedLoopMap (deloopingMap hF).hom (deloopingMap_basepoint_of_zeroEq hF h0)
        (V.kZeroObjectLoop A) = W.kZeroObjectLoop (F.obj A) :=
  objectLoopMapEq hF h0 A

/-- Complete original API: `weakObjectSquareLoopPath_postcompose`. -/
example (h0 : F.obj V.zero = W.zero)
    {A : C} (f : A ⟶ A) (hf : V.weq f) :
    ((V.weakObjectSquareLoopPath f hf).map
      (basedLoopMap (deloopingMap hF).hom
        (deloopingMap_basepoint_of_zeroEq hF h0)).continuous).cast
        (objectLoopMapEq hF h0 A).symm (objectLoopMapEq hF h0 A).symm =
      W.weakObjectSquareLoopPath (F.map f) (hF.weak f hf) :=
  weakObjectSquareLoopPath_postcompose hF h0 f hf

/-- The strict comparison retains actual outer nerve time s and inner loop time t. -/
example (h0 : F.obj V.zero = W.zero) {A : C} (f : A ⟶ A) (hf : V.weq f)
    (s t : unitInterval) :
    deloopingMap hF (V.weakObjectSquareLoopPath f hf s t) =
      W.weakObjectSquareLoopPath (F.map f) (hF.weak f hf) s t := by
  exact congrArg (fun p ↦ p s t) (weakObjectSquareLoopPath_postcompose hF h0 f hf)

/-- Object-loop naturality is likewise an equality at every loop coordinate. -/
example (h0 : F.obj V.zero = W.zero) (A : C) (t : unitInterval) :
    deloopingMap hF (V.kZeroObjectLoop A t) = W.kZeroObjectLoop (F.obj A) t := by
  exact congrArg (fun p ↦ p t) (objectLoopMapEq hF h0 A)

end Exact

section UnderlyingComparisons

/-- The realization cylinder uses its actual inverse, not a substitute realization model. -/
example (X : SSet.{u}) (z : |X| × TopCat.I.{u}) :
    (realizationCylinderIso X).hom ((realizationCylinderIso X).inv z) = z := by
  change ((realizationCylinderIso X).inv ≫ (realizationCylinderIso X).hom) z = z
  exact congrArg (fun h ↦ h z) (Iso.inv_hom_id (realizationCylinderIso X))

/-- The original affine primitive has its exact coefficients at each coordinate. -/
example {x y : StdSimplex ℝ (Fin 3)} (p q : Path x y)
    (r s : unitInterval) (i : Fin 3) :
    (StdSimplex.pathHomotopy p q (r, s)).weights i =
      (1 - (r : ℝ)) * (p s).weights i + (r : ℝ) * (q s).weights i :=
  StdSimplex.pathHomotopy_apply p q r s i

end UnderlyingComparisons
end ColibTest.WaldhausenWeakObjectComposition
