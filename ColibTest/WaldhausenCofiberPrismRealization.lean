/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Colib.KTheory.Waldhausen.BisimplexRealization
import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberPrismComposition
import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberPrismHomotopy
import Colib.KTheory.Waldhausen.GrothendieckComparison.CofiberPrismRealization
import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectCompositionRealization
import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectIdentitySquare
import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectSquareTrack
import Colib.KTheory.Waldhausen.ObjectTransformationSquareRealization
import Colib.KTheory.Waldhausen.ObjectTransformationTrack

/-!
# Source-only prescribed cofiber-prism realization regressions

These statements cover actual product inverse coordinates, all three S-faces, both whole
nerve faces, the independent comparison/nerve/loop inputs, endpoint lines, cylinder equality,
and the identity weak square as an entire constant path. They are UNCOMPILED.
Statements reproduce the selected source interfaces; proofs consume the new native names.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open MonoidalCategory CartesianMonoidalCategory Convexity SSet unitInterval
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open scoped Simplicial Topology
universe u v

namespace CategoryTheory.Waldhausen
section BisimplexRealization
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {n m : ℕ} (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)

example
    (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    bisimplexRealization W F hF (z, t) =
      SSet.toTop.map (bisimplexFamily W F hF)
        ((realizationProductSimplexHomeomorph n m).symm (z, t)) :=
  bisimplexRealization_apply W F hF z t

example {n' m' : ℕ}
    (α : ⦋n'⦌ ⟶ ⦋n⦌) (β : ⦋m'⦌ ⟶ ⦋m⦌)
    (z : StdSimplex ℝ (Fin (n' + 1))) (t : StdSimplex ℝ (Fin (m' + 1))) :
    bisimplexRealization W F hF (z.map α, t.map β) =
      bisimplexRealization W (gridMap₂ α β ⋙ F)
        (hF.precomp W.cof W.weq α β) (z, t) :=
  bisimplexRealization_precomp W F hF α β z t

example {G : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C}
    (hG : IsSimplex₂ W.cof W.weq G) (h : F = G) :
    bisimplexRealization W F hF = bisimplexRealization W G hG :=
  bisimplexRealization_congr W F hF hG h

-- The actual inverse comparison is the definition, with independent simplex coordinates.
example (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    bisimplexRealization W F hF (z, t) =
      SSet.toTop.map (bisimplexFamily W F hF)
        ((realizationProductSimplexHomeomorph n m).symm (z, t)) := rfl

end BisimplexRealization
end CategoryTheory.Waldhausen

namespace CategoryTheory.Waldhausen.Structure
section CofiberPrismComposition
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

example (r t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, 0, t) =
      W.cofiberObjectLoopTrack (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W) (r, t) :=
  cofiberPrismCompositionCube_nerve_zero W i q hi hwi hQ r t

example (r t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, 1, t) =
      W.cofiberObjectLoopTrack i q hi hQ (r, t) :=
  cofiberPrismCompositionCube_nerve_one W i q hi hwi hQ r t

example (k : Fin 3) (s t : unitInterval) :
    realizationSimplicialHomotopy (W.cofiberPrismHomotopy i q hi hwi hQ)
        (s, SSet.toTop.map (SSet.stdSimplex.δ k) (realizationInterval t)) =
      W.cofiberPrismRealization i q hi hwi hQ
        ((Convexity.StdSimplex.homeomorphI.symm t).map (SimplexCategory.δ k), s) :=
  cofiberPrismHomotopy_edge W i q hi hwi hQ k s t

example (s t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (1, s, t) =
      bisimplexRealization W (W.weakObjectSimplex i hwi).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex i hwi).property)
        (Convexity.StdSimplex.homeomorphI.symm t,
          Convexity.StdSimplex.homeomorphI.symm s) :=
  cofiberPrismCompositionCube_comparison_one W i q hi hwi hQ s t

example (s t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (0, s, t) =
      if h : (t : ℝ) ≤ 1 / 2 then
        bisimplexRealization W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
          ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
            (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
          (Convexity.StdSimplex.homeomorphI.symm
            ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩,
            Convexity.StdSimplex.homeomorphI.symm s)
      else
        bisimplexRealization W (W.weakObjectSimplex (0 : W.zero ⟶ Q)
            (cofiberTwo_quotient_weak W i q hi hwi hQ)).val
          ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
            (W.weakObjectSimplex (0 : W.zero ⟶ Q)
              (cofiberTwo_quotient_weak W i q hi hwi hQ)).property)
          (Convexity.StdSimplex.homeomorphI.symm
            ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩,
            Convexity.StdSimplex.homeomorphI.symm s) :=
  cofiberPrismCompositionCube_comparison_zero W i q hi hwi hQ s t

example (r s : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, s, 0) = W.kBasepoint :=
  cofiberPrismCompositionCube_loop_zero W i q hi hwi hQ r s

example (r s : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, s, 1) = W.kBasepoint :=
  cofiberPrismCompositionCube_loop_one W i q hi hwi hQ r s

example (r s t : unitInterval) :
    W.cofiberPrismCompositionLoops i q hi hwi hQ (r, s) t =
      W.cofiberPrismCompositionCube i q hi hwi hQ (r, s, t) :=
  cofiberPrismCompositionLoops_apply W i q hi hwi hQ r s t

-- Comparison r, nerve s and loop t are three independent inputs to the actual cube.
example (r s t : unitInterval) :
    W.cofiberPrismCompositionCube i q hi hwi hQ (r, s, t) =
      realizationSimplicialHomotopy (W.cofiberPrismHomotopy i q hi hwi hQ)
        (s, realizationStdSimplexPathHomotopy
          ((realizationEdgePath (simplexEdge.{max u v} 2 0 1 (by decide))).trans
            (realizationEdgePath (simplexEdge.{max u v} 2 1 2 (by decide))))
          (realizationEdgePath (simplexEdge.{max u v} 2 0 2 (by decide))) (r, t)) := rfl

-- Currying changes neither the coordinate order nor the underlying continuous values.
example (r s t : unitInterval) :
    W.cofiberPrismCompositionLoops i q hi hwi hQ (r, s) t =
      W.cofiberPrismCompositionCube i q hi hwi hQ (r, s, t) := rfl

end CofiberPrismComposition
end CategoryTheory.Waldhausen.Structure

namespace CategoryTheory.Waldhausen.Structure
section CofiberPrismHomotopy
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

example :
    SSet.ι₀ ≫ bisimplexFamily W (cofiberTwoPrism W i q hi hwi hQ)
        (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ) =
      SSet.yonedaEquiv.symm
        (W.cofiberObjectSimplex (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
          (cofiberTwo_identity_square W)) :=
  cofiberPrismFamily_zero W i q hi hwi hQ

example :
    SSet.ι₁ ≫ bisimplexFamily W (cofiberTwoPrism W i q hi hwi hQ)
        (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ) =
      SSet.yonedaEquiv.symm (W.cofiberObjectSimplex i q hi hQ) :=
  cofiberPrismFamily_one W i q hi hwi hQ

example
    (z : StdSimplex ℝ (Fin 3)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z, t) =
      realizationSimplicialHomotopy (W.cofiberPrismHomotopy i q hi hwi hQ)
        (t, (SimplexCategory.toTopHomeo ⦋2⦌).symm z) :=
  cofiberPrismRealization_homotopy W i q hi hwi hQ z t

example (j : Fin 3) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ j) ▷ Δ[1] ≫
        (W.cofiberPrismHomotopy i q hi hwi hQ).h =
      fst Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) :=
  cofiberPrismHomotopy_vertex_zero W i q hi hwi hQ j

example (j : Fin 3) (t : unitInterval) :
    realizationSimplicialHomotopy (W.cofiberPrismHomotopy i q hi hwi hQ)
      (t, realizationPoint (X := (Δ[2] : SSet.{max u v}))
        (ULift.up (SimplexCategory.const ⦋0⦌ ⦋2⦌ j))) = W.kBasepoint :=
  cofiberPrismHomotopy_fixed_vertex W i q hi hwi hQ j t

-- The homotopy carries the exact certified grid, rather than a chosen existence witness.
example : (W.cofiberPrismHomotopy i q hi hwi hQ).h =
    bisimplexFamily W (cofiberTwoPrism W i q hi hwi hQ)
      (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ) := rfl

end CofiberPrismHomotopy
end CategoryTheory.Waldhausen.Structure

namespace CategoryTheory.Waldhausen.Structure
section CofiberPrismRealization
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

example (z : StdSimplex ℝ (Fin 3)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z, t) =
      bisimplexRealization W (cofiberTwoPrism W i q hi hwi hQ)
        (cofiberTwoPrism_isSimplex₂ W i q hi hwi hQ)
        (z, StdSimplex.homeomorphI.symm t) :=
  cofiberPrismRealization_apply W i q hi hwi hQ z t

example
    (z : StdSimplex ℝ (Fin 2)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z.map (SimplexCategory.δ 2), t) =
      bisimplexRealization W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
        (z, StdSimplex.homeomorphI.symm t) :=
  cofiberPrismRealization_source_face W i q hi hwi hQ z t

example
    (z : StdSimplex ℝ (Fin 2)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z.map (SimplexCategory.δ 1), t) =
      bisimplexRealization W (W.weakObjectSimplex i hwi).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex i hwi).property)
        (z, StdSimplex.homeomorphI.symm t) :=
  cofiberPrismRealization_middle_face W i q hi hwi hQ z t

example
    (z : StdSimplex ℝ (Fin 2)) (t : unitInterval) :
    W.cofiberPrismRealization i q hi hwi hQ (z.map (SimplexCategory.δ 0), t) =
      bisimplexRealization W (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (0 : W.zero ⟶ Q)
          (cofiberTwo_quotient_weak W i q hi hwi hQ)).property)
        (z, StdSimplex.homeomorphI.symm t) :=
  cofiberPrismRealization_quotient_face W i q hi hwi hQ z t

end CofiberPrismRealization
end CategoryTheory.Waldhausen.Structure

namespace CategoryTheory.Waldhausen.Structure
section WeakObjectCompositionRealization
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

example
    (t : StdSimplex ℝ (Fin 2)) (z : StdSimplex ℝ (Fin 3)) :
    W.weakObjectCompositionRealization f g hf hg (t, z) =
      bisimplexRealization W (W.weakObjectCompositionPrism f g hf hg)
        (W.weakObjectCompositionPrism_isSimplex₂ f g hf hg) (t, z) :=
  weakObjectCompositionRealization_apply W f g hf hg t z

example
    (t z : StdSimplex ℝ (Fin 2)) :
    W.weakObjectCompositionRealization f g hf hg (t, z.map (SimplexCategory.δ 2)) =
      bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex f hf).property) (t, z) :=
  weakObjectCompositionRealization_first W f g hf hg t z

example (e : Fin 2) (z : StdSimplex ℝ (Fin 3)) :
    W.weakObjectCompositionRealization f g hf hg (StdSimplex.single e, z) = W.kBasepoint :=
  weakObjectCompositionRealization_vertex W f g hf hg e z

end WeakObjectCompositionRealization
end CategoryTheory.Waldhausen.Structure

namespace CategoryTheory.Waldhausen.Structure
section WeakObjectIdentitySquare
variable {C : Type u} [Category.{v} C] (W : Structure C) (A : C)

example :
    bisimplexFamily W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property) =
      CartesianMonoidalCategory.fst Δ[1] Δ[1] ≫
        SSet.yonedaEquiv.symm (W.kZeroObjectSimplex A) :=
  weakObjectIdentitySquare_family W A

example (s t : unitInterval) :
    bisimplexRealization W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) =
      W.kZeroObjectLoop A t :=
  weakObjectIdentitySquare_realization W A s t

end WeakObjectIdentitySquare
end CategoryTheory.Waldhausen.Structure

namespace CategoryTheory.Waldhausen.Structure
section WeakObjectSquareTrack
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B : C} (f : A ⟶ B) (hf : W.weq f)

example :
    gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0) ⋙
        (W.weakObjectSimplex f hf).val =
      (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val :=
  weakObjectSquare_initial_grid W f hf

example :
    gridMap₂ (𝟙 ⦋1⦌) (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1) ⋙
        (W.weakObjectSimplex f hf).val =
      (W.weakObjectSimplex (𝟙 B) (W.weq.id_mem B)).val :=
  weakObjectSquare_terminal_grid W f hf

example (t : unitInterval) :
    bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm 0) =
      W.kZeroObjectLoop A t :=
  weakObjectSquare_initial W f hf t

example (t : unitInterval) :
    bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm 1) =
      W.kZeroObjectLoop B t :=
  weakObjectSquare_terminal W f hf t

example (e : Fin 2) (s : unitInterval) :
    bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.single e, StdSimplex.homeomorphI.symm s) = W.kBasepoint :=
  weakObjectSquare_vertex W f hf e s

example (s t : unitInterval) :
    W.weakObjectSquareTrack f hf (s, t) =
      bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) :=
  weakObjectSquareTrack_apply W f hf s t

-- The selected loop-space path is the curry of the entire original square.
example (s t : unitInterval) :
    W.weakObjectSquareLoopPath f hf s t =
      bisimplexRealization W (W.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (W.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) := rfl

example : W.weakObjectSquareLoopPath f hf 0 = W.kZeroObjectLoop A :=
  (W.weakObjectSquareLoopPath f hf).source

example : W.weakObjectSquareLoopPath f hf 1 = W.kZeroObjectLoop B :=
  (W.weakObjectSquareLoopPath f hf).target

-- This is equality of entire loop-space paths, not only their endpoints or classes.
example : W.weakObjectSquareLoopPath (𝟙 A) (W.weq.id_mem A) =
    Path.refl (W.kZeroObjectLoop A) := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  change bisimplexRealization W (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).val
    ((isSimplex₂_diagonal_iff _ _ _).mpr
      (W.weakObjectSimplex (𝟙 A) (W.weq.id_mem A)).property)
    (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) = W.kZeroObjectLoop A t
  exact W.weakObjectIdentitySquare_realization A s t

end WeakObjectSquareTrack
end CategoryTheory.Waldhausen.Structure

namespace CategoryTheory.Waldhausen
section ObjectTransformationSquareRealization
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

include hF0 hG0 in
example (A : C) (s t : unitInterval) :
    weakNaturalTransformationRealizationHomotopy V W hF hG η hη
        (s, V.kZeroObjectLoop A t) =
      bisimplexRealization W (W.weakObjectSimplex (η.app A) (hη A)).val
        ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr
          (W.weakObjectSimplex (η.app A) (hη A)).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s) :=
  objectTransformationRealization_square V W hF hG η hη hF0 hG0 A s t

end ObjectTransformationSquareRealization
end CategoryTheory.Waldhausen

namespace CategoryTheory.Waldhausen
section ObjectTransformationTrack
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))
  (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)

example (A : C) (s t : unitInterval) :
    objectTransformationTrack V W hF hG η hη hF0 hG0 A (s, t) =
      weakNaturalTransformationRealizationHomotopy V W hF hG η hη
        (s, V.kZeroObjectLoop A t) :=
  objectTransformationTrack_apply V W hF hG η hη hF0 hG0 A s t

-- The actual cylinder retains both moving times and strict chosen-zero data.
example (A : C) (s t : unitInterval) :
    objectTransformationTrack V W hF hG η hη hF0 hG0 A (s, t) =
      weakNaturalTransformationRealizationHomotopy V W hF hG η hη
        (s, V.kZeroObjectLoop A t) := rfl

end ObjectTransformationTrack
end CategoryTheory.Waldhausen
