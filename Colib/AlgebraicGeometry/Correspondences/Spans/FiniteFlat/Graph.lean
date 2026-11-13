/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic
public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward

/-!
# Postcomposition of a whole finite flat span by an actual graph

The native incidence Tor pairing with the complete graph equals pushforward
along the actual postcomposed span map. This follows from the already proved
finite-support graph calculation, applied to every generic point with its
true local-ring length. No integral-source replacement is made.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- Composition on the right by the actual graph postcomposes the right span leg. -/
theorem ofFiniteFlatSpan_comp_graph
    {X Y Z : SmoothSite (Spec (.of k))} {A : Scheme.{u}}
    (f : A ⟶ X.left) [IsFinite f] [Flat f]
    (g : A ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom) (a : Y ⟶ Z) :
    ofFiniteFlatSpan f g h ≫ (graphFunctor k).map a =
      ofFiniteFlatSpan f (g ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w, h]) := by
  classical
  let : IsNoetherian A := isNoetherian_of_finiteType_of_isNoetherian f
  let m := pullback.lift f g h
  let n := pullback.lift f (g ≫ a.left)
    (by rw [Category.assoc, MorphismProperty.Over.w, h])
  let : IsFinite m := isFinite_spanMap f g h
  let : IsFinite n := isFinite_spanMap f (g ≫ a.left) _
  have hmn : m ≫ pullback.map X.hom Y.hom X.hom Z.hom
      (𝟙 X.left) a.left (𝟙 _) (by simp)
      (by simp) = n := by
    apply pullback.hom_ext <;> simp [m, n, Category.assoc]
  have ha : ∀ t : genericPoints A, IsFiniteCorrespondencePoint X.hom Y.hom (m t.val) := by
    intro t
    apply isFiniteCorrespondencePoint_finiteMap (X := X.left) (Y := Y.left)
      X.hom Y.hom m t.val
    · simp only [Category.assoc, m, pullback.lift_fst]
      infer_instance
    · simpa only [Category.assoc, m, pullback.lift_fst] using
        finiteFlat_range_integralComponentAt f t.val t.property
  obtain ⟨β, hβ, hcomp⟩ := exists_graph_factorization_of_generic_support_map
    X.hom Y.hom Z.hom a.left (MorphismProperty.Over.w a)
    (finite_genericPoints k (Cor.mk Y)) m n hmn
    (AlgebraicCycle.fundamentalCycle_genericPoints_finite A)
    (fun t => ((Module.length (A.presheaf.stalk t.val)
      (A.presheaf.stalk t.val)).toNat : ℤ)) ha
  have hb : β = ofFiniteFlatSpan f g h := Subtype.ext hβ
  rw [hb] at hcomp
  apply Subtype.ext
  exact hcomp

end AlgebraicGeometry.Cor
