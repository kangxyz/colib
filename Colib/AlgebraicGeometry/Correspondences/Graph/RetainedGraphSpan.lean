/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Isomorphism
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeSupportIsomorphism
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeGraphDivisor

/-!
# The whole retained relative graph span is the existing graph correspondence

The comparison uses the actual whole graph-support isomorphism and both
original coordinate equations. It requires no integral or connected source.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {k : Type u} [Field k] {U W : SmoothSite (Spec (.of k))} {A : Scheme.{u}}

/-- The original support isomorphism identifies both legs with the graph span. -/
theorem ofFiniteFlatSpan_eq_graph_of_iso (a : U ⟶ W) (e : A ≅ U.left)
    (f : A ⟶ U.left) [IsFinite f] [Flat f]
    (g : A ⟶ W.left) (h : f ≫ U.hom = g ≫ W.hom)
    (hf : e.hom = f) (hg : e.hom ≫ a.left = g) :
    ofFiniteFlatSpan f g h = (graphFunctor k).map a := by
  have hid : 𝟙 U.left ≫ U.hom = a.left ≫ W.hom :=
    (Category.id_comp _).trans (MorphismProperty.Over.w a).symm
  exact (ofFiniteFlatSpan_eq_of_iso (X := U) (Y := W) e f g h (𝟙 U.left)
    a.left hid ((Category.comp_id _).trans hf) hg).trans (ofFiniteFlatSpan_id_left a)

variable {S : Scheme.{u}} (q : U.left ⟶ S) (r : W.left ⟶ S) [IsSeparated r]
  (φ : U.left ⟶ W.left) (hφ : φ ≫ r = q)

local notation "I" => relativeGraphIdeal q r φ hφ

/-- The whole relative graph represents the graph of the same smooth-site morphism. -/
theorem ofFiniteFlatSpan_relativeGraph (a : U ⟶ W) (ha : a.left = φ)
    [IsFinite ((I).subschemeι ≫ pullback.fst q r)] [Flat ((I).subschemeι ≫ pullback.fst q r)]
    (h : ((I).subschemeι ≫ pullback.fst q r) ≫ U.hom =
      ((I).subschemeι ≫ pullback.snd q r) ≫ W.hom) :
    ofFiniteFlatSpan ((I).subschemeι ≫ pullback.fst q r)
      ((I).subschemeι ≫ pullback.snd q r) h = (graphFunctor k).map a := by
  apply ofFiniteFlatSpan_eq_graph_of_iso a (relativeGraphSupportIso q r φ hφ)
  · exact relativeGraphSupportIso_hom_base q r φ hφ
  · rw [ha]
    exact relativeGraphSupportIso_hom_target q r φ hφ

section Raw

variable {B M N T : Scheme.{u}} (t : B ⟶ T) (p : M ⟶ B) (s : N ⟶ B)
  [IsNoetherian M] [IsSeparated s] [IsSeparated (s ≫ t)] [LocallyOfFiniteType (s ≫ t)]
  (f : M ⟶ N) (hf : f ≫ s = p)

local notation "J" => relativeGraphIdeal p s f hf

/-- The actual relative graph support has the identity first leg and the specified second leg. -/
theorem ofFiniteFlatSpanRaw_relativeGraph_eq_id_left
    [IsFinite ((J).subschemeι ≫ pullback.fst p s)] [Flat ((J).subschemeι ≫ pullback.fst p s)]
    (h : (𝟙 M) ≫ (p ≫ t) = f ≫ (s ≫ t)) :
    ofFiniteFlatSpanRaw (p ≫ t) (s ≫ t) ((J).subschemeι ≫ pullback.fst p s)
      ((J).subschemeι ≫ pullback.snd p s) (relativeSupport_legs_over_base p s t J) =
      ofFiniteFlatSpanRaw (p ≫ t) (s ≫ t) (𝟙 M) f h := by
  let e := relativeGraphSupportIso p s f hf
  exact ofFiniteFlatSpanRaw_eq_of_iso (p ≫ t) (s ≫ t) e _ _ _ (𝟙 M) f h
    ((Category.comp_id _).trans (relativeGraphSupportIso_hom_base p s f hf))
    (relativeGraphSupportIso_hom_target p s f hf)

end Raw

end AlgebraicGeometry.Cor
