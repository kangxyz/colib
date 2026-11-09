/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# Genuine correspondence factorization from a whole support lift

A literal map from the entire scheme-theoretic pullback of an admissible integral
support to the lifted target yields a factorization in the existing native `Cor`.
For each source graph component, the actual incidence scheme maps into that
whole pullback. Its unchanged alternating Tor cycle is pushed along the resulting
finite map into the lifted target product. The finite-image comparison retains
all signed Tor coefficients and actual residue degrees, including colliding images.

Neither the support pullback nor the incidence scheme is replaced by its
reduction. No flatness of the support map, Nisnevich cover, local factorization,
or residue-field splitting is assumed. Those geometric constructions can supply
`b` and its displayed equation to this theorem. Empty and disconnected schemes
and arbitrary base fields are allowed.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/GeneratorLift.lean`,
`exists_component_graph_factorization` and
`exists_graph_factorization_of_support_lift`. Native Mathlib algebraic cycles,
Stacks integral components and the completed native incidence pairing replace
the original custom `IntegralCycle` and generator `Finsupp` models.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] isIntegral_integralComponentAt

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y U V : Scheme.SmoothSite (Spec (.of k))}
  (a : pullback (C := Scheme) X.hom Y.hom) (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
  (g : U ⟶ X) (q : V ⟶ Y)
  (b : pullback ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom)
      g.left ⟶ V.left)
  (hb : b ≫ q.left = pullback.fst
    ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left ≫
      (integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom)

include b hb in
private theorem exists_component_graph_factorization_of_support_lift
    (s : genericPoints U.left) :
    ∃ β : finiteCorrespondences U.hom V.hom,
      incidenceTorPairing U.hom V.hom Y.hom β
        (graphCorrespondenceOfComponents V.hom Y.hom q.left
          (MorphismProperty.Over.w q) (finite_genericPoints k (Cor.mk V))) =
      incidenceTorCorrespondence U.hom X.hom Y.hom
        (correspondenceGraphMap U.hom X.hom g.left (MorphismProperty.Over.w g) s.val) a
        (isFiniteCorrespondencePoint_graphMap U.hom X.hom g.left
          (MorphismProperty.Over.w g) s) ha := by
  classical
  let z := correspondenceGraphMap U.hom X.hom g.left (MorphismProperty.Over.w g) s.val
  have hz : IsFiniteCorrespondencePoint U.hom X.hom z :=
    isFiniteCorrespondencePoint_graphMap U.hom X.hom g.left (MorphismProperty.Over.w g) s
  let A := correspondenceIncidence U.hom X.hom Y.hom z a
  let p := (integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom
  let l : A ⟶ U.left := correspondenceIncidenceLeft U.hom X.hom Y.hom z a
  let r : A ⟶ Y.left := correspondenceIncidenceRight U.hom X.hom Y.hom z a
  have hbase : l ≫ U.hom = r ≫ Y.hom :=
    correspondenceIncidence_condition U.hom X.hom Y.hom z a
  have hleft : pullback.snd
      ((integralComponentAt z).subschemeι ≫ pullback.snd U.hom X.hom) p ≫ p =
      l ≫ g.left := by
    calc
      _ = pullback.fst
          ((integralComponentAt z).subschemeι ≫ pullback.snd U.hom X.hom) p ≫
            (integralComponentAt z).subschemeι ≫ pullback.snd U.hom X.hom :=
        (pullback.condition (f := (integralComponentAt z).subschemeι ≫
          pullback.snd U.hom X.hom) (g := p)).symm
      _ = l ≫ g.left := by
        have he := congrArg
          (fun f => pullback.fst
            ((integralComponentAt z).subschemeι ≫ pullback.snd U.hom X.hom) p ≫ f)
          (integralComponentAt_graphMap_snd U.hom X.hom g.left
            (MorphismProperty.Over.w g) s.val)
        simpa only [l, correspondenceIncidenceLeft, Category.assoc] using he
  let t : A ⟶ pullback p g.left := pullback.lift (pullback.snd _ _) l hleft
  have ht : t ≫ b ≫ q.left = r := by
    rw [hb, ← Category.assoc, pullback.lift_fst]
    rfl
  let m : A ⟶ pullback U.hom V.hom := pullback.lift l (t ≫ b) (by
    calc
      l ≫ U.hom = r ≫ Y.hom := hbase
      _ = (t ≫ b) ≫ V.hom := by rw [← ht]; simp only [Category.assoc,
        MorphismProperty.Over.w])
  have hm₁ : m ≫ pullback.fst U.hom V.hom = l := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd U.hom V.hom ≫ q.left = r := by
    rw [← Category.assoc, show m ≫ pullback.snd U.hom V.hom = t ≫ b from
      pullback.lift_snd _ _ _, Category.assoc, ht]
  let j : A ⟶ pullback U.hom Y.hom := correspondenceIncidenceMap U.hom X.hom Y.hom z a
  have : IsFinite l := isFinite_correspondenceIncidenceLeft U.hom X.hom Y.hom z a hz ha
  have : IsFinite (m ≫ pullback.fst U.hom V.hom) := by rw [hm₁]; infer_instance
  have : IsFinite m := IsFinite.of_comp m (pullback.fst U.hom V.hom)
  have : IsFinite j := isFinite_correspondenceIncidenceMap U.hom X.hom Y.hom z a hz ha
  have hmj : m ≫ pullback.map U.hom V.hom U.hom Y.hom (𝟙 U.left) q.left (𝟙 _)
      (by simp) (by simp) = j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.map, pullback.lift_fst,
        j, correspondenceIncidenceMap_fst]
      change m ≫ (pullback.fst U.hom V.hom ≫ 𝟙 U.left) = l
      exact (Category.assoc m (pullback.fst U.hom V.hom) (𝟙 U.left)).symm.trans
        ((Category.comp_id (m ≫ pullback.fst U.hom V.hom)).trans hm₁)
    · simpa only [Category.assoc, pullback.map, pullback.lift_snd,
        j, correspondenceIncidenceMap_snd] using hm₂
  have hadm (x : genericPoints A) : IsFiniteCorrespondencePoint U.hom V.hom (m x.val) := by
    apply isFiniteCorrespondencePoint_finiteMap U.hom V.hom m x.val
    · have hfin : IsFinite ((integralComponentAt x.val).subschemeι ≫ l) := inferInstance
      simpa only [Category.assoc, hm₁] using hfin
    · have hcomp := range_integralComponent_correspondenceIncidenceLeft_mem_of_smooth
        U.hom X.hom Y.hom z a hz ha x.val x.property
      simpa only [Category.assoc, hm₁] using hcomp
  obtain ⟨β, _, hβ⟩ := exists_graph_factorization_of_generic_support_map
    U.hom V.hom Y.hom q.left (MorphismProperty.Over.w q)
    (finite_genericPoints k (Cor.mk V)) m j hmj
    (finite_genericPoints_correspondenceIncidence_of_smooth U.hom X.hom Y.hom z a ha)
    (correspondenceIncidenceTorCoefficient k U.hom X.hom Y.hom z a) hadm
  refine ⟨β, ?_⟩
  apply Subtype.ext
  exact hβ

include b hb in
/-- A map from the entire scheme-theoretic support pullback gives a genuine
factorization of the restricted prime correspondence through the actual target graph. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/GeneratorLift.lean: exists_graph_factorization_of_support_lift"
  "adaptation" "whole nonreduced support pullback, native Tor cycles and actual residue degrees"]
theorem exists_graph_factorization_of_support_lift :
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 := by
  classical
  let := (finite_genericPoints k (Cor.mk U)).fintype
  have h (s : genericPoints U.left) :=
    exists_component_graph_factorization_of_support_lift k a ha g q b hb s
  choose β hβ using h
  refine ⟨∑ s : genericPoints U.left, β s, ?_⟩
  change (incidenceTorPairing U.hom V.hom Y.hom).flip
    (graphCorrespondenceOfComponents V.hom Y.hom q.left (MorphismProperty.Over.w q)
      (finite_genericPoints k (Cor.mk V))) (∑ s : genericPoints U.left, β s) =
      (incidenceTorPairing U.hom X.hom Y.hom).flip
        (singleFiniteCorrespondence X.hom Y.hom a ha 1)
        (graphCorrespondenceOfComponents U.hom X.hom g.left (MorphismProperty.Over.w g)
          (finite_genericPoints k (Cor.mk U)))
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence U.hom X.hom
    g.left (MorphismProperty.Over.w g) (finite_genericPoints k (Cor.mk U)), map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact (hβ s).trans (incidenceTorPairing_single_one U.hom X.hom Y.hom _ a _ ha).symm

include b hb in
/-- The same whole-support lift factors every signed multiple of the native prime. -/
theorem exists_graph_factorization_of_support_lift_signed (n : ℤ) :
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha n := by
  obtain ⟨β, hβ⟩ := exists_graph_factorization_of_support_lift k a ha g q b hb
  let γ : Cor.mk U ⟶ Cor.mk X := (graphFunctor k).map g
  let δ : Cor.mk V ⟶ Cor.mk Y := (graphFunctor k).map q
  change β ≫ δ = γ ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 at hβ
  refine ⟨n • β, ?_⟩
  change (n • β) ≫ δ = γ ≫ singleFiniteCorrespondence X.hom Y.hom a ha n
  rw [singleFiniteCorrespondence_eq_zsmul, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, hβ]

/-- A native prime support contained in an open target image factors through the actual graph.
The open-immersion lift is applied to the whole integral support scheme. -/
theorem exists_graph_factorization_of_range_subset
    {W V Y : Scheme.SmoothSite (Spec (.of k))}
    (a : pullback (C := Scheme) W.hom Y.hom) (ha : IsFiniteCorrespondencePoint W.hom Y.hom a)
    (q : V ⟶ Y) [IsOpenImmersion q.left]
    (hA : Set.range ((integralComponentAt a).subschemeι ≫ pullback.snd W.hom Y.hom) ⊆
      Set.range q.left) :
    ∃ β : Cor.mk W ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q = singleFiniteCorrespondence W.hom Y.hom a ha 1 := by
  let r := (integralComponentAt a).subschemeι ≫ pullback.snd W.hom Y.hom
  let b : (integralComponentAt a).subscheme ⟶ V.left := IsOpenImmersion.lift q.left r hA
  have hb : b ≫ q.left = r := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨β, hβ⟩ := exists_graph_factorization_of_support_lift k a ha (𝟙 W) q
    (pullback.fst ((integralComponentAt a).subschemeι ≫ pullback.fst W.hom Y.hom)
      (𝟙 W : W ⟶ W).left ≫ b)
    (by
      change (pullback.fst ((integralComponentAt a).subschemeι ≫ pullback.fst W.hom Y.hom)
        (𝟙 W : W ⟶ W).left ≫ b) ≫ q.left =
          pullback.fst ((integralComponentAt a).subschemeι ≫ pullback.fst W.hom Y.hom)
            (𝟙 W : W ⟶ W).left ≫ r
      exact (Category.assoc _ _ _).trans (congrArg
        (fun f => pullback.fst
          ((integralComponentAt a).subschemeι ≫ pullback.fst W.hom Y.hom)
            (𝟙 W : W ⟶ W).left ≫ f) hb))
  let δ : Cor.mk V ⟶ Cor.mk Y := (graphFunctor k).map q
  let ε : Cor.mk W ⟶ Cor.mk W := (graphFunctor k).map (𝟙 W)
  have hε : ε = 𝟙 (Cor.mk W) := (graphFunctor k).map_id W
  change β ≫ δ = ε ≫ singleFiniteCorrespondence W.hom Y.hom a ha 1 at hβ
  rw [hε, Category.id_comp] at hβ
  exact ⟨β, hβ⟩

end AlgebraicGeometry.Cor
