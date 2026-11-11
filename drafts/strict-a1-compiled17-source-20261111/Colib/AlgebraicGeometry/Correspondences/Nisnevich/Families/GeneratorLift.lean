/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.GeneratorLift
public import Colib.AlgebraicGeometry.Correspondences.Graph.PrecompositionSum
public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.BaseChange.ClosedImageBaseChange

/-!
# Native correspondence lifting through a finite support partition

A finite closed-open cover of the whole support pullback, with a separately
labeled target lift on each piece, gives actual native finite correspondences.
The construction assigns each generic incidence component to a piece containing
its generic point and retains its original signed Tor coefficient and its actual
finite-image residue degree. Colliding image points are added in `AlgebraicCycle`.

Every point of every surviving branch support lifts back to its original piece.
Every surviving integral support also maps to the whole original scheme-theoretic
support pullback, compatibly with graph postcomposition. The support pullback is
not reduced. No target family finiteness, nonempty partition, injective image map,
positivity, or additional graph factorization hypothesis is assumed.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Families/GeneratorLift.lean`,
blob `1afe201f797fe38f8914104ba7ff516de123098c`. The source's custom generators and
`Finsupp` cycles are replaced by native `integralComponentAt`, `AlgebraicCycle`,
`singleFiniteCorrespondence`, and the existing incidence Tor pairing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] isIntegral_integralComponentAt

universe u v

namespace AlgebraicGeometry.Cor

/-- A reduced source factors through an actual closed immersion when its image
lies in the closed image. The target closed subscheme need not be reduced. -/
private theorem exists_lift_to_closed_support
    {D C P : Scheme.{u}} [IsReduced D] (i : C ⟶ P) [IsClosedImmersion i]
    (f : D ⟶ P) (hf : Set.range f ⊆ Set.range i) :
    ∃ r : D ⟶ C, r ≫ i = f := by
  obtain ⟨r, hr⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    i.ker f).2 (by
      rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
      exact hf)
  refine ⟨r ≫ inv i.toImage, ?_⟩
  calc
    (r ≫ inv i.toImage) ≫ i = (r ≫ inv i.toImage) ≫ (i.toImage ≫ i.imageι) :=
      congrArg ((r ≫ inv i.toImage) ≫ ·) i.toImage_imageι.symm
    _ = r ≫ i.imageι := by simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    _ = f := hr

variable (k : Type u) [Field k]
  {X Y U : Scheme.SmoothSite (Spec (.of k))}
  (a : pullback (C := Scheme) X.hom Y.hom)
  (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
  (g : U ⟶ X) {I : Type v} (V : I → Scheme.SmoothSite (Spec (.of k)))
  (q : ∀ i, V i ⟶ Y) (n : ℕ)
  (F : Fin n → (pullback
    ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left).Opens)
  (hFclosed : ∀ j, IsClosed (F j : Set (pullback
    ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left : Scheme)))
  (hFtop : (⨆ j, F j) = ⊤) (label : Fin n → I)
  (b : ∀ j, (F j).toScheme ⟶ (V (label j)).left)
  (hb : ∀ j, b j ≫ (q (label j)).left =
    (F j).ι ≫ pullback.fst
      ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left ≫
        (integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom)

include hFclosed hFtop hb in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_component_graph_family_factorization
    (s : genericPoints U.left) :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (graphFunctor k).map (q (label j))) =
        incidenceTorCorrespondence U.hom X.hom Y.hom
          (correspondenceGraphMap U.hom X.hom g.left (MorphismProperty.Over.w g) s.val) a
          (isFiniteCorrespondencePoint_graphMap U.hom X.hom g.left
            (MorphismProperty.Over.w g) s) ha ∧
      ∀ j B, (β j).val B ≠ 0 →
        (∃ r : (integralComponentAt B).subscheme ⟶ pullback
          ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left,
          r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
            (MorphismProperty.Over.w g) (integralComponentAt a).subschemeι =
          correspondenceGraphPostcompositionMap U.hom (V (label j)).hom Y.hom
            (q (label j)).left (MorphismProperty.Over.w (q (label j))) B) ∧
        ∀ z : (integralComponentAt B).subscheme, ∃ t : (F j).toScheme,
          ((F j).ι ≫ pullback.snd
            ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left) t =
            ((integralComponentAt B).subschemeι ≫ pullback.fst U.hom (V (label j)).hom) z ∧
          b j t = ((integralComponentAt B).subschemeι ≫
            pullback.snd U.hom (V (label j)).hom) z := by
  classical
  let z := correspondenceGraphMap U.hom X.hom g.left (MorphismProperty.Over.w g) s.val
  have hz : IsFiniteCorrespondencePoint U.hom X.hom z :=
    isFiniteCorrespondencePoint_graphMap U.hom X.hom g.left (MorphismProperty.Over.w g) s
  let A := correspondenceIncidence U.hom X.hom Y.hom z a
  let p := (integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom
  let l : A ⟶ U.left := correspondenceIncidenceLeft U.hom X.hom Y.hom z a
  let r : A ⟶ Y.left := correspondenceIncidenceRight U.hom X.hom Y.hom z a
  let j : A ⟶ pullback U.hom Y.hom := correspondenceIncidenceMap U.hom X.hom Y.hom z a
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
  have ht₁ : t ≫ pullback.snd p g.left = l := pullback.lift_snd _ _ _
  have ht₂ : t ≫ pullback.fst p g.left ≫
      (integralComponentAt a).subschemeι ≫ pullback.snd X.hom Y.hom = r := by
    rw [← Category.assoc, pullback.lift_fst]
    rfl
  let i : pullback p g.left ⟶ pullback U.hom Y.hom :=
    ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
      (MorphismProperty.Over.w g) (integralComponentAt a).subschemeι
  have hi : IsClosedImmersion i := by dsimp only [i]; infer_instance
  have htj : t ≫ i = j := by
    apply pullback.hom_ext
    · simpa only [i, Category.assoc, ClosedImageBaseChange.inclusion_fst,
        j, correspondenceIncidenceMap_fst] using ht₁
    · simpa only [i, Category.assoc, ClosedImageBaseChange.inclusion_snd,
        j, correspondenceIncidenceMap_snd] using ht₂
  have hlfin : IsFinite l := isFinite_correspondenceIncidenceLeft U.hom X.hom Y.hom z a hz ha
  have hjfin : IsFinite j := isFinite_correspondenceIncidenceMap U.hom X.hom Y.hom z a hz ha
  let hA := finite_genericPoints_correspondenceIncidence_of_smooth U.hom X.hom Y.hom z a ha
  let := hA.fintype
  let c : genericPoints A → ℤ := correspondenceIncidenceTorCoefficient k U.hom X.hom Y.hom z a
  have hpiece (x : genericPoints A) : ∃ j, t x.val ∈ F j := by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [hFtop]
    trivial
  choose κ hκ using hpiece
  let D (x : genericPoints A) := (integralComponentAt x.val).subscheme
  let d (x : genericPoints A) : D x ⟶ A := (integralComponentAt x.val).subschemeι
  have hRange (x : genericPoints A) :
      Set.range (d x ≫ t) ⊆ Set.range (F (κ x)).ι := by
    rw [Scheme.Opens.range_ι]
    have hs : closure ({x.val} : Set A) ⊆
        t ⁻¹' (F (κ x) : Set (pullback p g.left : Scheme)) :=
      ((hFclosed (κ x)).preimage t.continuous).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hκ x))
    rintro w ⟨w', rfl⟩
    apply hs
    rw [← coe_support_integralComponentAt, ← (integralComponentAt x.val).range_subschemeι]
    exact Set.mem_range_self w'
  let e (x : genericPoints A) : D x ⟶ (F (κ x)).toScheme :=
    IsOpenImmersion.lift (F (κ x)).ι (d x ≫ t) (hRange x)
  have he (x : genericPoints A) : e x ≫ (F (κ x)).ι = d x ≫ t :=
    IsOpenImmersion.lift_fac _ _ _
  have heb (x : genericPoints A) :
      e x ≫ b (κ x) ≫ (q (label (κ x))).left = d x ≫ r := by
    rw [hb, ← Category.assoc, he]
    simpa only [Category.assoc] using congrArg (d x ≫ ·) ht₂
  let m (x : genericPoints A) : D x ⟶ pullback U.hom (V (label (κ x))).hom :=
    pullback.lift (d x ≫ l) (e x ≫ b (κ x)) (by
      calc
        _ = d x ≫ r ≫ Y.hom := by rw [Category.assoc, hbase]
        _ = (e x ≫ b (κ x)) ≫ (V (label (κ x))).hom := by
          rw [← Category.assoc, ← heb]
          simp only [Category.assoc, MorphismProperty.Over.w])
  have hm₁ (x : genericPoints A) :
      m x ≫ pullback.fst U.hom (V (label (κ x))).hom = d x ≫ l :=
    pullback.lift_fst _ _ _
  have hm₂ (x : genericPoints A) :
      m x ≫ pullback.snd U.hom (V (label (κ x))).hom = e x ≫ b (κ x) :=
    pullback.lift_snd _ _ _
  have hmfin₁ (x : genericPoints A) :
      IsFinite (m x ≫ pullback.fst U.hom (V (label (κ x))).hom) := by
    rw [hm₁]
    dsimp only [d]
    infer_instance
  have hmfin (x : genericPoints A) : IsFinite (m x) := by
    have := hmfin₁ x
    exact IsFinite.of_comp (m x) (pullback.fst U.hom (V (label (κ x))).hom)
  let : ∀ x, IsFinite (m x) := hmfin
  let : ∀ x, IsFinite (m x ≫ pullback.fst U.hom (V (label (κ x))).hom) := hmfin₁
  have hcomp (x : genericPoints A) :
      Set.range (m x ≫ pullback.fst U.hom (V (label (κ x))).hom) ∈
        irreducibleComponents U.left := by
    rw [hm₁]
    exact range_integralComponent_correspondenceIncidenceLeft_mem_of_smooth
      U.hom X.hom Y.hom z a hz ha x.val x.property
  have hadm (x : genericPoints A) : IsFiniteCorrespondencePoint
      U.hom (V (label (κ x))).hom (m x (genericPoint (D x))) := by
    apply isFiniteCorrespondencePoint_finiteMap
      U.hom (V (label (κ x))).hom (m x) (genericPoint (D x))
    · rw [Category.assoc]
      infer_instance
    · simp only [Category.assoc, finiteCyclePushforward_range_integralComponentAt,
        coe_support_integralComponentAt, genericPoint_closure, Set.image_univ]
      exact hcomp x
  let P (x : genericPoints A) : pullback U.hom (V (label (κ x))).hom ⟶
      pullback U.hom Y.hom := pullback.map U.hom (V (label (κ x))).hom U.hom Y.hom
        (𝟙 U.left) (q (label (κ x))).left (𝟙 _) (by simp) (by simp)
  have hpost (x : genericPoints A) : m x ≫ P x = d x ≫ j := by
    apply pullback.hom_ext
    · simp only [P, Category.assoc, pullback.map, pullback.lift_fst,
        j, correspondenceIncidenceMap_fst]
      change m x ≫ (pullback.fst U.hom (V (label (κ x))).hom ≫ 𝟙 U.left) = d x ≫ l
      exact (Category.assoc (m x) (pullback.fst U.hom (V (label (κ x))).hom)
        (𝟙 U.left)).symm.trans
        ((Category.comp_id (m x ≫ pullback.fst U.hom (V (label (κ x))).hom)).trans (hm₁ x))
    · simp only [P, Category.assoc, pullback.map, pullback.lift_snd,
        j, correspondenceIncidenceMap_snd]
      rw [← Category.assoc, hm₂, Category.assoc, heb]
  let δ (x : genericPoints A) : Cor.mk U ⟶ Cor.mk (V (label (κ x))) :=
    singleFiniteCorrespondence U.hom (V (label (κ x))).hom (m x (genericPoint (D x)))
      (hadm x) (c x * ((m x).residueDegree (genericPoint (D x)) : ℤ))
  have hδ (x : genericPoints A) :
      (δ x ≫ (graphFunctor k).map (q (label (κ x)))).val =
        finiteCyclePushforward j (single x.val (c x)) := by
    have hdj : IsFinite (d x ≫ j) := by dsimp only [d]; infer_instance
    have h := incidenceTorPairing_finiteImage_single_graph_right_val
      U.hom (V (label (κ x))).hom Y.hom (q (label (κ x))).left
      (MorphismProperty.Over.w (q (label (κ x))))
      (finite_genericPoints k (Cor.mk (V (label (κ x)))))
      (m x) (d x ≫ j) (hpost x) (genericPoint (D x)) (hadm x) (c x)
    change (δ x ≫ (graphFunctor k).map (q (label (κ x)))).val = _ at h
    rw [← finiteCyclePushforward_comp_apply] at h
    have hd : finiteCyclePushforward (d x) (single (genericPoint (D x)) (c x)) =
        single x.val (c x) := by
      have hη : d x (genericPoint (D x)) = x.val := genericPointOf_integralComponentAt x.val
      rw [finiteCyclePushforward_single, hη]
      simp only [d, residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one]
    exact h.trans (congrArg (finiteCyclePushforward j) hd)
  have hδcontrol (x : genericPoints A) (B) (hB : (δ x).val B ≠ 0) :
      (∃ r' : (integralComponentAt B).subscheme ⟶ pullback p g.left,
        r' ≫ i = correspondenceGraphPostcompositionMap U.hom (V (label (κ x))).hom Y.hom
          (q (label (κ x))).left (MorphismProperty.Over.w (q (label (κ x)))) B) ∧
      ∀ z' : (integralComponentAt B).subscheme, ∃ t' : (F (κ x)).toScheme,
        ((F (κ x)).ι ≫ pullback.snd p g.left) t' =
          ((integralComponentAt B).subschemeι ≫ pullback.fst U.hom (V (label (κ x))).hom) z' ∧
        b (κ x) t' = ((integralComponentAt B).subschemeι ≫
          pullback.snd U.hom (V (label (κ x))).hom) z' := by
    have hBeq : B = m x (genericPoint (D x)) := by
      by_contra hne
      change single (m x (genericPoint (D x)))
        (c x * ((m x).residueDegree (genericPoint (D x)) : ℤ)) B ≠ 0 at hB
      simp [single_apply, hne] at hB
    have hpre (z' : (integralComponentAt B).subscheme) :
        ∃ d' : D x, m x d' = (integralComponentAt B).subschemeι z' := by
      have hc : (integralComponentAt B).subschemeι z' ∈ closure ({B} : Set _) := by
        rw [← coe_support_integralComponentAt, ← (integralComponentAt B).range_subschemeι]
        exact Set.mem_range_self z'
      have hmem : B ∈ Set.range (m x) := ⟨genericPoint (D x), hBeq.symm⟩
      exact closure_minimal (Set.singleton_subset_iff.mpr hmem)
        (m x).isClosedMap.isClosed_range hc
    constructor
    · apply exists_lift_to_closed_support i
      rintro w ⟨z', rfl⟩
      obtain ⟨d', hd'⟩ := hpre z'
      refine ⟨t (d x d'), ?_⟩
      have h := congrArg (fun f : D x ⟶ pullback U.hom Y.hom => f d')
        ((hpost x).trans (by rw [← htj]))
      change P x (m x d') = i (t (d x d')) at h
      rw [hd'] at h
      exact h.symm
    · intro z'
      obtain ⟨d', hd'⟩ := hpre z'
      refine ⟨e x d', ?_, ?_⟩
      · have hs : e x ≫ (F (κ x)).ι ≫ pullback.snd p g.left =
            m x ≫ pullback.fst U.hom (V (label (κ x))).hom := by
          rw [← Category.assoc, he, Category.assoc, ht₁, hm₁]
        have h := congrArg (fun f : D x ⟶ U.left => f d') hs
        change ((F (κ x)).ι ≫ pullback.snd p g.left) (e x d') =
          pullback.fst U.hom (V (label (κ x))).hom (m x d') at h
        rwa [hd'] at h
      · have h := congrArg (fun f : D x ⟶ (V (label (κ x))).left => f d') (hm₂ x)
        change pullback.snd U.hom (V (label (κ x))).hom (m x d') = b (κ x) (e x d') at h
        rw [hd'] at h
        exact h.symm
  let ε (j : Fin n) (x : genericPoints A) : Cor.mk U ⟶ Cor.mk (V (label j)) :=
    if h : κ x = j then h ▸ δ x else 0
  have hε (x : genericPoints A) :
      (∑ j, ε j x ≫ (graphFunctor k).map (q (label j))) =
        δ x ≫ (graphFunctor k).map (q (label (κ x))) := by
    rw [Finset.sum_eq_single (κ x)]
    · simp only [ε, dite_true]
    · intro j _ hj
      simp only [ε, dite_eq_right (Ne.symm hj), zero_comp]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  refine ⟨fun j => ∑ x, ε j x, ?_, ?_⟩
  · simp only [Preadditive.sum_comp]
    rw [Finset.sum_comm]
    simp only [hε]
    apply Subtype.ext
    change (finiteCorrespondences U.hom Y.hom).subtype
      (∑ x, δ x ≫ (graphFunctor k).map (q (label (κ x)))) = _
    rw [map_sum, incidenceTorCorrespondence_val, incidenceTorCycle_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact hδ x
  · intro j B hB
    have hval : (∑ x, ε j x).val = ∑ x, (ε j x).val := by
      exact map_sum (finiteCorrespondences U.hom (V (label j)).hom).subtype
        (fun x => ε j x) Finset.univ
    rw [hval] at hB
    have hsum : (∑ x, (ε j x).val B) ≠ 0 := by
      simpa only [coe_sum, Finset.sum_apply] using hB
    obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    by_cases hκ : κ x = j
    · subst j
      simp only [ε, dite_true] at hx
      exact hδcontrol x B hx
    · simp only [ε, dite_eq_right hκ] at hx
      exact (hx rfl).elim

include hFclosed hFtop hb in
/-- A finite closed-open cover of the whole support pullback gives actual native
branches. Every surviving integral support retains both its whole-support map
and a point preimage in its own original piece. The index universe is arbitrary. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Families/GeneratorLift.lean: exists_graph_family_factorization_with_fiber_lift"
  "adaptation" "native signed Tor coefficients, residue degrees, whole support maps and all-point lifts"]
theorem exists_graph_family_factorization_with_fiber_lift :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (graphFunctor k).map (q (label j))) =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 ∧
      ∀ j B, (β j).val B ≠ 0 →
        (∃ r : (integralComponentAt B).subscheme ⟶ pullback
          ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left,
          r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
            (MorphismProperty.Over.w g) (integralComponentAt a).subschemeι =
          correspondenceGraphPostcompositionMap U.hom (V (label j)).hom Y.hom
            (q (label j)).left (MorphismProperty.Over.w (q (label j))) B) ∧
        ∀ z : (integralComponentAt B).subscheme, ∃ t : (F j).toScheme,
          ((F j).ι ≫ pullback.snd
            ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left) t =
            ((integralComponentAt B).subschemeι ≫ pullback.fst U.hom (V (label j)).hom) z ∧
          b j t = ((integralComponentAt B).subschemeι ≫
            pullback.snd U.hom (V (label j)).hom) z := by
  classical
  let := (finite_genericPoints k (Cor.mk U)).fintype
  have h (s : genericPoints U.left) :=
    exists_component_graph_family_factorization k a ha g V q n F hFclosed hFtop label b hb s
  choose β hβ hcontrol using h
  let Γq (j : Fin n) : Cor.mk (V (label j)) ⟶ Cor.mk Y :=
    (graphFunctor k).map (q (label j))
  let Γg : Cor.mk U ⟶ Cor.mk X := (graphFunctor k).map g
  have hβ' (s : genericPoints U.left) :
      (∑ j, β s j ≫ Γq j) = incidenceTorCorrespondence U.hom X.hom Y.hom
        (correspondenceGraphMap U.hom X.hom g.left (MorphismProperty.Over.w g) s.val) a
        (isFiniteCorrespondencePoint_graphMap U.hom X.hom g.left
          (MorphismProperty.Over.w g) s) ha := hβ s
  refine ⟨fun j => ∑ s, β s j, ?_, ?_⟩
  · change (∑ j, (∑ s, β s j) ≫ Γq j) =
      Γg ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1
    simp only [Preadditive.sum_comp]
    rw [Finset.sum_comm]
    simp only [hβ']
    simpa only [one_zsmul] using (graph_comp_single_eq_sum_incidence k g a ha 1).symm
  · intro j B hB
    have hval : (∑ s, β s j).val = ∑ s, (β s j).val := by
      exact map_sum (finiteCorrespondences U.hom (V (label j)).hom).subtype
        (fun s => β s j) Finset.univ
    rw [hval] at hB
    have hsum : (∑ s, (β s j).val B) ≠ 0 := by
      simpa only [coe_sum, Finset.sum_apply] using hB
    obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    exact hcontrol s j B hs

include hFclosed hFtop hb in
/-- The same family construction retains the whole nonreduced support pullback. -/
theorem exists_graph_family_factorization_with_support_lift :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (graphFunctor k).map (q (label j))) =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 ∧
      ∀ j B, (β j).val B ≠ 0 →
        ∃ r : (integralComponentAt B).subscheme ⟶ pullback
          ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left,
          r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
            (MorphismProperty.Over.w g) (integralComponentAt a).subschemeι =
          correspondenceGraphPostcompositionMap U.hom (V (label j)).hom Y.hom
            (q (label j)).left (MorphismProperty.Over.w (q (label j))) B := by
  obtain ⟨β, hβ, hc⟩ := exists_graph_family_factorization_with_fiber_lift
    k a ha g V q n F hFclosed hFtop label b hb
  exact ⟨β, hβ, fun j B hB => (hc j B hB).1⟩

include hFclosed hFtop hb in
/-- Forgetting the retained support data yields the native finite graph-sum equality. -/
theorem exists_graph_family_factorization_of_support_lift :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (graphFunctor k).map (q (label j))) =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 := by
  obtain ⟨β, hβ, _⟩ := exists_graph_family_factorization_with_fiber_lift
    k a ha g V q n F hFclosed hFtop label b hb
  exact ⟨β, hβ⟩

include hFclosed hFtop hb in
/-- Every integer multiple has the same all-point and whole-support control.
Zero and negative multiplicities are allowed; scalar cancellation only removes support. -/
theorem exists_graph_family_factorization_with_fiber_lift_signed (c : ℤ) :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (graphFunctor k).map (q (label j))) =
        (graphFunctor k).map g ≫ singleFiniteCorrespondence X.hom Y.hom a ha c ∧
      ∀ j B, (β j).val B ≠ 0 →
        (∃ r : (integralComponentAt B).subscheme ⟶ pullback
          ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left,
          r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
            (MorphismProperty.Over.w g) (integralComponentAt a).subschemeι =
          correspondenceGraphPostcompositionMap U.hom (V (label j)).hom Y.hom
            (q (label j)).left (MorphismProperty.Over.w (q (label j))) B) ∧
        ∀ z : (integralComponentAt B).subscheme, ∃ t : (F j).toScheme,
          ((F j).ι ≫ pullback.snd
            ((integralComponentAt a).subschemeι ≫ pullback.fst X.hom Y.hom) g.left) t =
            ((integralComponentAt B).subschemeι ≫ pullback.fst U.hom (V (label j)).hom) z ∧
          b j t = ((integralComponentAt B).subschemeι ≫
            pullback.snd U.hom (V (label j)).hom) z := by
  obtain ⟨β, hβ, hc⟩ := exists_graph_family_factorization_with_fiber_lift
    k a ha g V q n F hFclosed hFtop label b hb
  let Γq (j : Fin n) : Cor.mk (V (label j)) ⟶ Cor.mk Y :=
    (graphFunctor k).map (q (label j))
  let Γg : Cor.mk U ⟶ Cor.mk X := (graphFunctor k).map g
  change (∑ j, β j ≫ Γq j) = Γg ≫ singleFiniteCorrespondence X.hom Y.hom a ha 1 at hβ
  refine ⟨fun j => c • β j, ?_, ?_⟩
  · change (∑ j, (c • β j) ≫ Γq j) =
      Γg ≫ singleFiniteCorrespondence X.hom Y.hom a ha c
    rw [singleFiniteCorrespondence_eq_zsmul, Preadditive.comp_zsmul, ← hβ]
    simp only [Preadditive.zsmul_comp, Finset.smul_sum]
  · intro j B hB
    apply hc j B
    intro hz
    apply hB
    change c • (β j).val B = 0
    rw [hz, smul_zero]

end AlgebraicGeometry.Cor
