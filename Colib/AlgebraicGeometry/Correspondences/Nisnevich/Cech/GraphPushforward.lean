/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# Graph pushforward of the original whole-support cycle

A native correspondence whose cycle is the actual finite image of a generic
coefficient cycle keeps that same cycle after graph postcomposition. Only its
literal support map changes. The map equation is proved from the two displayed
scheme projection equations. The existing native graph comparison constructs a
correspondence with the required cycle; subtype injectivity identifies it with
the given correspondence. No graph/cycle comparison is assumed.

The incidence specialization uses the original nonreduced incidence scheme and
its exact signed alternating Tor coefficient function. The target morphism need
not be finite, and collisions retain their separate residue-degree contributions.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Cech/GraphPushforward.lean`.
The explicit finite-generic-set premise replaces the stronger Noetherian premise.
Native `AlgebraicCycle` and the existing `Cor` graph functor are used throughout.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {T X Y V : Scheme.SmoothSite (Spec (.of k))}

/-- Graph postcomposition preserves the entire original signed coefficient cycle
and changes only its actual finite support map, with all original residue degrees. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/GraphPushforward.lean: \
toIntegralCycle_graph_of_generic_coefficients"
  "adaptation" "actual native graph composite of the whole finite generic coefficient cycle"]
theorem comp_graph_val_of_generic_coefficients
    (W : Scheme.{u}) (hW : (genericPoints W).Finite)
    (m : W ⟶ pullback T.hom V.hom) [IsFinite m]
    [IsFinite (m ≫ pullback.fst T.hom V.hom)]
    (hm : ∀ x : genericPoints W,
      Set.range (((integralComponentAt x.val).subschemeι ≫ m) ≫
        pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
    (q : V ⟶ Y) (j : W ⟶ pullback T.hom Y.hom) [IsFinite j]
    (hj₁ : j ≫ pullback.fst T.hom Y.hom = m ≫ pullback.fst T.hom V.hom)
    (hj₂ : j ≫ pullback.snd T.hom Y.hom = m ≫ pullback.snd T.hom V.hom ≫ q.left)
    (c : genericPoints W → ℤ) (α : Cor.mk T ⟶ Cor.mk V)
    (hα : α.val = finiteCyclePushforward m (AlgebraicCycle.ofGenericCoefficients hW c)) :
    (α ≫ (graphFunctor k).map q).val =
      finiteCyclePushforward j (AlgebraicCycle.ofGenericCoefficients hW c) := by
  have hmj : m ≫ pullback.map T.hom V.hom T.hom Y.hom (𝟙 T.left) q.left (𝟙 _)
      (by simp) (by simp) = j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.map, pullback.lift_fst]
      exact (Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans hj₁.symm)
    · simpa only [Category.assoc, pullback.map, pullback.lift_snd] using hj₂.symm
  have hadm (x : genericPoints W) : IsFiniteCorrespondencePoint T.hom V.hom (m x.val) := by
    apply isFiniteCorrespondencePoint_finiteMap T.hom V.hom m x.val
    · rw [Category.assoc]
      infer_instance
    · exact hm x
  obtain ⟨β, hβ, hgraph⟩ := exists_graph_factorization_of_generic_support_map
    T.hom V.hom Y.hom q.left (MorphismProperty.Over.w q)
    (finite_genericPoints k (Cor.mk V)) m j hmj hW c hadm
  have heq : α = β := Subtype.ext (hα.trans hβ.symm)
  rw [heq]
  exact hgraph

/-- Actual incidence Tor composition keeps its original signed Tor cycle after
postcomposition with the full graph. The second support map is literal scheme data. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/GraphPushforward.lean: toIntegralCycle_graph_incidenceTor"
  "adaptation" "the native incidence Tor correspondence with its unchanged coefficient cycle"]
theorem incidenceTorCorrespondence_comp_graph_val
    (a : pullback (C := Scheme) T.hom X.hom) (b : pullback (C := Scheme) X.hom V.hom)
    (ha : IsFiniteCorrespondencePoint T.hom X.hom a)
    (hb : IsFiniteCorrespondencePoint X.hom V.hom b)
    (q : V ⟶ Y)
    (j : correspondenceIncidence T.hom X.hom V.hom a b ⟶ pullback T.hom Y.hom)
    [IsFinite j]
    (hj₁ : j ≫ pullback.fst T.hom Y.hom =
      correspondenceIncidenceLeft T.hom X.hom V.hom a b)
    (hj₂ : j ≫ pullback.snd T.hom Y.hom =
      correspondenceIncidenceRight T.hom X.hom V.hom a b ≫ q.left) :
    ((incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb : Cor.mk T ⟶ Cor.mk V) ≫
      (graphFunctor k).map q).val =
      finiteCyclePushforward j (incidenceTorCycle T.hom X.hom V.hom a b hb) := by
  have : IsFinite (correspondenceIncidenceMap T.hom X.hom V.hom a b) :=
    isFinite_correspondenceIncidenceMap T.hom X.hom V.hom a b ha hb
  have : IsFinite (correspondenceIncidenceLeft T.hom X.hom V.hom a b) :=
    isFinite_correspondenceIncidenceLeft T.hom X.hom V.hom a b ha hb
  have : IsFinite (correspondenceIncidenceMap T.hom X.hom V.hom a b ≫
      pullback.fst T.hom V.hom) := by
    rw [correspondenceIncidenceMap_fst]
    infer_instance
  apply comp_graph_val_of_generic_coefficients k
    (correspondenceIncidence T.hom X.hom V.hom a b)
    (finite_genericPoints_correspondenceIncidence_of_smooth T.hom X.hom V.hom a b hb)
    (correspondenceIncidenceMap T.hom X.hom V.hom a b)
    (fun x => by
      simp only [Category.assoc, correspondenceIncidenceMap_fst]
      exact range_integralComponent_correspondenceIncidenceLeft_mem_of_smooth
          T.hom X.hom V.hom a b ha hb x.val x.property)
    q j
    (by simpa only [correspondenceIncidenceMap_fst] using hj₁)
    (by simpa only [← Category.assoc, correspondenceIncidenceMap_snd] using hj₂)
    (correspondenceIncidenceTorCoefficient k T.hom X.hom V.hom a b)
    (incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb)
  exact incidenceTorCorrespondence_val T.hom X.hom V.hom a b ha hb

end AlgebraicGeometry.Cor
