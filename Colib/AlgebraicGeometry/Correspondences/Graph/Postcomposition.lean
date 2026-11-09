/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Composition

/-!
# Actual graph postcomposition as native finite pushforward

For an arbitrary admissible prime, composition with the full right graph is the
native finite pushforward of its original integral support's generic prime along
the literal postcomposed support map. That map is finite because its source
projection is unchanged and the target is separated. The target morphism itself
need not be finite, flat, dominant, or a closed immersion. Its actual residue
field degree is retained; it is not replaced by one.

The surviving graph incidence is the original support by its actual projection
isomorphism. Existing right-graph Tor multiplicity one and native finite
pushforward functoriality identify the actual correspondence with this support
pushforward. All other middle components are empty. Native additive extension
then gives the degree-weighted action on every signed finite correspondence.

The field is arbitrary. Only the middle graph's generic indexing set must be
finite. Ambient schemes may be disconnected or empty. No category, general
associativity, functor, new cycle model, or arbitrary-left-graph law is assumed.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Correspondences/Composition/Support/Graphs.lean`, and
`Correspondences/Exterior/Simplex/GraphInterchangeRight.lean`,
`toIntegralCycle_incidenceTorPairing_componentGraph_right`. The source's custom
fundamental-cycle representation is replaced by the actual native generic prime.
The finite pushforward formula and functoriality are Stacks 02R4 and 02R5.
MVW (2006), Lecture 1, printed pp. 3-4 and p. 6 supplies graph conventions.


-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

section Geometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g) (z : pullback (C := Scheme) f g)

/-- The actual support inclusion followed by postcomposition of its target coordinate. -/
def correspondenceGraphPostcompositionMap :
    (integralComponentAt z).subscheme ⟶ pullback (C := Scheme) f h :=
  (integralComponentAt z).subschemeι ≫
    pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm)

/-- Graph postcomposition preserves the original support's source projection. -/
@[reassoc (attr := simp)]
theorem correspondenceGraphPostcompositionMap_fst :
    correspondenceGraphPostcompositionMap f g h ψ hψ z ≫ pullback.fst f h =
      (integralComponentAt z).subschemeι ≫ pullback.fst f g := by
  simp [correspondenceGraphPostcompositionMap, pullback.map]

/-- The target projection is the original target projection followed by the given morphism. -/
@[reassoc (attr := simp)]
theorem correspondenceGraphPostcompositionMap_snd :
    correspondenceGraphPostcompositionMap f g h ψ hψ z ≫ pullback.snd f h =
      (integralComponentAt z).subschemeι ≫ pullback.snd f g ≫ ψ := by
  simp [correspondenceGraphPostcompositionMap, pullback.map]

/-- The generic prime is sent to the literal postcomposed original point. -/
theorem correspondenceGraphPostcompositionMap_genericPoint :
    correspondenceGraphPostcompositionMap f g h ψ hψ z
        (genericPoint (integralComponentAt z).subscheme) =
      (pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm)) z := by
  have hz' : (integralComponentAt z).subschemeι
      (genericPoint (integralComponentAt z).subscheme) = z :=
    genericPointOf_integralComponentAt z
  change (pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm))
    ((integralComponentAt z).subschemeι (genericPoint (integralComponentAt z).subscheme)) = _
  rw [hz']

/-- The literal support map is finite without any finiteness hypothesis on the target morphism. -/
theorem isFinite_correspondenceGraphPostcompositionMap [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) :
    IsFinite (correspondenceGraphPostcompositionMap f g h ψ hψ z) := by
  have : IsFinite (correspondenceGraphPostcompositionMap f g h ψ hψ z ≫
      pullback.fst f h) := by
    rw [correspondenceGraphPostcompositionMap_fst]
    exact hz.1
  exact IsFinite.of_comp (correspondenceGraphPostcompositionMap f g h ψ hψ z)
    (pullback.fst f h)

/-- The actual generic image is admissible independently of its eventual coefficient.
Native integral-image finiteness and the unchanged source component supply both conditions. -/
theorem isFiniteCorrespondencePoint_graphPostcomposition_genericPoint
    [IsSeparated h] [LocallyOfFiniteType h] (hz : IsFiniteCorrespondencePoint f g z) :
    IsFiniteCorrespondencePoint f h
      (correspondenceGraphPostcompositionMap f g h ψ hψ z
        (genericPoint (integralComponentAt z).subscheme)) := by
  let q := correspondenceGraphPostcompositionMap f g h ψ hψ z
  let A := (integralComponentAt z).subscheme
  let : IsFinite q := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
  let : IsFinite (q ≫ pullback.fst f h) := by
    rw [correspondenceGraphPostcompositionMap_fst]
    exact hz.1
  have hfin : IsFinite (((integralComponentAt (genericPoint A)).subschemeι ≫ q) ≫
      pullback.fst f h) := by
    simpa only [Category.assoc] using
      (inferInstance : IsFinite ((integralComponentAt (genericPoint A)).subschemeι ≫
        (q ≫ pullback.fst f h)))
  refine ⟨finiteCyclePushforward_isFinite_integralComponentAt q
    (pullback.fst f h) (genericPoint A) hfin, ?_⟩
  have hcomp : (q ≫ pullback.fst f h).base ''
      ((integralComponentAt (genericPoint A)).support : Set A) ∈ irreducibleComponents X := by
    rw [coe_support_integralComponentAt, (genericPoint_spec A).def, Set.image_univ]
    simpa only [q, correspondenceGraphPostcompositionMap_fst] using hz.2
  simpa only [finiteCyclePushforward_range_integralComponentAt] using
    finiteCyclePushforward_image_mem_irreducibleComponents q
      (pullback.fst f h) (genericPoint A) hcomp

end Geometry

section Smooth

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)

open Classical in
omit [IsSeparated g] in
/-- The matching actual graph incidence pushes the original support's native generic prime.
The residue degree of the support postcomposition map is not assumed to be one. -/
@[colib_ref "motivic_source_a6805c4"
  "Exterior/Simplex/GraphInterchangeRight.lean: compatible component pushforward"
  "adaptation" "actual right-graph Tor cycle transported by its literal incidence projection",
  stacks 02R5 "finite pushforward functoriality through the actual incidence projection iso"]
theorem incidenceTorCorrespondence_graph_right_val_of_range_subset
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
    (t : genericPoints Y)
    (ht : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆
      closure {t.val}) :
    (incidenceTorCorrespondence f g h z (correspondenceGraphMap g h ψ hψ t.val)
      hz (isFiniteCorrespondencePoint_graphMap g h ψ hψ t)).val =
      letI := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
      finiteCyclePushforward (correspondenceGraphPostcompositionMap f g h ψ hψ z)
        (single (genericPoint (integralComponentAt z).subscheme) 1) := by
  classical
  let w := correspondenceGraphMap g h ψ hψ t.val
  let hw : IsFiniteCorrespondencePoint g h w :=
    isFiniteCorrespondencePoint_graphMap g h ψ hψ t
  let W := correspondenceIncidence f g h z w
  let p : W ⟶ (integralComponentAt z).subscheme := pullback.fst _ _
  let q := correspondenceGraphPostcompositionMap f g h ψ hψ z
  let : IsIso p :=
    isIso_correspondenceIncidence_fst_graphMap_of_range_subset f g h ψ hψ z t.val ht
  let : IsIntegral W := IsIntegral.of_isIso (inv p)
  let : IsFinite q := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
  have hcycle : incidenceTorCycle f g h z w hw = single (genericPoint W) 1 := by
    apply Function.locallyFinsuppWithin.ext
    intro x
    by_cases hx : x ∈ genericPoints W
    · have hx' : x = genericPoint W := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
      rw [← hx', single_apply, ite_eq_left rfl]
      exact (incidenceTorCycle_apply_generic f g h z w hw ⟨x, hx⟩).trans
        (correspondenceIncidenceTorCoefficient_graph_right_eq_one
          k f g h z ψ hψ t ⟨x, hx⟩)
    · have hx' : x ≠ genericPoint W := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
      rw [incidenceTorCycle_apply_of_notMem f g h z w hw x hx, single_apply]
      simp only [hx', ite_false]
  have hmap : correspondenceIncidenceMap f g h z w = p ≫ q :=
    correspondenceIncidenceMap_graphMap_right f g h ψ hψ z t.val
  have hpush (r s : W ⟶ pullback (C := Scheme) f h)
      (hr : IsFinite r) (hs : IsFinite s) (hrs : r = s) :
      @finiteCyclePushforward W (pullback f h) r hr =
        @finiteCyclePushforward W (pullback f h) s hs := by
    cases hrs
    rfl
  rw [incidenceTorCorrespondence_val, hcycle,
    hpush _ _ (isFinite_correspondenceIncidenceMap f g h z w hz hw)
      (inferInstance : IsFinite (p ≫ q)) hmap,
    ← finiteCyclePushforward_comp_apply,
    finiteCyclePushforward_single_of_isClosedImmersion, genericPoint_eq_of_isOpenImmersion p]

omit [Smooth f] [IsSeparated g] in
/-- For an arbitrary admissible prime, exactly its compatible middle graph component survives. -/
theorem incidenceTorPairing_single_graph_right_of_range_subset
    (hY : (genericPoints Y).Finite)
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
    (t : genericPoints Y)
    (ht : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆
      closure {t.val}) :
    incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
      (graphCorrespondenceOfComponents g h ψ hψ hY) =
      incidenceTorCorrespondence f g h z (correspondenceGraphMap g h ψ hψ t.val)
        hz (isFiniteCorrespondencePoint_graphMap g h ψ hψ t) := by
  classical
  let := hY.fintype
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence, map_sum]
  simp only [incidenceTorPairing_single_one]
  apply Finset.sum_eq_single t
  · intro u hu hut
    exact incidenceTorCorrespondence_graph_right_eq_zero_of_ne f g h z hz ψ hψ t u hut.symm ht
  · simp

open Classical in
omit [IsSeparated g] in
/-- Composition of an arbitrary native prime with the full right graph is the actual finite
pushforward on its original support, including every residue-field degree. -/
@[colib_ref "motivic_source_a6805c4"
  "GraphInterchangeRight.lean: toIntegralCycle_incidenceTorPairing_componentGraph_right"
  "adaptation" "native generic-prime finite pushforward with the complete middle graph sum",
  stacks 02R4 "actual residue-degree finite pushforward of the original support prime"]
theorem incidenceTorPairing_single_graph_right_val
    (hY : (genericPoints Y).Finite)
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) :
    (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
      (graphCorrespondenceOfComponents g h ψ hψ hY)).val =
      letI := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
      finiteCyclePushforward (correspondenceGraphPostcompositionMap f g h ψ hψ z)
        (single (genericPoint (integralComponentAt z).subscheme) 1) := by
  obtain ⟨t, ht⟩ := exists_genericPoint_range_correspondenceTarget_subset f g z
  rw [incidenceTorPairing_single_graph_right_of_range_subset f g h ψ hψ hY z hz t ht]
  exact incidenceTorCorrespondence_graph_right_val_of_range_subset f g h ψ hψ z hz t ht

omit [IsSeparated g] in
/-- The subgroup-valued image prime retains the actual support-map residue degree. -/
theorem incidenceTorPairing_single_graph_right_eq_single
    (hY : (genericPoints Y).Finite)
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) :
    incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
      (graphCorrespondenceOfComponents g h ψ hψ hY) =
      singleFiniteCorrespondence f h
        (correspondenceGraphPostcompositionMap f g h ψ hψ z
          (genericPoint (integralComponentAt z).subscheme))
        (isFiniteCorrespondencePoint_graphPostcomposition_genericPoint f g h ψ hψ z hz)
        ((correspondenceGraphPostcompositionMap f g h ψ hψ z).residueDegree
          (genericPoint (integralComponentAt z).subscheme) : ℤ) := by
  let := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
  apply Subtype.ext
  rw [incidenceTorPairing_single_graph_right_val, finiteCyclePushforward_single, one_mul]
  rfl

open Classical in
omit [IsSeparated g] in
/-- On every signed native finite correspondence, right-graph pairing is the additive extension
of the actual support finite pushforwards. No new correspondence model is introduced. -/
theorem incidenceTorPairing_graph_right_val_eq_lift
    (hY : (genericPoints Y).Finite) :
    (finiteCorrespondences f h).subtype.comp
        ((incidenceTorPairing f g h).flip (graphCorrespondenceOfComponents g h ψ hψ hY)) =
      liftFiniteCorrespondence f g (A := AlgebraicCycle (pullback (C := Scheme) f h) ℤ)
        (fun z hz =>
          letI := isFinite_correspondenceGraphPostcompositionMap f g h ψ hψ z hz
          finiteCyclePushforward (correspondenceGraphPostcompositionMap f g h ψ hψ z)
            (single (genericPoint (integralComponentAt z).subscheme) 1)) := by
  apply finiteCorrespondences.addHom_ext_one f g
  intro z hz
  rw [AddMonoidHom.comp_apply, liftFiniteCorrespondence_single, one_smul]
  exact incidenceTorPairing_single_graph_right_val f g h ψ hψ hY z hz

omit [IsSeparated g] in
/-- The same graph action is the degree-weighted additive extension inside the native subgroup.
The generic image's admissibility was proved without a nonzero-coefficient premise. -/
theorem incidenceTorPairing_graph_right_eq_lift
    (hY : (genericPoints Y).Finite) :
    (incidenceTorPairing f g h).flip (graphCorrespondenceOfComponents g h ψ hψ hY) =
      liftFiniteCorrespondence f g (A := finiteCorrespondences f h) (fun z hz =>
        singleFiniteCorrespondence f h
          (correspondenceGraphPostcompositionMap f g h ψ hψ z
            (genericPoint (integralComponentAt z).subscheme))
          (isFiniteCorrespondencePoint_graphPostcomposition_genericPoint f g h ψ hψ z hz)
          ((correspondenceGraphPostcompositionMap f g h ψ hψ z).residueDegree
            (genericPoint (integralComponentAt z).subscheme) : ℤ)) := by
  apply finiteCorrespondences.addHom_ext_one f g
  intro z hz
  rw [liftFiniteCorrespondence_single, one_smul]
  exact incidenceTorPairing_single_graph_right_eq_single f g h ψ hψ hY z hz

end Smooth

end Stacks.Chow
