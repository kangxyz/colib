/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.IdentitySum

/-!
# Composition of actual native component graph correspondences

For each source component, the unique compatible middle graph component gives an
incidence isomorphic to the original graph support. Its outer map is the actual
composite graph closed immersion. The existing right-graph Tor theorem gives
multiplicity one, and native degree-one finite pushforward gives the composite
prime. All incompatible middle components have empty incidence. Two finite graph
sums then give compatibility of the actual Tor pairing with graph composition.

The field is arbitrary. Smooth schemes may be disconnected or empty. Only the
source and middle graph indexing sets must be finite; no target finiteness,
connectedness, ambient integrality, perfectness or morphism flatness is assumed.
The compact specialization obtains these finite sets from smoothness. The result
is an identity of native finite correspondences, independent of associativity.
No Cor category or graph functor is constructed here.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Graph/Components/Composition.lean`,
blob `ec013b96ad67a30e61e6aa029915fb591a5f146c`. This is a new proof on the native
Stacks cycle subgroup, not a copy of its generator/Finsupp model. MVW (2006),
Lecture 1, Example 1.2, printed p. 3, composition on p. 4 and the graph-functor
paragraph on p. 6 supply the graph conventions. The actual local Tor and residue
degree calculations are the native inputs proved in the imported modules.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

section Geometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (φ : X ⟶ Y) (hφ : φ ≫ g = f) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)

/-- Postcomposing the actual source-first graph gives the graph of the composite. -/
theorem correspondenceGraphMap_postcomposition :
    correspondenceGraphMap f g φ hφ ≫
        pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm) =
      correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst,
      correspondenceGraphMap_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.map, pullback.lift_snd,
      correspondenceGraphMap_snd, correspondenceGraphMap_snd_assoc]

/-- The first graph support's induced outer map factors through the actual composite graph. -/
theorem integralComponentAt_graphMap_postcomposition [IsSeparated g] (s : X) :
    (integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
        pullback.map f g f h (𝟙 X) ψ (𝟙 S) (by simp) (by simpa using hψ.symm) =
      (integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
        pullback.fst f g ≫
          correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst,
      correspondenceGraphMap_fst, Category.comp_id]
  · simp only [Category.assoc, pullback.map, pullback.lift_snd,
      correspondenceGraphMap_snd]
    exact integralComponentAt_graphMap_snd_assoc f g φ hφ s ψ

/-- The actual two-graph incidence outer map is the composite graph after its source projection. -/
theorem correspondenceIncidenceMap_graphMap_comp [IsSeparated g] [IsSeparated h]
    (s : X) (t : Y) :
    correspondenceIncidenceMap f g h (correspondenceGraphMap f g φ hφ s)
        (correspondenceGraphMap g h ψ hψ t) =
      pullback.fst _ _ ≫
        (integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
          pullback.fst f g ≫
            correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) := by
  rw [correspondenceIncidenceMap_graphMap_right f g h ψ hψ
      (correspondenceGraphMap f g φ hφ s) t,
    integralComponentAt_graphMap_postcomposition f g h φ hφ ψ hψ s]

/-- On a compatible middle component, the actual outer map is a closed immersion.
This proves residue-field degree one without assuming any pushforward comparison. -/
theorem isClosedImmersion_correspondenceIncidenceMap_graphMap_comp_of_range_subset
    [IsSeparated g] [IsSeparated h] (s : X) (t : Y)
    (hs : Set.range
      ((integralComponentAt (correspondenceGraphMap f g φ hφ s)).subschemeι ≫
        pullback.snd f g) ⊆ closure {t}) :
    IsClosedImmersion (correspondenceIncidenceMap f g h
      (correspondenceGraphMap f g φ hφ s) (correspondenceGraphMap g h ψ hψ t)) := by
  let z := correspondenceGraphMap f g φ hφ s
  let w := correspondenceGraphMap g h ψ hψ t
  let p : correspondenceIncidence f g h z w ⟶ (integralComponentAt z).subscheme :=
    pullback.fst _ _
  let : IsIso p :=
    isIso_correspondenceIncidence_fst_graphMap_of_range_subset f g h ψ hψ z t hs
  let : IsClosedImmersion ((integralComponentAt z).subschemeι ≫ pullback.fst f g) :=
    isClosedImmersion_integralComponentAt_graphMap_fst f g φ hφ s
  let : IsClosedImmersion
      (correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ])) :=
    isClosedImmersion_correspondenceGraphMap f h (φ ≫ ψ) _
  rw [correspondenceIncidenceMap_graphMap_comp]
  simpa only [Category.assoc] using
    (inferInstance : IsClosedImmersion (p ≫
      ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ≫
        correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ])))

end Geometry

section Smooth

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]

omit [Smooth f] [IsSeparated g] in
/-- A nonmatching right graph component contributes zero to the actual Tor correspondence. -/
theorem incidenceTorCorrespondence_graph_right_eq_zero_of_ne
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
    (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g) (s t : genericPoints Y) (hst : s ≠ t)
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆
      closure {s.val}) :
    incidenceTorCorrespondence f g h z (correspondenceGraphMap g h ψ hψ t.val)
      hz (isFiniteCorrespondencePoint_graphMap g h ψ hψ t) = 0 := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : IsNormal Y := isNormal_of_isRegular Y (isRegular_of_smooth_over_field g)
  let := isEmpty_correspondenceIncidence_graphMap_of_ne f g h ψ hψ z s t hst hs
  apply incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty
  exact Set.eq_empty_iff_forall_notMem.mpr fun t ht => isEmptyElim (⟨t, ht⟩ : genericPoints _)

variable (φ : X ⟶ Y) (hφ : φ ≫ g = f) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)

/-- A surviving pair of actual graph components gives the composite graph prime.
Both its Tor coefficient and residue-field degree are proved to be one. -/
@[colib_ref "motivic_source_a6805c4"
  "Graph/Components/Composition.lean: incidenceTorCorrespondence_componentGraph_comp"
  "adaptation" "actual component graph composition in the native finite-cycle subgroup",
  colib_ref "MVW2006" "Lecture 1, printed pp. 3-4, graph sum and composition"
  "background" "component graph calculation with native Tor and residue-degree multiplicities"]
theorem incidenceTorCorrespondence_graphMap_comp_of_range_subset
    (s : genericPoints X) (t : genericPoints Y)
    (hs : Set.range
      ((integralComponentAt (correspondenceGraphMap f g φ hφ s.val)).subschemeι ≫
        pullback.snd f g) ⊆ closure {t.val}) :
    incidenceTorCorrespondence f g h (correspondenceGraphMap f g φ hφ s.val)
      (correspondenceGraphMap g h ψ hψ t.val)
      (isFiniteCorrespondencePoint_graphMap f g φ hφ s)
      (isFiniteCorrespondencePoint_graphMap g h ψ hψ t) =
      singleFiniteCorrespondence f h
        (correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) s.val)
        (isFiniteCorrespondencePoint_graphMap f h (φ ≫ ψ)
          (by rw [Category.assoc, hψ, hφ]) s) 1 := by
  classical
  let z := correspondenceGraphMap f g φ hφ s.val
  let w := correspondenceGraphMap g h ψ hψ t.val
  let hz : IsFiniteCorrespondencePoint f g z :=
    isFiniteCorrespondencePoint_graphMap f g φ hφ s
  let hw : IsFiniteCorrespondencePoint g h w :=
    isFiniteCorrespondencePoint_graphMap g h ψ hψ t
  let W := correspondenceIncidence f g h z w
  let p : W ⟶ (integralComponentAt z).subscheme := pullback.fst _ _
  let : IsIso p :=
    isIso_correspondenceIncidence_fst_graphMap_of_range_subset f g h ψ hψ z t.val hs
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let : IsIntegral W := IsIntegral.of_isIso (inv p)
  let : IsClosedImmersion (correspondenceIncidenceMap f g h z w) :=
    isClosedImmersion_correspondenceIncidenceMap_graphMap_comp_of_range_subset
      f g h φ hφ ψ hψ s.val t.val hs
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
  have hpoint : correspondenceIncidenceMap f g h z w (genericPoint W) =
      correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) s.val := by
    rw [correspondenceIncidenceMap_graphMap_right f g h ψ hψ z t.val]
    change (pullback.map f g f h (𝟙 X) ψ (𝟙 _) (by simp) (by simpa using hψ.symm))
      ((integralComponentAt z).subschemeι (p (genericPoint W))) = _
    rw [genericPoint_eq_of_isOpenImmersion p]
    have hz' : (integralComponentAt z).subschemeι
        (genericPoint (integralComponentAt z).subscheme) = z :=
      genericPointOf_integralComponentAt z
    rw [hz']
    exact congrArg (fun q : X ⟶ pullback (C := Scheme) f h => q s.val)
      (correspondenceGraphMap_postcomposition f g h φ hφ ψ hψ)
  apply Subtype.ext
  change (incidenceTorCorrespondence f g h z w hz hw).val =
    single (correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) s.val) 1
  rw [incidenceTorCorrespondence_val, hcycle,
    finiteCyclePushforward_single_of_isClosedImmersion, hpoint]

/-- Pairing one graph prime with the full second graph keeps exactly its composite graph prime. -/
theorem incidenceTorPairing_single_graph_comp (hY : (genericPoints Y).Finite)
    (s : genericPoints X) :
    incidenceTorPairing f g h
      (singleFiniteCorrespondence f g (correspondenceGraphMap f g φ hφ s.val)
        (isFiniteCorrespondencePoint_graphMap f g φ hφ s) 1)
      (graphCorrespondenceOfComponents g h ψ hψ hY) =
      singleFiniteCorrespondence f h
        (correspondenceGraphMap f h (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) s.val)
        (isFiniteCorrespondencePoint_graphMap f h (φ ≫ ψ)
          (by rw [Category.assoc, hψ, hφ]) s) 1 := by
  classical
  let := hY.fintype
  obtain ⟨t, ht⟩ := exists_genericPoint_range_correspondenceTarget_subset
    f g (correspondenceGraphMap f g φ hφ s.val)
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence, map_sum]
  simp only [incidenceTorPairing_single_one]
  rw [Finset.sum_eq_single t]
  · exact incidenceTorCorrespondence_graphMap_comp_of_range_subset f g h φ hφ ψ hψ s t ht
  · intro u hu hut
    exact incidenceTorCorrespondence_graph_right_eq_zero_of_ne f g h
      (correspondenceGraphMap f g φ hφ s.val)
      (isFiniteCorrespondencePoint_graphMap f g φ hφ s) ψ hψ t u hut.symm ht
  · simp

/-- Actual graph correspondences compose under the actual Tor pairing.
Only the source and middle generic sets need be finite, and the field is arbitrary. -/
@[colib_ref "motivic_source_a6805c4"
  "Graph/Components/Composition.lean: incidenceTorPairing_componentGraph_comp"
  "adaptation" "complete native graph sums, allowing disconnected and empty smooth schemes",
  colib_ref "MVW2006" "Lecture 1, printed p. 6, graph functor paragraph"
  "adaptation" "graph composition as an identity of actual finite correspondences"]
theorem incidenceTorPairing_graph_comp
    (hX : (genericPoints X).Finite) (hY : (genericPoints Y).Finite) :
    incidenceTorPairing f g h
      (graphCorrespondenceOfComponents f g φ hφ hX)
      (graphCorrespondenceOfComponents g h ψ hψ hY) =
      graphCorrespondenceOfComponents f h (φ ≫ ψ)
        (by rw [Category.assoc, hψ, hφ]) hX := by
  classical
  let := hX.fintype
  change (incidenceTorPairing f g h).flip (graphCorrespondenceOfComponents g h ψ hψ hY)
    (graphCorrespondenceOfComponents f g φ hφ hX) = _
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence f g φ hφ hX,
    graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence f h (φ ≫ ψ)
      (by rw [Category.assoc, hψ, hφ]) hX, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact incidenceTorPairing_single_graph_comp f g h φ hφ ψ hψ hY s

/-- Signed multiples of the two graph cycles retain the product of their integer coefficients. -/
theorem incidenceTorPairing_zsmul_graph_comp
    (hX : (genericPoints X).Finite) (hY : (genericPoints Y).Finite) (a b : ℤ) :
    incidenceTorPairing f g h
      (a • graphCorrespondenceOfComponents f g φ hφ hX)
      (b • graphCorrespondenceOfComponents g h ψ hψ hY) =
      (a * b) • graphCorrespondenceOfComponents f h (φ ≫ ψ)
        (by rw [Category.assoc, hψ, hφ]) hX := by
  rw [incidenceTorPairing_zsmul_left, incidenceTorPairing_zsmul_right,
    incidenceTorPairing_graph_comp, smul_smul]

/-- Compact smooth source and middle schemes supply finite graph support natively. -/
theorem incidenceTorPairing_graph_comp_of_compact [CompactSpace X] [CompactSpace Y] :
    incidenceTorPairing f g h
      (graphCorrespondenceOfComponents f g φ hφ (finite_genericPoints_of_smooth_of_compact f))
      (graphCorrespondenceOfComponents g h ψ hψ (finite_genericPoints_of_smooth_of_compact g)) =
      graphCorrespondenceOfComponents f h (φ ≫ ψ)
        (by rw [Category.assoc, hψ, hφ]) (finite_genericPoints_of_smooth_of_compact f) :=
  incidenceTorPairing_graph_comp f g h φ hφ ψ hψ
    (finite_genericPoints_of_smooth_of_compact f) (finite_genericPoints_of_smooth_of_compact g)

end Smooth

end Stacks.Chow
