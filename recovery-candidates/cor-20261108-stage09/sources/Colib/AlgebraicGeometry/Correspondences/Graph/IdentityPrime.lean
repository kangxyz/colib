/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.ActualTorCoefficients
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorCycle
public import Colib.AlgebraicGeometry.Correspondences.Additive
public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Actual identity-component prime correspondences

The matching identity incidence is isomorphic to the original integral support by
its literal incidence projection. Its outer map is therefore a closed immersion.
The actual incidence Tor cycle is proved to be the unique native prime with
coefficient one, using `Graph.ActualTorCoefficients`. The degree-one closed-immersion
pushforward is the original native prime, with the original point and coefficient.
For every other identity component the actual incidence is empty and its actual
Tor correspondence is zero.

No coefficient or comparison is assumed. The component-containment premise is
explicit here and is discharged when the identity is summed over all components.
The ambient factors may be disconnected or empty. The proof does not replace
the full incidence by its reduction, or assume flatness of a finite support.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Units.lean`.
Mathematical context: MVW (2006), Lecture 1, printed p. 4, the diagonal-identity
paragraph, with the disconnected graph convention from Example 1.2, printed p. 3.
The arbitrary-field scope is proved from the native Stacks local calculations;
it is stronger than MVW's published perfect-field convention.
Validation status: isolated uncompiled source; dependent coefficient and Tor-cycle
modules are also uncompiled source candidates. No category unit acceptance is claimed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

universe u

namespace Stacks.Chow

section RightIdentity

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [IsSeparated g]
  (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
  (s : genericPoints Y)

/-- The actual right identity correspondence at the matching component is the original
native prime. Both the Tor multiplicity and the residue degree are proved to be one. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Units.lean"
  "adaptation" "matching right identity component, on actual native prime cycles",
  colib_ref "MVW2006" "Lecture 1, printed p. 4, diagonal-identity paragraph" "specialization"
    "right component unit before the sum over identity components, arbitrary-field extension"]
theorem incidenceTorCorrespondence_identity_right_of_range_subset
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆
      closure {s.val}) :
    incidenceTorCorrespondence f g g z (correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s.val)
      hz (isFiniteCorrespondencePoint_graphMap g g (𝟙 Y) (Category.id_comp g) s) =
      singleFiniteCorrespondence f g z hz 1 := by
  classical
  let δ := correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s.val
  let hδ : IsFiniteCorrespondencePoint g g δ :=
    isFiniteCorrespondencePoint_graphMap g g (𝟙 Y) (Category.id_comp g) s
  let W := correspondenceIncidence f g g z δ
  let p : W ⟶ (integralComponentAt z).subscheme := pullback.fst _ _
  let : IsIso p := isIso_correspondenceIncidence_fst_graphMap_of_range_subset
    f g g (𝟙 Y) (Category.id_comp g) z s.val hs
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let : IsIntegral W := IsIntegral.of_isIso (inv p)
  let : IsClosedImmersion (correspondenceIncidenceMap f g g z δ) := by
    rw [correspondenceIncidenceMap_diagonal_right]
    infer_instance
  have hcycle : incidenceTorCycle f g g z δ hδ = single (genericPoint W) 1 := by
    apply Function.locallyFinsuppWithin.ext
    intro x
    by_cases hx : x ∈ genericPoints W
    · have hx' : x = genericPoint W := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
      rw [← hx', single_apply, if_pos rfl]
      exact (incidenceTorCycle_apply_generic f g g z δ hδ ⟨x, hx⟩).trans
        (correspondenceIncidenceTorCoefficient_identity_right_eq_one k f g z s ⟨x, hx⟩)
    · have hx' : x ≠ genericPoint W := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
      rw [incidenceTorCycle_apply_of_notMem f g g z δ hδ x hx, single_apply]
      simp only [hx', if_false]
  have hpoint : correspondenceIncidenceMap f g g z δ (genericPoint W) = z := by
    rw [correspondenceIncidenceMap_diagonal_right, Scheme.Hom.comp_apply]
    change (integralComponentAt z).subschemeι (p (genericPoint W)) = z
    rw [genericPoint_eq_of_isOpenImmersion p]
    exact genericPointOf_integralComponentAt z
  apply Subtype.ext
  change (incidenceTorCorrespondence f g g z δ hz hδ).val = single z 1
  rw [incidenceTorCorrespondence_val, hcycle,
    finiteCyclePushforward_single_of_isClosedImmersion, hpoint]

/-- Every nonmatching right identity component has zero actual Tor correspondence. -/
theorem incidenceTorCorrespondence_identity_right_eq_zero_of_ne
    (s' : genericPoints Y) (hss' : s ≠ s')
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆
      closure {s.val}) :
    incidenceTorCorrespondence f g g z
      (correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s'.val)
      hz (isFiniteCorrespondencePoint_graphMap g g (𝟙 Y) (Category.id_comp g) s') = 0 := by
  let := isEmpty_genericPoints_correspondenceIncidence_identity_right_of_ne
    k f g z s s' hss' hs
  apply incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty
  exact Set.eq_empty_iff_forall_notMem.mpr fun t ht => isEmptyElim (⟨t, ht⟩ : genericPoints _)

end RightIdentity

section LeftIdentity

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [Smooth f] [IsSeparated f] [Smooth g] [IsSeparated g]
  (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
  (s : genericPoints X)

/-- The actual left identity correspondence at the matching component is the original
native prime, including the actual degree-one finite pushforward. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Units.lean"
  "adaptation" "matching left identity component, original Tor order, actual finite pushforward",
  colib_ref "MVW2006" "Lecture 1, printed p. 4, diagonal-identity paragraph" "specialization"
    "left component unit before summing identity components, without integral ambient assumptions"]
theorem incidenceTorCorrespondence_identity_left_of_range_subset
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆
      closure {s.val}) :
    incidenceTorCorrespondence f f g (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z
      (isFiniteCorrespondencePoint_graphMap f f (𝟙 X) (Category.id_comp f) s) hz =
      singleFiniteCorrespondence f g z hz 1 := by
  classical
  let δ := correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val
  let hδ : IsFiniteCorrespondencePoint f f δ :=
    isFiniteCorrespondencePoint_graphMap f f (𝟙 X) (Category.id_comp f) s
  let W := correspondenceIncidence f f g δ z
  let p : W ⟶ (integralComponentAt z).subscheme := pullback.snd _ _
  let : IsIso p := isIso_correspondenceIncidence_snd_diagonal_of_range_subset f g s.val z hs
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let : IsIntegral W := IsIntegral.of_isIso (inv p)
  let : IsClosedImmersion (correspondenceIncidenceMap f f g δ z) := by
    rw [correspondenceIncidenceMap_diagonal_left]
    infer_instance
  have hcycle : incidenceTorCycle f f g δ z hz = single (genericPoint W) 1 := by
    apply Function.locallyFinsuppWithin.ext
    intro x
    by_cases hx : x ∈ genericPoints W
    · have hx' : x = genericPoint W := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
      rw [← hx', single_apply, if_pos rfl]
      exact (incidenceTorCycle_apply_generic f f g δ z hz ⟨x, hx⟩).trans
        (correspondenceIncidenceTorCoefficient_identity_left_eq_one k f g z s ⟨x, hx⟩)
    · have hx' : x ≠ genericPoint W := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hx
      rw [incidenceTorCycle_apply_of_notMem f f g δ z hz x hx, single_apply]
      simp only [hx', if_false]
  have hpoint : correspondenceIncidenceMap f f g δ z (genericPoint W) = z := by
    rw [correspondenceIncidenceMap_diagonal_left, Scheme.Hom.comp_apply]
    change (integralComponentAt z).subschemeι (p (genericPoint W)) = z
    rw [genericPoint_eq_of_isOpenImmersion p]
    exact genericPointOf_integralComponentAt z
  apply Subtype.ext
  change (incidenceTorCorrespondence f f g δ z hδ hz).val = single z 1
  rw [incidenceTorCorrespondence_val, hcycle,
    finiteCyclePushforward_single_of_isClosedImmersion, hpoint]

/-- Every nonmatching left identity component has zero actual Tor correspondence. -/
theorem incidenceTorCorrespondence_identity_left_eq_zero_of_ne
    (s' : genericPoints X) (hss' : s ≠ s')
    (hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆
      closure {s.val}) :
    incidenceTorCorrespondence f f g
      (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s'.val) z
      (isFiniteCorrespondencePoint_graphMap f f (𝟙 X) (Category.id_comp f) s') hz = 0 := by
  let := isEmpty_genericPoints_correspondenceIncidence_identity_left_of_ne
    k f g z s s' hss' hs
  apply incidenceTorCorrespondence_eq_zero_of_genericPoints_eq_empty
  exact Set.eq_empty_iff_forall_notMem.mpr fun t ht => isEmptyElim (⟨t, ht⟩ : genericPoints _)

end LeftIdentity

end Stacks.Chow
