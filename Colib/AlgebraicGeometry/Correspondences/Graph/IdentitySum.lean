/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Correspondences.Graph.IdentityPrime
public import Colib.AlgebraicGeometry.Correspondences.Composition.Pairing

/-!
# Both identity laws for the actual native Tor pairing

The existing graph correspondence is the finite sum of its actual component
prime correspondences. For each original admissible prime, exactly one identity
component has a nonempty incidence. The matching incidence is the original prime
by `IdentityPrime`, including its actual Tor multiplicity and residue-field degree.
All other incidences are empty. Native additive extensionality then gives both
unit laws for the actual Tor pairing, with arbitrary signed coefficients.

The identity graph needs a finite generic indexing set because the existing
`finiteCorrespondences` group has finite point support. This hypothesis is
explicit in the lower statements. It follows for compact smooth schemes from
native Noetherian component finiteness; arbitrary non-quasi-compact smooth schemes
are not asserted to possess a finite identity cycle. No connectedness, ambient
integrality, nonemptiness, or perfect-field assumption is used.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Units.lean`.
MVW (2006), Lecture 1, Example 1.2, printed p. 3, and the diagonal and composition
paragraphs, printed p. 4, supply the published graph-sum and unit conventions.
The stated arbitrary-field hypotheses and coefficient formulas are supplied by
native smooth/regular/normal geometry and the actual Tor calculations.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

/-- The existing graph correspondence is the sum of its actual native prime correspondences.
Only the existing graph definition is rewritten; no second identity cycle is introduced. -/
theorem graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) [IsSeparated g]
    (hX : (genericPoints X).Finite) :
    graphCorrespondenceOfComponents f g φ hφ hX =
      letI := hX.fintype
      ∑ s : genericPoints X, singleFiniteCorrespondence f g
        (correspondenceGraphMap f g φ hφ s.val)
        (isFiniteCorrespondencePoint_graphMap f g φ hφ s) 1 := by
  classical
  let := hX.fintype
  apply Subtype.ext
  change (∑ x ∈ hX.toFinset, single (correspondenceGraphMap f g φ hφ x) 1) =
    (finiteCorrespondences f g).subtype
      (∑ s : genericPoints X, singleFiniteCorrespondence f g
        (correspondenceGraphMap f g φ hφ s.val)
        (isFiniteCorrespondencePoint_graphMap f g φ hφ s) 1)
  rw [map_sum]
  change (∑ x ∈ hX.toFinset, single (correspondenceGraphMap f g φ hφ x) 1) =
    ∑ s : genericPoints X, single (correspondenceGraphMap f g φ hφ s.val) 1
  exact Finset.sum_subtype hX.toFinset (fun x => hX.mem_toFinset) _

/-- The target projection of the actual integral support lies in some actual component.
This uses continuous irreducible image and sobriety, not target integrality or connectedness. -/
theorem exists_genericPoint_range_correspondenceTarget_subset
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : pullback (C := Scheme) f g) :
    ∃ s : genericPoints Y,
      Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆ closure {s.val} := by
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  let p := (integralComponentAt z).subschemeι ≫ pullback.snd f g
  have hp : IsIrreducible (Set.range p) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (integralComponentAt z).subscheme).image
      p p.continuous.continuousOn
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hp
  refine ⟨genericPoints.ofComponent ⟨C, hC⟩, ?_⟩
  rw [(genericPoints.isGenericPoint_ofComponent (⟨C, hC⟩ : irreducibleComponents Y)).def]
  exact hsub

section RightIdentity

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [IsSeparated g]
  (hY : (genericPoints Y).Finite)

/-- Summing every actual right identity component returns the original native prime. -/
theorem incidenceTorPairing_single_graphIdentity_right
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) :
    incidenceTorPairing f g g (singleFiniteCorrespondence f g z hz 1)
      (graphCorrespondenceOfComponents g g (𝟙 Y) (Category.id_comp g) hY) =
      singleFiniteCorrespondence f g z hz 1 := by
  classical
  let := hY.fintype
  obtain ⟨s, hs⟩ := exists_genericPoint_range_correspondenceTarget_subset f g z
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence, map_sum]
  simp only [incidenceTorPairing_single_one]
  rw [Finset.sum_eq_single s]
  · exact incidenceTorCorrespondence_identity_right_of_range_subset f g z hz s hs
  · intro t ht hts
    exact incidenceTorCorrespondence_identity_right_eq_zero_of_ne f g z hz s t hts.symm hs
  · simp

/-- The full right unit law for the actual native Tor pairing, including signed cycles
and disconnected or empty smooth schemes with finite identity support. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Units.lean"
  "adaptation" "full right identity sum and additive extension on native finite cycles",
  colib_ref "MVW2006" "Lecture 1, printed pp. 3-4, graph sum and diagonal identity"
  "adaptation" "right unit over arbitrary fields, with finite generic identity support explicit",
  colib_tag "COL-0365",
  colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Units.lean"
  "adaptation" "Full componentwise identity laws"]
theorem incidenceTorPairing_graphIdentity_right (c : finiteCorrespondences f g) :
    incidenceTorPairing f g g c
      (graphCorrespondenceOfComponents g g (𝟙 Y) (Category.id_comp g) hY) = c := by
  have heq : (incidenceTorPairing f g g).flip
      (graphCorrespondenceOfComponents g g (𝟙 Y) (Category.id_comp g) hY) =
        AddMonoidHom.id (finiteCorrespondences f g) := by
    apply finiteCorrespondences.addHom_ext_one f g
    intro z hz
    exact incidenceTorPairing_single_graphIdentity_right f g hY z hz
  exact congrArg (fun F : finiteCorrespondences f g →+ finiteCorrespondences f g => F c) heq

end RightIdentity

section LeftIdentity

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [Smooth f] [IsSeparated f] [Smooth g] [IsSeparated g]
  (hX : (genericPoints X).Finite)

/-- Summing every actual left identity component returns the original native prime. -/
theorem incidenceTorPairing_graphIdentity_single_left
    (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) :
    incidenceTorPairing f f g
      (graphCorrespondenceOfComponents f f (𝟙 X) (Category.id_comp f) hX)
      (singleFiniteCorrespondence f g z hz 1) = singleFiniteCorrespondence f g z hz 1 := by
  classical
  let := hX.fintype
  let s : genericPoints X := genericPoints.ofComponent
    ⟨Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g), hz.2⟩
  have hs : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆
      closure {s.val} :=
    (genericPoints.isGenericPoint_ofComponent
      (⟨Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g), hz.2⟩ :
        irreducibleComponents X)).symm.le
  change (incidenceTorPairing f f g).flip (singleFiniteCorrespondence f g z hz 1)
    (graphCorrespondenceOfComponents f f (𝟙 X) (Category.id_comp f) hX) = _
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence, map_sum]
  simp only [AddMonoidHom.flip_apply, incidenceTorPairing_single_one]
  rw [Finset.sum_eq_single s]
  · exact incidenceTorCorrespondence_identity_left_of_range_subset f g z hz s hs
  · intro t ht hts
    exact incidenceTorCorrespondence_identity_left_eq_zero_of_ne f g z hz s t hts.symm hs
  · simp

/-- The full left unit law for the actual native Tor pairing. No global integral-source
restriction is introduced when the componentwise prime identities are extended additively. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Units.lean"
  "adaptation" "full left identity sum and additive extension in the native subgroup",
  colib_ref "MVW2006" "Lecture 1, printed pp. 3-4, graph sum and diagonal identity"
  "adaptation" "left unit over arbitrary fields with actual finite identity support",
  colib_tag "COL-0365",
  colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Units.lean"
  "adaptation" "Full componentwise identity laws"]
theorem incidenceTorPairing_graphIdentity_left (c : finiteCorrespondences f g) :
    incidenceTorPairing f f g
      (graphCorrespondenceOfComponents f f (𝟙 X) (Category.id_comp f) hX) c = c := by
  have heq : incidenceTorPairing f f g
      (graphCorrespondenceOfComponents f f (𝟙 X) (Category.id_comp f) hX) =
        AddMonoidHom.id (finiteCorrespondences f g) := by
    apply finiteCorrespondences.addHom_ext_one f g
    intro z hz
    exact incidenceTorPairing_graphIdentity_single_left f g hX z hz
  exact congrArg (fun F : finiteCorrespondences f g →+ finiteCorrespondences f g => F c) heq

end LeftIdentity

/-- Compactness is the needed global hypothesis for finite identity support.
Smoothness alone only gives local Noetherianness and does not imply this finiteness. -/
theorem finite_genericPoints_of_smooth_of_compact
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] [CompactSpace X] : (genericPoints X).Finite := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  exact genericPoints.finite (finite_irreducibleComponents_of_isNoetherian (X := X))

end Stacks.Chow
