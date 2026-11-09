/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.PulledTorCoefficients
public import Colib.AlgebraicGeometry.Correspondences.Graph.PulledStalkTor
public import Colib.AlgebraicGeometry.Correspondences.Graph.LeftPulledStalkTor
public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

/-!
# Actual Tor multiplicities for identity components

At every generic point of a right graph incidence or a left identity incidence,
the actual incidence Tor coefficient is one. The proof evaluates the existing
finite signed sum: native positive pulled-support Tor is zero, and its degree-zero
length is one. The degreewise native ambient comparison is already built into
`correspondenceIncidenceTorCoefficient_eq_sum_pulledStalkTor`. No coefficient,
comparison, transversality, or finite-Tor hypothesis is added to the statements.

The factors are smooth over an arbitrary field. Normality and local Noetherianity
of the component source are derived. Ambient schemes may be disconnected or empty.
An unmatched identity component has empty actual incidence, hence no generic point
at which a coefficient could contribute. The empty cases are not assigned an
artificial coefficient at a nonexistent point.

Implementation provenance: `kangxyz/motivic` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Tor.lean`.
This is a new direct-native reconstruction of its component-identity multiplicities.
Mathematical context: MVW (2006), Lecture 1, Example 1.2, printed p. 3, and the
composition and diagonal-identity paragraphs on printed p. 4. The precise local
Tor multiplicity theorem here is proved from native Stacks inputs; MVW is cited
for the graph and composition conventions, not as a verbatim local Tor statement.

The supporting references are Stacks 0AZT (actual Tor formula), 056S and 0569
(smooth implies regular implies normal), and 0357 (normal component geometry).
A coefficient computation is not yet the finite-sum Cor category unit theorem.
Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

section RightGraph

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (ψ : Y ⟶ Z) (hψ : ψ ≫ h = g)
  (s : genericPoints Y)

omit [IsSeparated g] in
/-- The actual finite alternating Tor sum is one at every generic right-graph incidence point.
All higher terms vanish by the native open-section calculation, not by hypothesis. -/
theorem correspondenceIncidenceTorCoefficient_graph_right_eq_one
    (t : genericPoints
      (correspondenceIncidence f g h z (correspondenceGraphMap g h ψ hψ s.val))) :
    correspondenceIncidenceTorCoefficient k f g h z
      (correspondenceGraphMap g h ψ hψ s.val) t = 1 := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : IsNormal Y := isNormal_of_isRegular Y (isRegular_of_smooth_over_field g)
  rw [correspondenceIncidenceTorCoefficient_eq_sum_pulledStalkTor]
  rw [Finset.sum_eq_single 0]
  · rw [length_correspondencePulledStalkTor_zero_graph_right_eq_one
      f g h z ψ hψ s t.val ((mem_genericPoints_iff_isMax _ _).mp t.property)]
    simp
  · intro n hn hn0
    cases n with
    | zero => exact (hn0 rfl).elim
    | succ n =>
      have hz := (Module.length_eq_zero_iff
        (R := (correspondenceTripleProduct f g h).presheaf.stalk
          (correspondenceIncidenceInclusion f g h z
            (correspondenceGraphMap g h ψ hψ s.val) t.val))).mpr
        (ModuleCat.isZero_iff_subsingleton.mp
          (isZero_correspondencePulledStalkTor_succ_graph_right f g h z ψ hψ s t.val n))
      simp only [hz, ENat.toNat_zero, Nat.cast_zero, mul_zero]
  · intro hzero
    exact (hzero (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim

end RightGraph

section RightIdentity

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [IsSeparated g]
  (z : pullback (C := Scheme) f g) (s : genericPoints Y)

/-- The actual right identity-component incidence multiplicity is one.
The statement includes every matching generic incidence, with no connectedness hypothesis. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Tor.lean"
  "adaptation" "right identity coefficient from native pulled Tor and the actual finite sum",
  colib_ref "MVW2006" "Lecture 1, printed p. 4, diagonal-identity paragraph" "background"
    "local multiplicity input for the right unit, proved here over an arbitrary field"]
theorem correspondenceIncidenceTorCoefficient_identity_right_eq_one
    (t : genericPoints
      (correspondenceIncidence f g g z
        (correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s.val))) :
    correspondenceIncidenceTorCoefficient k f g g z
      (correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s.val) t = 1 :=
  correspondenceIncidenceTorCoefficient_graph_right_eq_one k f g g z (𝟙 Y) (Category.id_comp g) s t

omit [Smooth f] in
/-- A distinct right identity component contributes no generic incidence point.
Containment is a statement about the original support's actual projection. -/
theorem isEmpty_genericPoints_correspondenceIncidence_identity_right_of_ne
    (s' : genericPoints Y) (hss' : s ≠ s')
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.snd f g) ⊆
      closure {s.val}) :
    IsEmpty (genericPoints (correspondenceIncidence f g g z
      (correspondenceGraphMap g g (𝟙 Y) (Category.id_comp g) s'.val))) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let : IsNormal Y := isNormal_of_isRegular Y (isRegular_of_smooth_over_field g)
  let := isEmpty_correspondenceIncidence_graphMap_of_ne f g g (𝟙 Y) (Category.id_comp g)
    z s s' hss' hz
  infer_instance

end RightIdentity

section LeftIdentity

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [Smooth f] [IsSeparated f] [Smooth g]
  (z : pullback (C := Scheme) f g) (s : genericPoints X)

/-- The actual left identity-component incidence multiplicity is one.
The native balancing theorem already restored the original left/right Tor order. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Identity/Tor.lean"
  "adaptation" "left identity coefficient in the original Tor order, with the actual finite sum",
  colib_ref "MVW2006" "Lecture 1, printed p. 4, diagonal-identity paragraph" "background"
    "local multiplicity input for the left unit; no arbitrary-left-graph transversality claim"]
theorem correspondenceIncidenceTorCoefficient_identity_left_eq_one
    (t : genericPoints
      (correspondenceIncidence f f g
        (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z)) :
    correspondenceIncidenceTorCoefficient k f f g
      (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z t = 1 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNormal X := isNormal_of_isRegular X (isRegular_of_smooth_over_field f)
  rw [correspondenceIncidenceTorCoefficient_eq_sum_pulledStalkTor]
  rw [Finset.sum_eq_single 0]
  · rw [length_correspondencePulledStalkTor_zero_diagonal_left_eq_one
      f g z s t.val ((mem_genericPoints_iff_isMax _ _).mp t.property)]
    simp
  · intro n hn hn0
    cases n with
    | zero => exact (hn0 rfl).elim
    | succ n =>
      have hz := (Module.length_eq_zero_iff
        (R := (correspondenceTripleProduct f f g).presheaf.stalk
          (correspondenceIncidenceInclusion f f g
            (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s.val) z t.val))).mpr
        (ModuleCat.isZero_iff_subsingleton.mp
          (isZero_correspondencePulledStalkTor_succ_identity_left k f g z s t.val n))
      simp only [hz, ENat.toNat_zero, Nat.cast_zero, mul_zero]
  · intro hzero
    exact (hzero (Finset.mem_range.mpr (Nat.zero_lt_succ _))).elim

omit [Smooth g] in
/-- A distinct left identity component contributes no generic incidence point. -/
theorem isEmpty_genericPoints_correspondenceIncidence_identity_left_of_ne
    (s' : genericPoints X) (hss' : s ≠ s')
    (hz : Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst f g) ⊆
      closure {s.val}) :
    IsEmpty (genericPoints (correspondenceIncidence f f g
      (correspondenceGraphMap f f (𝟙 X) (Category.id_comp f) s'.val) z)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNormal X := isNormal_of_isRegular X (isRegular_of_smooth_over_field f)
  let := isEmpty_correspondenceIncidence_diagonal_left_of_ne f g z s s' hss' hz
  infer_instance

end LeftIdentity

end Stacks.Chow
