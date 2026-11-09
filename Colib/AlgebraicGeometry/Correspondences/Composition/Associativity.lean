/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWholeCycle
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingWholeCycle

/-!
# Associativity of the actual signed incidence Tor pairing

The two literal generator brackets have independently proved equalities with the same
finite pushforward of the actual combined-diagonal triple Tor cycle. Equality in the native
finite-correspondence subgroup follows from this equality of the underlying native cycles.
Three applications of native additive extensionality then cover every signed cycle.

There is no supplied comparison, associativity assumption, alternate composition, or
connectedness/integrality restriction. The field is arbitrary. The lower statement even
allows non-quasi-compact smooth schemes: finite identity support is only needed by the
separate category construction on the existing finite-type smooth site.

Implementation adapted from `motivic_source_a6805c4`,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/TorAssociativity.lean`,
blob `dfa8b6e238e80d6f67dc3a1c2ed999d78e8cd5a0`. The old `Finsupp.addHom_ext` is replaced
by extensionality of the actual native cycle subgroup. MVW (2006), Lecture 1, printed
pp. 4-6, gives the composition and finite-correspondence category conventions. The geometric
and Tor comparisons are the actual imported proofs, not additional categorical hypotheses.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  [IsSeparated g] [IsSeparated h] [IsSeparated i]

/-- Both actual prime brackets are the same actual triple-Tor finite pushforward. -/
theorem incidenceTorPairing_assoc_single_one
    (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (v : pullback (C := Scheme) h i)
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    incidenceTorPairing f h i
        (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
          (singleFiniteCorrespondence g h w hw 1)) (singleFiniteCorrespondence h i v hv 1) =
      incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)
        (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw 1)
          (singleFiniteCorrespondence h i v hv 1)) := by
  apply Subtype.ext
  exact (leftBracket_val_eq_finiteCyclePushforward_tripleTorCycle k f g h i z w v hz hw hv).trans
    (rightBracket_val_eq_finiteCyclePushforward_tripleTorCycle k f g h i z w v hz hw hv).symm

/-- The actual incidence Tor pairing is associative on all signed native finite cycles. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/TorAssociativity.lean"
  "adaptation" "actual signed associativity by independently proved common triple Tor comparisons",
  colib_ref "MVW2006" "Lecture 1, printed pp. 4-6, composition and the category Cor"
  "adaptation" "arbitrary-field smooth schemes with native signed cycle coefficients"]
@[colib_tag "COL-0352"]
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/TorAssociativity.lean"
  "adaptation" "Associativity of signed Tor composition"]
theorem incidenceTorPairing_assoc (α : finiteCorrespondences f g)
    (β : finiteCorrespondences g h) (γ : finiteCorrespondences h i) :
    incidenceTorPairing f h i (incidenceTorPairing f g h α β) γ =
      incidenceTorPairing f g i α (incidenceTorPairing g h i β γ) := by
  have hthird (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z)
      (w : pullback (C := Scheme) g h) (hw : IsFiniteCorrespondencePoint g h w) :
      incidenceTorPairing f h i
          (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)
            (singleFiniteCorrespondence g h w hw 1)) =
        (incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)).comp
          (incidenceTorPairing g h i (singleFiniteCorrespondence g h w hw 1)) := by
    apply finiteCorrespondences.addHom_ext_one h i
    intro v hv
    exact incidenceTorPairing_assoc_single_one k f g h i z w v hz hw hv
  have hsecond (z : pullback (C := Scheme) f g) (hz : IsFiniteCorrespondencePoint f g z) :
      ((incidenceTorPairing f h i).flip γ).comp
          (incidenceTorPairing f g h (singleFiniteCorrespondence f g z hz 1)) =
        (incidenceTorPairing f g i (singleFiniteCorrespondence f g z hz 1)).comp
          ((incidenceTorPairing g h i).flip γ) := by
    apply finiteCorrespondences.addHom_ext_one g h
    intro w hw
    exact congrArg (fun F : finiteCorrespondences h i →+ finiteCorrespondences f i => F γ)
      (hthird z hz w hw)
  have hfirst : ((incidenceTorPairing f h i).flip γ).comp
        ((incidenceTorPairing f g h).flip β) =
      (incidenceTorPairing f g i).flip (incidenceTorPairing g h i β γ) := by
    apply finiteCorrespondences.addHom_ext_one f g
    intro z hz
    exact congrArg (fun F : finiteCorrespondences g h →+ finiteCorrespondences f i => F β)
      (hsecond z hz)
  exact congrArg (fun F : finiteCorrespondences f g →+ finiteCorrespondences f i => F α) hfirst

end Stacks.Chow
