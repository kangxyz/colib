/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointTorCuts
public import Colib.AlgebraicGeometry.Correspondences.Composition.FlatSourceCycle

/-!
# The actual polynomial endpoint Tor cycle is the full incidence cycle

The genuine principal-cut producer at bound zero identifies the full cut with
native ambient Tor zero. Native Tor-zero transport then gives the full original
incidence stalk length, including nilpotents, without support flatness.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X Z : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- The original native endpoint Euler coefficient equals the full unreduced
incidence stalk length. Only structural smoothness and parameter dominance are used. -/
theorem graphIncidenceTorCoefficient_eq_fullStalkLength
    [IsIntegral X] [IsSeparated p] [Smooth p] [Smooth h]
    (c : k) (s : genericPoints X)
    (w : pullback (C := Scheme) (projection p ≫ p) h)
    [IsDominant ((integralComponentAt w).subschemeι ≫
      pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]
    (t : genericPoints (correspondenceIncidence p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w)) :
    correspondenceIncidenceTorCoefficient k p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w t =
      ((Module.length
        ((correspondenceIncidence p (projection p ≫ p) h
          (correspondenceGraphMap p (projection p ≫ p)
            (endpoint p c) (by simp) s.val) w).presheaf.stalk
          t.val)
        ((correspondenceIncidence p (projection p ≫ p) h
          (correspondenceGraphMap p (projection p ≫ p)
            (endpoint p c) (by simp) s.val) w).presheaf.stalk
          t.val)).toNat : ℤ) := by
  let := isIntegral_integralComponentAt w
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  have : Smooth (projection p) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (projection p ≫ p) := inferInstance
  have : IsAffineHom (projection p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsSeparated (projection p ≫ p) := inferInstance
  let : IsClosedImmersion (endpoint p c) := by
    have H := (endpoint_parameter_isPullback p c).flip
    rw [← H.isoPullback_hom_snd]
    infer_instance
  let δ := correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val
  let x := correspondenceIncidenceInclusion p (projection p ≫ p) h δ w t.val
  let l := correspondenceIncidenceToLeftPulled p (projection p ≫ p) h δ w t.val
  have hx := correspondenceIncidence_leftPulled_point_eq p (projection p ≫ p) h δ w t.val
  let y := pullback.snd (pullback.snd p (projection p ≫ p))
    (pullback.fst (projection p ≫ p) h) x
  let z := (leftGraphPulledOuterIso p (projection p ≫ p) h (endpoint p c) (by simp) s).hom l
  have hy := leftGraphPulledOuterIso_point p (projection p ≫ p) h (endpoint p c) (by simp)
    s x l hx
  have he := graphIncidence_right_point p (projection p ≫ p) h (endpoint p c) (by simp)
    s w t.val
  have H := graphEndpoint_stalkTor_eq_parameterCut p h c (integralComponentAt w).subschemeι
    y z (pullback.snd (C := Scheme) _ _ t.val) hy he
    0
  dsimp only at H
  simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul] at H
  have ht := graphIncidenceTor_length_eq_endpointStalkTor
    k p (projection p ≫ p) h (endpoint p c) (by simp) s w t.val 0
  have hz := length_correspondenceIncidenceAmbientTor_zero
    p (projection p ≫ p) h δ w t.val
  rw [graphIncidenceTorCoefficient_eq_parameterCut]
  exact H.symm.trans (congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (ht.symm.trans hz))

local instance : Smooth (projection p) := by
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  exact SmoothOfRelativeDimension.smooth 1 _

local instance : IsAffineHom (projection p) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance

variable [IsIntegral X] [IsSeparated p] [Smooth p] [Smooth h]
  (c : k) (s : genericPoints X)
  (w : pullback (C := Scheme) (projection p ≫ p) h)
  [IsDominant ((integralComponentAt w).subschemeι ≫
    pullback.fst (projection p ≫ p) h ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]

/-- At the literal original endpoint, the actual native Tor cycle is exactly the
whole unreduced incidence fundamental cycle, with no flatness of its support. -/
@[colib_tag "COL-1086", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/RingTheory/Tor/FlatExtendScalarsFirst.lean:66-84"
  "ingredient" "Flat change of rings for actual support Tor; the endpoint geometry and cycle \
    assembly are proved here."]
theorem graphEndpoint_incidenceTorCycle_eq_fundamentalCycle
    [IsNoetherian (correspondenceIncidence p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w)]
    (hw : IsFiniteCorrespondencePoint (projection p ≫ p) h w) :
    incidenceTorCycle p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w hw =
      AlgebraicCycle.fundamentalCycle (correspondenceIncidence p (projection p ≫ p) h
        (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w) := by
  let δ := correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ genericPoints (correspondenceIncidence p (projection p ≫ p) h δ w)
  · rw [incidenceTorCycle_apply_generic _ _ _ _ _ hw ⟨x, hx⟩,
      AlgebraicCycle.fundamentalCycle_apply_generic _ ⟨x, hx⟩]
    exact graphIncidenceTorCoefficient_eq_fullStalkLength p h c s w ⟨x, hx⟩
  · rw [incidenceTorCycle_apply_of_notMem _ _ _ _ _ hw x hx,
      AlgebraicCycle.fundamentalCycle_apply_of_notMem _ x hx]

/-- Native finite pushforward transports this actual cycle identity, preserving
all residue degrees and collisions automatically. -/
theorem graphEndpoint_incidenceTorCorrespondence_val [IsSeparated h]
    [IsNoetherian (correspondenceIncidence p (projection p ≫ p) h
      (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w)]
    (hw : IsFiniteCorrespondencePoint (projection p ≫ p) h w) :
    let δ := correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val
    let hδ := isFiniteCorrespondencePoint_graphMap p (projection p ≫ p)
      (endpoint p c) (by simp) s
    (incidenceTorCorrespondence p (projection p ≫ p) h δ w hδ hw).val =
      letI := isFinite_correspondenceIncidenceMap p (projection p ≫ p) h δ w hδ hw
      finiteCyclePushforward (correspondenceIncidenceMap p (projection p ≫ p) h δ w)
        (AlgebraicCycle.fundamentalCycle (correspondenceIncidence p (projection p ≫ p) h
          δ w)) := by
  dsimp only
  rw [incidenceTorCorrespondence_val,
    graphEndpoint_incidenceTorCycle_eq_fundamentalCycle p h c s w hw]

/-- The original endpoint incidence correspondence is the finite pushforward of
the whole original graph fibre, with all its nilpotent multiplicities retained. -/
theorem graphEndpoint_incidenceTorCorrespondence_eq_graphFiberPushforward
    [IsSeparated h] [IsNoetherian X]
    (hw : IsFiniteCorrespondencePoint (projection p ≫ p) h w) :
    let δ := correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val
    let hδ := isFiniteCorrespondencePoint_graphMap p (projection p ≫ p)
      (endpoint p c) (by simp) s
    letI := hw.1
    letI := isNoetherian_correspondenceGraphFiber (projection p ≫ p) h w (endpoint p c) hw
    letI := isFinite_correspondenceGraphFiberMap p (projection p ≫ p) h w
      (endpoint p c) (by simp) hw
    (incidenceTorCorrespondence p (projection p ≫ p) h δ w hδ hw).val =
      finiteCyclePushforward
        (correspondenceGraphFiberMap p (projection p ≫ p) h w (endpoint p c) (by simp))
        (AlgebraicCycle.fundamentalCycle
          (correspondenceGraphFiber (projection p ≫ p) h w (endpoint p c))) := by
  dsimp only
  let δ := correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val
  let hδ := isFiniteCorrespondencePoint_graphMap p (projection p ≫ p)
    (endpoint p c) (by simp) s
  have := hw.1
  have := isNoetherian_correspondenceIncidence_of_finite_source
    p (projection p ≫ p) h δ w hδ hw
  have := isFinite_correspondenceIncidenceMap p (projection p ≫ p) h δ w hδ hw
  have := isFinite_correspondenceGraphFiberMap p (projection p ≫ p) h w
    (endpoint p c) (by simp) hw
  have := isNoetherian_correspondenceGraphFiber (projection p ≫ p) h w (endpoint p c) hw
  rw [graphEndpoint_incidenceTorCorrespondence_val p h c s w hw]
  let e : correspondenceIncidence p (projection p ≫ p) h δ w ≅
      correspondenceGraphFiber (projection p ≫ p) h w (endpoint p c) :=
    correspondenceLeftGraphFiberIso p (projection p ≫ p) h w
      (endpoint p c) (by simp) s
  let v := correspondenceGraphFiberMap p (projection p ≫ p) h w (endpoint p c) (by simp)
  have he := finiteCyclePushforward_fundamentalCycle_iso
    (A := correspondenceIncidence p (projection p ≫ p) h δ w)
    (X := correspondenceGraphFiber (projection p ≫ p) h w (endpoint p c)) e
  have hem : e.hom ≫ v = correspondenceIncidenceMap p (projection p ≫ p) h δ w :=
    correspondenceLeftGraphFiberIso_map p (projection p ≫ p) h w
      (endpoint p c) (by simp) s
  have H := (finiteCyclePushforward_comp_apply e.hom v
    (AlgebraicCycle.fundamentalCycle
      (correspondenceIncidence p (projection p ≫ p) h δ w))).symm
  simp only [he, hem] at H
  exact H

end Stacks.Chow
