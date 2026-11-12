/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryGraphEndpointCoefficient

/-! # Original signed source cuts through the actual outer finite pushforward

Both original residue-degree stages and every outer image collision remain
explicit. This is the coefficient of the actual native incidence correspondence,
not an equality of Chow classes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow.PrincipalBoundary

variable {k : Type u} [Field k] {C X Y V : Scheme.{u}}
    [IsIntegral C] [IsNoetherian C] [IsIntegral X] [IsAffine X]
    (p : X ⟶ Spec (.of k)) (h : Y ⟶ Spec (.of k))
    [IsSeparated p] [IsSeparated h] [Smooth p] [Smooth h]
    (q : C ⟶ parameterSpace p) [IsProper q]
    (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
    (F : Γ(C, U)) (hF : IsUnit F)
    (g : V ⟶ Y) (hg : j ≫ q ≫ (projection p ≫ p) = g ≫ h)

local instance : IsAffineHom (projection p) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance

local instance : IsAffine (parameterSpace p) := isAffine_of_isAffineHom (projection p)

local instance : Smooth (projection p) := by
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  exact SmoothOfRelativeDimension.smooth 1 _

/-- The explicit source-cut formula through both actual finite maps. Every original
source point and every outer image collision is retained. -/
def sourceEndpointPushforwardCoefficient (z : support U F) (c : k)
    (s : genericPoints X) (y : pullback (C := Scheme) p h) : ℤ :=
    let w := imagePoint (projection p ≫ p) h q j U hU F hF g hg z
    let δ := correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val
    let hw := imagePoint_admissible (projection p ≫ p) h q j U hU F hF g hg z
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth p
      (projection p ≫ p) h δ w hw).fintype
    let D := (integralComponentAt z.val).subscheme
    letI := isIntegral_integralComponentAt z.val
    let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
    let e := integralImageMap r
    let eqn := PolynomialEndpointFiber.equation
      ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c
    ∑ t : genericPoints (correspondenceIncidence p (projection p ≫ p) h δ w),
      if (correspondenceIncidenceMap p (projection p ≫ p) h δ w).base t.val = y then
        ((cycle U F) z.val *
          (∑ᶠ x ∈ e.base ⁻¹' {pullback.snd (C := Scheme) _ _ t.val},
            ((Module.length (D.presheaf.stalk x)
              (D.presheaf.stalk x ⧸ Ideal.span
                {D.presheaf.germ ⊤ x (by trivial) (e.appTop eqn)})).toNat : ℤ) *
                  (r.residueDegree x : ℤ))) *
          ((correspondenceIncidenceMap p (projection p ≫ p) h δ w).residueDegree t.val : ℤ)
      else 0

/-- The native outer finite pushforward sums every collision with its own residue
degree, after replacing local Tor by the original signed source-cut formula. -/
theorem componentCorrespondence_graphEndpointPushforwardCoefficient
    (z : support U F) (c : k) (s : genericPoints X) (y : pullback (C := Scheme) p h) :
    let w := imagePoint (projection p ≫ p) h q j U hU F hF g hg z
    let δ := correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val
    let hw := imagePoint_admissible (projection p ≫ p) h q j U hU F hF g hg z
    let hδ := isFiniteCorrespondencePoint_graphMap p (projection p ≫ p)
      (endpoint p c) (by simp) s
    letI := (finite_genericPoints_correspondenceIncidence_of_smooth p
      (projection p ≫ p) h δ w hw).fintype
    let D := (integralComponentAt z.val).subscheme
    letI := isIntegral_integralComponentAt z.val
    let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
    let e := integralImageMap r
    let eqn := PolynomialEndpointFiber.equation
      ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c
    (componentCorrespondence (projection p ≫ p) h q j U hU F hF g hg z).val w *
      (incidenceTorCorrespondence p (projection p ≫ p) h δ w hδ hw).val y =
    ∑ t : genericPoints (correspondenceIncidence p (projection p ≫ p) h δ w),
      if (correspondenceIncidenceMap p (projection p ≫ p) h δ w).base t.val = y then
        ((cycle U F) z.val *
          (∑ᶠ x ∈ e.base ⁻¹' {pullback.snd (C := Scheme) _ _ t.val},
            ((Module.length (D.presheaf.stalk x)
              (D.presheaf.stalk x ⧸ Ideal.span
                {D.presheaf.germ ⊤ x (by trivial) (e.appTop eqn)})).toNat : ℤ) *
                  (r.residueDegree x : ℤ))) *
          ((correspondenceIncidenceMap p (projection p ≫ p) h δ w).residueDegree t.val : ℤ)
      else 0 := by
  classical
  dsimp only
  rw [incidenceTorCorrespondence_coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs
  · rw [← mul_assoc, ← componentCorrespondence_graphEndpointTorCoefficient
      p h q j U hU F hF g hg z c s t]
  · exact mul_zero _

/-- The actual native pairing of an endpoint graph prime with an original
principal component has the complete two-stage source-cut coefficient. -/
theorem componentCorrespondence_graphPairing_coefficient
    (z : support U F) (c : k) (s : genericPoints X) (y : pullback (C := Scheme) p h) :
    (incidenceTorPairing p (projection p ≫ p) h
      (singleFiniteCorrespondence p (projection p ≫ p)
        (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val)
        (isFiniteCorrespondencePoint_graphMap p (projection p ≫ p)
          (endpoint p c) (by simp) s) 1)
      (componentCorrespondence (projection p ≫ p) h q j U hU F hF g hg z)).val y =
      sourceEndpointPushforwardCoefficient p h q j U hU F hF g hg z c s y := by
  let := isIntegral_integralComponentAt z.val
  change (incidenceTorPairing p (projection p ≫ p) h _
    (singleFiniteCorrespondence _ _ _
      (imagePoint_admissible (projection p ≫ p) h q j U hU F hF g hg z)
      ((cycle U F) z.val * ((componentMap (projection p ≫ p) h q j U hU F hF g hg z).residueDegree
        (genericPoint (integralComponentAt z.val).subscheme) : ℤ)))).val y = _
  rw [incidenceTorPairing_single_apply, one_mul]
  have H := componentCorrespondence_graphEndpointPushforwardCoefficient
    p h q j U hU F hF g hg z c s y
  simpa only [componentCorrespondence, Function.locallyFinsuppWithin.single_apply, ite_true,
    sourceEndpointPushforwardCoefficient] using H

/-- The complete original principal correspondence retains every original
support and every source/outer collision in its actual native pairing coefficient. -/
theorem correspondence_graphPairing_coefficient (c : k) (s : genericPoints X)
    (y : pullback (C := Scheme) p h) :
    let := (cycle U F).finite_support.fintype
    (incidenceTorPairing p (projection p ≫ p) h
      (singleFiniteCorrespondence p (projection p ≫ p)
        (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val)
        (isFiniteCorrespondencePoint_graphMap p (projection p ≫ p)
          (endpoint p c) (by simp) s) 1)
      (correspondence (projection p ≫ p) h q j U hU F hF g hg)).val y =
      ∑ z : support U F,
        sourceEndpointPushforwardCoefficient p h q j U hU F hF g hg z c s y := by
  classical
  let := (cycle U F).finite_support.fintype
  unfold correspondence
  rw [map_sum]
  change ((finiteCorrespondences p h).subtype (∑ z : support U F, _)) y = _
  rw [map_sum, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun z _ =>
    componentCorrespondence_graphPairing_coefficient p h q j U hU F hF g hg z c s y

/-- The original whole endpoint graph and principal correspondence have the
complete source-cut coefficient, retaining both finite residue factors and collisions. -/
@[colib_tag "COL-1074"]
theorem correspondence_endpointGraph_coefficient (c : k) (s : genericPoints X)
    (y : pullback (C := Scheme) p h) :
    let hX : (genericPoints X).Finite := by
      rw [genericPoints_eq_singleton]
      exact Set.finite_singleton _
    letI := (cycle U F).finite_support.fintype
    (incidenceTorPairing p (projection p ≫ p) h
      (graphCorrespondenceOfComponents p (projection p ≫ p) (endpoint p c) (by simp) hX)
      (correspondence (projection p ≫ p) h q j U hU F hF g hg)).val y =
      ∑ z : support U F,
        sourceEndpointPushforwardCoefficient p h q j U hU F hF g hg z c s y := by
  classical
  dsimp only
  let hX : (genericPoints X).Finite := by
    rw [genericPoints_eq_singleton]
    exact Set.finite_singleton _
  let := hX.fintype
  let : Unique (genericPoints X) :=
    { default := s
      uniq := fun t => Subtype.ext (by
        have ht := t.property
        have hs := s.property
        simp only [genericPoints_eq_singleton, Set.mem_singleton_iff] at ht hs
        exact ht.trans hs.symm) }
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence,
    Fintype.sum_subsingleton _ s]
  exact correspondence_graphPairing_coefficient p h q j U hU F hF g hg c s y

end Stacks.Chow.PrincipalBoundary
