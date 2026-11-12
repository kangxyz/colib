/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryParameterCuts
public import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointTorCuts
public import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointCodimension

/-!
# Original signed principal image coefficients at actual graph endpoints

The original principal order coefficient, source-point residue degrees and full
source cuts give the original component-correspondence coefficient times its
actual native incidence Tor coefficient. Endpoint coheight and parameter
nonvanishing are produced, not assumed. The later outer finite pushforward and
its image-collision sum remain separate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

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

/-- The actual native local incidence coefficient has the original signed finite
source-cut formula, retaining all source fibre points and their residue degrees. -/
@[colib_tag "COL-1071", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/RingTheory/Tor/FlatExtendScalarsFirst.lean:66-84"
  "ingredient" "Flat change of rings for actual support Tor; the endpoint geometry and cycle \
    assembly are proved here."]
theorem componentCorrespondence_graphEndpointTorCoefficient (z : support U F)
    (c : k) (s : genericPoints X) :
    let w := imagePoint (projection p ≫ p) h q j U hU F hF g hg z
    let D := (integralComponentAt z.val).subscheme
    letI := isIntegral_integralComponentAt z.val
    let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
    let e := integralImageMap r
    let eqn := PolynomialEndpointFiber.equation
      ((integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c
    ∀ t : genericPoints (correspondenceIncidence p (projection p ≫ p) h
        (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w),
      (cycle U F) z.val *
        (∑ᶠ x ∈ e.base ⁻¹' {pullback.snd (C := Scheme) _ _ t.val},
          ((Module.length (D.presheaf.stalk x)
            (D.presheaf.stalk x ⧸ Ideal.span
              {D.presheaf.germ ⊤ x (by trivial) (e.appTop eqn)})).toNat : ℤ) *
                (r.residueDegree x : ℤ)) =
        (componentCorrespondence (projection p ≫ p) h q j U hU F hF g hg z).val w *
          correspondenceIncidenceTorCoefficient k p (projection p ≫ p) h
            (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val) w t := by
  have : IsAffineHom (projection p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom) (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsAffine (parameterSpace p) := isAffine_of_isAffineHom (projection p)
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  have : Smooth (projection p) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (projection p ≫ p) := inferInstance
  have : IsLocallyNoetherian (parameterSpace p) :=
    LocallyOfFiniteType.isLocallyNoetherian (projection p ≫ p)
  have : IsLocallyNoetherian (pullback (projection p ≫ p) h) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (projection p ≫ p) h)
  let a := pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
  have := imagePoint_parameter_isDominant (projection p ≫ p) h q j U hU F hF g hg a z
  have : IsLocallyNoetherian
      (integralComponentAt (imagePoint (projection p ≫ p) h q j U hU F hF g hg z)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      (integralComponentAt (imagePoint (projection p ≫ p) h q j U hU F hF g hg z)).subschemeι
  dsimp only
  intro t
  rw [graphIncidenceTorCoefficient_eq_parameterCut]
  exact componentCorrespondence_endpointCutCoefficient (projection p ≫ p) h q j U hU
    F hF g hg a z c _ (graphIncidence_endpoint_generic_coheight p h c s _ t)

end Stacks.Chow.PrincipalBoundary
