/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointCorrespondence

/-! # Regression for actual original principal polynomial correspondence endpoints -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X C V W B Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p] [IsSeparated p]
    (h : Y ⟶ Spec (.of k)) [Smooth h] [IsSeparated h]
    (q : C ⟶ X) [IsProper q] [IsIntegral C] [IsNoetherian C]
    (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (v : W ⟶ C) [IsOpenImmersion v]
    (b : B ⟶ W) [Nonempty B]
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
    [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]
    (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ h)

local instance : IsAffineHom (projection p) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback _ _).flip inferInstance

local instance : IsAffine (parameterSpace p) := isAffine_of_isAffineHom (projection p)

local instance : Smooth (projection p) := by
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  exact SmoothOfRelativeDimension.smooth 1 _

local instance : IsProper (lineMap p q) :=
  MorphismProperty.of_isPullback (lineMap_isPullback p q).flip inferInstance

local instance : IsAffineHom (projection (j ≫ (q ≫ p))) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback _ _).flip inferInstance

local instance : (parameterSpace (j ≫ (q ≫ p))).IsQuasiAffine :=
  Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ (q ≫ p)))

local instance : SmoothOfRelativeDimension 1 (lineMap (q ≫ p) j ≫ lineMap p q) :=
  MorphismProperty.of_isPullback
    ((lineMap_isPullback (q ≫ p) j).paste_horiz (lineMap_isPullback p q)).flip inferInstance


local instance {A D : Scheme.{u}} (i : A ⟶ D) [IsOpenImmersion i]
    [IsIntegral A] [IsIntegral D] : IsDominant i :=
  ⟨i.isOpenEmbedding.isOpen_range.dense ⟨i (genericPoint A), Set.mem_range_self _⟩⟩

variable [IsIntegral V] [IsIntegral W]

example :
    let hX : (genericPoints X).Finite := by
      rw [genericPoints_eq_singleton]
      exact Set.finite_singleton _
    letI := retainedCurve_isNoetherian j
    let G := fun c : k => graphCorrespondenceOfComponents p (projection p ≫ p)
      (endpoint p c) (by simp) hX
    let K := PrincipalPolynomialFamily.correspondence p h q j v b hcover f hf g hg
    incidenceTorPairing p (projection p ≫ p) h (G 0) K = 0 ∧
      (incidenceTorPairing p (projection p ≫ p) h (G 1) K).val =
        noetherianCyclePushforward (retainedCurveMap p h q j g hg)
          (principalCycle V (j.functionFieldMap (curveRationalFunction v f))) :=
  polynomialCorrespondence_endpointGraph_zero_one p h q j v b hcover f hf g hg

end AlgebraicGeometry.PrincipalFamilyUnitOpen

#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.sourceEndpoint_generic_original_coheight
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.principalFamily_support_endpoint_coheight
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.signedSourceEndpointCycle_zero_one
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.retainedSignedSourceEndpointCycle_zero_one
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.componentEndpointCycle_eq_retainedPushforward
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialCorrespondence_endpointGraph_val
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialCorrespondence_endpointGraph_zero_one
#print axioms AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialCorrespondence_endpointGraph_eq_of_val
#print axioms Stacks.Chow.noetherianCyclePushforward_apply_of_isOpenImmersion
