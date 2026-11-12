/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryEndpointFiberTransport
public import Colib.AlgebraicGeometry.Correspondences.Principal.GraphEndpointFundamentalCycle
public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointFundamentalPushforward

/-! # Original signed boundary endpoint cycles before rational equivalence -/

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


/-- The original affine smooth base is Noetherian. -/
theorem base_isNoetherian {k : Type u} [Field k] {X : Scheme.{u}}
    [IsAffine X] (p : X ⟶ Spec (.of k)) [Smooth p] : IsNoetherian X :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian p
    toCompactSpace := inferInstance }

/-- The whole original source-support endpoint, pushed by its original outer map
and multiplied by the unchanged signed principal order. -/
def componentEndpointCycle (z : support U F) (c : k) :
    AlgebraicCycle (pullback (C := Scheme) p h) ℤ := by
  let := base_isNoetherian p
  let := isIntegral_integralComponentAt z.val
  let w := imagePoint (projection p ≫ p) h q j U hU F hF g hg z
  let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
  let e : (integralComponentAt z.val).subscheme ⟶ (integralComponentAt w).subscheme :=
    integralImageMap r
  let n := (integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h
  let : IsFinite r := componentMap_isFinite (projection p ≫ p) h q j U hU F hF g hg z
  let : IsFinite e := integralImageMap_isFinite r
  let : IsFinite n := (imagePoint_admissible (projection p ≫ p) h q j U hU F hF g hg z).1
  let v := correspondenceGraphFiberMap p (projection p ≫ p) h w (endpoint p c) (by simp)
  let : IsFinite v := isFinite_correspondenceGraphFiberMap p (projection p ≫ p) h w
    (endpoint p c) (by simp) (imagePoint_admissible (projection p ≫ p) h q j U hU F hF g hg z)
  let := polynomialEndpoint_isNoetherian p (e ≫ n) c
  exact (cycle U F) z.val • finiteCyclePushforward (polynomialEndpointMap p n e c ≫ v)
    (AlgebraicCycle.fundamentalCycle (pullback (C := Scheme) (endpoint p c) (e ≫ n)))

/-- Native endpoint pairing with one original signed principal component is
exactly its whole source endpoint cycle, not just its rational-equivalence class. -/
theorem componentCorrespondence_graphPairing_eq_endpointCycle
    (z : support U F) (c : k) (s : genericPoints X) :
    (incidenceTorPairing p (projection p ≫ p) h
      (singleFiniteCorrespondence p (projection p ≫ p)
        (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val)
        (isFiniteCorrespondencePoint_graphMap p (projection p ≫ p)
          (endpoint p c) (by simp) s) 1)
      (componentCorrespondence (projection p ≫ p) h q j U hU F hF g hg z)).val =
      componentEndpointCycle p h q j U hU F hF g hg z c := by
  let := base_isNoetherian p
  let := isIntegral_integralComponentAt z.val
  let w := imagePoint (projection p ≫ p) h q j U hU F hF g hg z
  let := isIntegral_integralComponentAt w
  let hw := imagePoint_admissible (projection p ≫ p) h q j U hU F hF g hg z
  let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
  let e : (integralComponentAt z.val).subscheme ⟶ (integralComponentAt w).subscheme :=
    integralImageMap r
  let n := (integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h
  let : IsFinite r := componentMap_isFinite (projection p ≫ p) h q j U hU F hF g hg z
  let : IsFinite e := integralImageMap_isFinite r
  let : IsDominant e := integralImageMap_isDominant r
  let : IsFinite n := hw.1
  let : IsDominant n := imagePoint_projection_isDominant p h q j U hU F hF g hg z
  let v := correspondenceGraphFiberMap p (projection p ≫ p) h w (endpoint p c) (by simp)
  let : IsFinite v := isFinite_correspondenceGraphFiberMap p (projection p ≫ p) h w
    (endpoint p c) (by simp) hw
  let := polynomialEndpoint_isNoetherian p n c
  let := polynomialEndpoint_isNoetherian p (e ≫ n) c
  let : IsDominant ((integralComponentAt w).subschemeι ≫
      pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) :=
    imagePoint_parameter_isDominant (projection p ≫ p) h q j U hU F hF g hg
      (pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) z
  have H := polynomialEndpoint_fundamentalCycle_pushforward p n e c
  have HB := congrArg (fun Z => (cycle U F) z.val • finiteCyclePushforward v Z) H
  rw [map_zsmul, smul_smul, finiteCyclePushforward_comp_apply] at HB
  have hedeg : e.residueDegree (genericPoint (integralComponentAt z.val).subscheme) =
      r.residueDegree (genericPoint (integralComponentAt z.val).subscheme) :=
    integralImageMap_residueDegree r _
  rw [hedeg] at HB
  change (incidenceTorPairing p (projection p ≫ p) h _
    (singleFiniteCorrespondence _ _ w hw
      ((cycle U F) z.val * (r.residueDegree
        (genericPoint (integralComponentAt z.val).subscheme) : ℤ)))).val = _
  rw [incidenceTorPairing_single, one_mul]
  change ((cycle U F) z.val * (r.residueDegree
    (genericPoint (integralComponentAt z.val).subscheme) : ℤ)) • _ = _
  rw [graphEndpoint_incidenceTorCorrespondence_eq_graphFiberPushforward p h c s w hw]
  exact HB.symm

omit [IsIntegral X] [IsAffine X] [IsSeparated p] [IsSeparated h] [Smooth p] [Smooth h]
  [IsProper q] [V.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ q)] in
/-- The source endpoint is cut on the unchanged original principal support and
its unchanged original projection to the parameter space. -/
theorem componentEndpoint_source_projection (z : support U F) :
    letI := isIntegral_integralComponentAt z.val
    let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
    integralImageMap r ≫
      ((integralComponentAt (imagePoint (projection p ≫ p) h q j U hU F hF g hg z)).subschemeι ≫
        pullback.fst (projection p ≫ p) h) =
      (integralComponentAt z.val).subschemeι ≫ q := by
  let := isIntegral_integralComponentAt z.val
  dsimp only
  let r := componentMap (projection p ≫ p) h q j U hU F hF g hg z
  have H := congrArg (fun a : (integralComponentAt z.val).subscheme ⟶
      pullback (projection p ≫ p) h => a ≫ pullback.fst (projection p ≫ p) h)
    (integralImageMap_inclusion r)
  exact (Category.assoc _ _ _).symm.trans
    (H.trans (componentMap_fst (projection p ≫ p) h q j U hU F hF g hg z))

/-- Native pairing sums all original signed component endpoint cycles, retaining
all coincident images without choosing a representative support. -/
theorem correspondence_graphPairing_eq_sum_endpointCycles (c : k) (s : genericPoints X) :
    letI := (cycle U F).finite_support.fintype
    (incidenceTorPairing p (projection p ≫ p) h
      (singleFiniteCorrespondence p (projection p ≫ p)
        (correspondenceGraphMap p (projection p ≫ p) (endpoint p c) (by simp) s.val)
        (isFiniteCorrespondencePoint_graphMap p (projection p ≫ p)
          (endpoint p c) (by simp) s) 1)
      (correspondence (projection p ≫ p) h q j U hU F hF g hg)).val =
      ∑ z : support U F, componentEndpointCycle p h q j U hU F hF g hg z c := by
  classical
  let := (cycle U F).finite_support.fintype
  unfold correspondence
  rw [map_sum]
  change (finiteCorrespondences p h).subtype (∑ z : support U F, _) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun z _ =>
    componentCorrespondence_graphPairing_eq_endpointCycle p h q j U hU F hF g hg z c s

/-- The whole original endpoint graph paired with the original signed principal
correspondence equals the sum of native whole source-support endpoint cycles.
This is literal cycle equality before any rational-equivalence quotient. -/
@[colib_tag "COL-1089", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/ProperPushforwardPrincipal/ResidueTrdeg.lean:87\
    -101"
  "ingredient" "Original residue-degree composition and degree-one immersion transport in the \
    fibre and pushforward comparison."]
theorem correspondence_endpointGraph_eq_sourceEndpointCycles (c : k) :
    let hX : (genericPoints X).Finite := by
      rw [genericPoints_eq_singleton]
      exact Set.finite_singleton _
    letI := (cycle U F).finite_support.fintype
    (incidenceTorPairing p (projection p ≫ p) h
      (graphCorrespondenceOfComponents p (projection p ≫ p) (endpoint p c) (by simp) hX)
      (correspondence (projection p ≫ p) h q j U hU F hF g hg)).val =
      ∑ z : support U F, componentEndpointCycle p h q j U hU F hF g hg z c := by
  classical
  dsimp only
  let hX : (genericPoints X).Finite := by
    rw [genericPoints_eq_singleton]
    exact Set.finite_singleton _
  let := hX.fintype
  let s : genericPoints X := ⟨genericPoint X, by
    rw [genericPoints_eq_singleton]
    exact Set.mem_singleton _⟩
  let : Unique (genericPoints X) :=
    { default := s
      uniq := fun t => Subtype.ext (by
        have ht := t.property
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using ht) }
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence,
    Fintype.sum_subsingleton _ s]
  exact correspondence_graphPairing_eq_sum_endpointCycles p h q j U hU F hF g hg c s

end Stacks.Chow.PrincipalBoundary
