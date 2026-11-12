/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.AmbientPrincipalSupportCuts
public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointStalkLength
public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointFiberMap
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.EndpointProjection
public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental

/-! # Original source endpoint cycles on the unchanged curve -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X C D : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : C ⟶ X) (c : k)

/-- The whole endpoint projection is inverse to the original scalar endpoint. -/
@[reassoc (attr := simp)]
theorem polynomialEndpointProjection_endpoint :
    polynomialEndpointProjection p q c ≫ endpoint (q ≫ p) c =
      pullback.snd (endpoint p c) (lineMap p q) := by
  let a := pullback.lift q (endpoint (q ≫ p) c) (endpoint_lineMap p q c).symm
  have ha : a ≫ polynomialEndpointProjection p q c = 𝟙 C := by
    simp only [a, polynomialEndpointProjection, pullback.lift_snd_assoc, endpoint_projection]
  have hai : a = inv (polynomialEndpointProjection p q c) := by
    apply (cancel_mono (polynomialEndpointProjection p q c)).mp
    rw [ha, IsIso.inv_hom_id]
  have : IsIso a := by rw [hai]; infer_instance
  apply (cancel_epi a).mp
  rw [← Category.assoc, ha, Category.id_comp]
  exact (pullback.lift_snd _ _ _).symm

/-- The original source endpoint maps to the original curve, not its finite image. -/
def sourceEndpointToCurve (i : D ⟶ parameterSpace (q ≫ p)) :
    pullback (endpoint p c) (i ≫ lineMap p q) ⟶ C :=
  polynomialEndpointMap p (lineMap p q) i c ≫ polynomialEndpointProjection p q c

/-- The source endpoint map keeps its original inclusion into the ambient product. -/
@[reassoc (attr := simp)]
theorem sourceEndpointToCurve_endpoint (i : D ⟶ parameterSpace (q ≫ p)) :
    sourceEndpointToCurve p q c i ≫ endpoint (q ≫ p) c =
      pullback.snd (endpoint p c) (i ≫ lineMap p q) ≫ i := by
  simp only [sourceEndpointToCurve, Category.assoc,
    polynomialEndpointProjection_endpoint, polynomialEndpointMap_snd]

instance (i : D ⟶ parameterSpace (q ≫ p)) [IsClosedImmersion i] :
    IsClosedImmersion (sourceEndpointToCurve p q c i) := by
  have : IsClosedImmersion (polynomialEndpointMap p (lineMap p q) i c) :=
    MorphismProperty.of_isPullback (polynomialEndpointMap_isPullback p (lineMap p q) i c)
      inferInstance
  unfold sourceEndpointToCurve
  infer_instance

/-- The whole source endpoint is Noetherian because it is an actual closed
subscheme of the original Noetherian curve. -/
theorem sourceEndpoint_isNoetherian [IsNoetherian C]
    (i : D ⟶ parameterSpace (q ≫ p)) [IsClosedImmersion i] :
    IsNoetherian (pullback (C := Scheme) (endpoint p c) (i ≫ lineMap p q)) :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
      (sourceEndpointToCurve p q c i)
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
      (sourceEndpointToCurve p q c i) }

/-- Every original whole source endpoint coefficient is the full literal cut on
its original integral support, with no replacement by a reduced endpoint. -/
theorem sourceEndpoint_fundamentalCycle_coefficient [IsNoetherian C]
    (z : parameterSpace (q ≫ p))
    (e : pullback (C := Scheme) (endpoint p c)
      ((integralComponentAt z).subschemeι ≫ lineMap p q)) :
    let i := (integralComponentAt z).subschemeι
    letI := sourceEndpoint_isNoetherian p q c i
    finiteCyclePushforward (sourceEndpointToCurve p q c i)
        (AlgebraicCycle.fundamentalCycle _) (sourceEndpointToCurve p q c i e) =
      principalSupportCutLength (parameterSpace (q ≫ p))
        (endpoint (q ≫ p) c (sourceEndpointToCurve p q c i e)) z
        (endpointEquation (q ≫ p) c) := by
  let i := (integralComponentAt z).subschemeι
  let E := pullback (endpoint p c) (i ≫ lineMap p q)
  let := sourceEndpoint_isNoetherian p q c i
  let d := pullback.snd (endpoint p c) (i ≫ lineMap p q) e
  have he : i d = endpoint (q ≫ p) c (sourceEndpointToCurve p q c i e) :=
    (congrArg (fun a => a e) (sourceEndpointToCurve_endpoint p q c i)).symm
  have hz : z ⤳ endpoint (q ≫ p) c (sourceEndpointToCurve p q c i e) := by
    apply specializes_iff_mem_closure.mpr
    rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨d, he⟩
  dsimp only
  rw [principalSupportCutLength_eq_at_point _ z hz d he,
    finiteCyclePushforward_apply_of_isClosedImmersion]
  have HL := polynomialEndpoint_stalk_length p (i ≫ lineMap p q) c e
  have heqn : PolynomialEndpointFiber.equation
      ((i ≫ lineMap p q) ≫ pullback.snd p (Spec.map
        (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c =
      i.appTop (endpointEquation (q ≫ p) c) := by
    rw [endpointEquation, ← PolynomialEndpointFiber.equation_comp]
    congr 1
    simp only [lineMap, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
  rw [heqn] at HL
  have HC : AlgebraicCycle.fundamentalCycle E e =
      ((Module.length (E.presheaf.stalk e) (E.presheaf.stalk e)).toNat : ℤ) := by
    by_cases h : e ∈ genericPoints E
    · exact AlgebraicCycle.fundamentalCycle_apply_generic E ⟨e, h⟩
    · have ht : Module.length (E.presheaf.stalk e) (E.presheaf.stalk e) = ⊤ := by
        by_contra hn
        exact h ((length_stalk_ne_top_iff_mem_genericPoints e).mp hn)
      rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem E e h, ht, ENat.toNat_top,
        Nat.cast_zero]
  exact HC.trans (congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) HL)

/-- The whole source endpoint meets exactly the original ambient support at the
literal scalar endpoint; closed pullback supplies every such point. -/
theorem sourceEndpointToCurve_range (z : parameterSpace (q ≫ p)) :
    Set.range (sourceEndpointToCurve p q c (integralComponentAt z).subschemeι) =
      {x : C | z ⤳ endpoint (q ≫ p) c x} := by
  let i := (integralComponentAt z).subschemeι
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    apply specializes_iff_mem_closure.mpr
    rw [← coe_support_integralComponentAt, ← Scheme.IdealSheafData.range_subschemeι]
    refine ⟨pullback.snd (endpoint p c) (i ≫ lineMap p q) e, ?_⟩
    exact (congrArg (fun a => a e) (sourceEndpointToCurve_endpoint p q c i)).symm
  · intro hx
    obtain ⟨d, hd⟩ := exists_integralComponentPointOfSpecializes
      (parameterSpace (q ≫ p)) (endpoint (q ≫ p) c x) z hx
    let y := inv (polynomialEndpointProjection p q c) x
    have hy : polynomialEndpointProjection p q c y = x := by
      change (inv (polynomialEndpointProjection p q c) ≫
        polynomialEndpointProjection p q c) x = x
      rw [IsIso.inv_hom_id]
      rfl
    have hsy : pullback.snd (endpoint p c) (lineMap p q) y = endpoint (q ≫ p) c x := by
      have H := congrArg (fun a => a y) (polynomialEndpointProjection_endpoint p q c)
      change endpoint (q ≫ p) c (polynomialEndpointProjection p q c y) = _ at H
      exact (H.symm.trans (congrArg (endpoint (q ≫ p) c) hy))
    obtain ⟨e, _, he⟩ := Scheme.exists_preimage_of_isPullback
      (polynomialEndpointMap_isPullback p (lineMap p q) i c) d y (hd.trans hsy.symm)
    refine ⟨e, ?_⟩
    change polynomialEndpointProjection p q c (polynomialEndpointMap p (lineMap p q) i c e) = x
    rw [he]
    exact hy

/-- At every original curve point, the whole source endpoint fundamental-cycle
pushforward has exactly the original ambient full support-cut coefficient. -/
theorem sourceEndpoint_fundamentalCycle_apply [IsNoetherian C]
    (z : parameterSpace (q ≫ p)) (x : C) :
    let i := (integralComponentAt z).subschemeι
    letI := sourceEndpoint_isNoetherian p q c i
    finiteCyclePushforward (sourceEndpointToCurve p q c i)
        (AlgebraicCycle.fundamentalCycle _) x =
      principalSupportCutLength (parameterSpace (q ≫ p))
        (endpoint (q ≫ p) c x) z (endpointEquation (q ≫ p) c) := by
  classical
  let i := (integralComponentAt z).subschemeι
  let := sourceEndpoint_isNoetherian p q c i
  dsimp only
  by_cases hx : x ∈ Set.range (sourceEndpointToCurve p q c i)
  · obtain ⟨e, rfl⟩ := hx
    exact sourceEndpoint_fundamentalCycle_coefficient p q c z e
  · have hs : ¬ z ⤳ endpoint (q ≫ p) c x := by
      rw [sourceEndpointToCurve_range] at hx
      exact hx
    rw [principalSupportCutLength, dite_eq_right hs]
    by_contra hn
    have hm : x ∈ (finiteCyclePushforward (sourceEndpointToCurve p q c i)
        (AlgebraicCycle.fundamentalCycle _)).support := hn
    obtain ⟨e, _, he⟩ := finiteCyclePushforward_support_subset _ _ hm
    exact hx ⟨e, he⟩

variable [IsNoetherian C] [IsIntegral (parameterSpace (q ≫ p))]
    [IsNoetherian (parameterSpace (q ≫ p))]

/-- The finite original signed principal support sum, on the unchanged original
curve, formed from the whole source endpoint fundamental cycles. -/
def signedSourceEndpointCycle (F : (parameterSpace (q ≫ p)).functionField) :
    AlgebraicCycle C ℤ := by
  classical
  let := (principalCycle (parameterSpace (q ≫ p)) F).finite_support.fintype
  exact ∑ z : (principalCycle (parameterSpace (q ≫ p)) F).support,
    let i := (integralComponentAt z.val).subschemeι
    letI := sourceEndpoint_isNoetherian p q c i
    (principalCycle (parameterSpace (q ≫ p)) F) z.val •
      finiteCyclePushforward (sourceEndpointToCurve p q c i)
        (AlgebraicCycle.fundamentalCycle _)

/-- Finite original signed support sums agree coefficientwise with their full
ambient support cuts. All actual source components and signs are retained. -/
@[colib_tag "COL-1097"]
theorem signedSourceEndpointCycle_apply
    (F : (parameterSpace (q ≫ p)).functionField) (x : C) :
    signedSourceEndpointCycle p q c F x =
      ∑ᶠ z ∈ principalSupportThrough (parameterSpace (q ≫ p)) (endpoint (q ≫ p) c x) F,
        (principalCycle (parameterSpace (q ≫ p)) F) z *
          principalSupportCutLength (parameterSpace (q ≫ p)) (endpoint (q ≫ p) c x) z
            (endpointEquation (q ≫ p) c) := by
  classical
  let P := parameterSpace (q ≫ p)
  let Z := principalCycle P F
  let := Z.finite_support.fintype
  have H : signedSourceEndpointCycle p q c F x =
      ∑ z : Z.support, Z z.val * principalSupportCutLength P
        (endpoint (q ≫ p) c x) z.val (endpointEquation (q ≫ p) c) := by
    unfold signedSourceEndpointCycle
    rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro z _
    change Z z.val * _ = _
    rw [sourceEndpoint_fundamentalCycle_apply]
  rw [H, ← finsum_eq_sum_of_fintype]
  trans ∑ᶠ z ∈ Z.support, Z z * principalSupportCutLength P
    (endpoint (q ≫ p) c x) z (endpointEquation (q ≫ p) c)
  · exact finsum_set_coe_eq_finsum_mem (f := fun z : P => Z z *
      principalSupportCutLength P (endpoint (q ≫ p) c x) z
        (endpointEquation (q ≫ p) c)) Z.support
  apply finsum_mem_inter_support_eq'
  intro z hz
  have hs : z ⤳ endpoint (q ≫ p) c x := by
    by_contra hn
    apply hz
    simp only [principalSupportCutLength, dite_eq_right hn, mul_zero]
  exact ⟨fun h => ⟨h, hs⟩, And.left⟩

end AlgebraicGeometry.PrincipalFamilyUnitOpen
