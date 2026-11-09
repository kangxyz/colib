/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.GraphPushforward
public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.IncidencePairing

/-!
# Čech contraction through an actual common closed support

Whole incidence cycles retain their original signed Tor coefficients in a common
finite support. The proven support pairing supplies both Čech graph composites,
and the graph-pushforward theorem identifies the third composite with the same
cycle on the common support. Native closed-immersion pushforward is injective,
so a finite signed sum with zero target graph composite has zero second Čech
projection. Its first-minus-second boundary is the original sum.

The final incidence-family theorem derives all three cycle identities from
literal scheme maps. It does not assume a pairing comparison or local exactness.
Every surviving support-component point of the boundary witness lifts to one of
the original incidence schemes. Neither those schemes nor the common support
are replaced by their reductions. The existence of suitable maps on an actual
Nisnevich neighborhood remains a separate geometric step.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Cech/Contraction.lean`.
Native `AlgebraicCycle`, the actual incidence Tor pairing, and finite pushforward
replace the former custom integral-cycle and generator presentations.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] isIntegral_integralComponentAt

universe u v

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {T X Y V : Scheme.SmoothSite (Spec (.of k))}

/-- Literal finite factorizations of one whole incidence give both Čech projections
and its target graph composite, all from the exact same original Tor cycle. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/Contraction.lean: \
exists_cech_incidence_pairing_over_common_support_with_point_lift"
  "adaptation" "three native cycle identities from whole-support maps, retaining original \
signed Tor weights and point lifts"]
theorem exists_cech_incidence_pairing_over_common_support_with_point_lift
    (a : pullback (C := Scheme) T.hom X.hom) (b : pullback (C := Scheme) X.hom V.hom)
    (ha : IsFiniteCorrespondencePoint T.hom X.hom a)
    (hb : IsFiniteCorrespondencePoint X.hom V.hom b)
    (q : V ⟶ Y) [Etale q.left] (C : Scheme.{u})
    (r : correspondenceIncidence T.hom X.hom V.hom a b ⟶ C) [IsFinite r]
    (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsFinite j]
    (hsrc : s ≫ pullback.fst T.hom V.hom = j ≫ pullback.fst T.hom Y.hom)
    (htgt : s ≫ pullback.snd T.hom V.hom ≫ q.left = j ≫ pullback.snd T.hom Y.hom)
    (hrsource : r ≫ s ≫ pullback.fst T.hom V.hom =
      correspondenceIncidenceLeft T.hom X.hom V.hom a b)
    (hrtarget : r ≫ j ≫ pullback.snd T.hom Y.hom =
      correspondenceIncidenceRight T.hom X.hom V.hom a b ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) =
        incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward s
          (finiteCyclePushforward r (incidenceTorCycle T.hom X.hom V.hom a b hb)) ∧
      ((incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb : Cor.mk T ⟶ Cor.mk V) ≫
        (graphFunctor k).map q).val =
        finiteCyclePushforward j
          (finiteCyclePushforward r (incidenceTorCycle T.hom X.hom V.hom a b hb)) ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme,
        ∃ w : correspondenceIncidence T.hom X.hom V.hom a b,
          correspondenceIncidenceLeft T.hom X.hom V.hom a b w =
            ((integralComponentAt v).subschemeι ≫
              pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom) z ∧
          correspondenceIncidenceRight T.hom X.hom V.hom a b w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackFst q q).left) z ∧
          ((r ≫ s) ≫ pullback.snd T.hom V.hom) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackSnd q q).left) z := by
  obtain ⟨β, h₁, h₂, hpoint⟩ := exists_cech_pairing_of_incidenceTor_with_point_lift
    k a b ha hb (r ≫ s) q
    (by rw [correspondenceIncidenceMap_fst, Category.assoc, hrsource])
    (by
      calc
        _ = correspondenceIncidenceRight T.hom X.hom V.hom a b ≫ q.left := by
          rw [← Category.assoc, correspondenceIncidenceMap_snd]
        _ = _ := by
          simpa only [Category.assoc] using
            ((congrArg (fun f => r ≫ f) htgt).trans hrtarget).symm)
  refine ⟨β, h₁, ?_, ?_, hpoint⟩
  · simpa only [finiteCyclePushforward_comp_apply] using h₂
  · have h := incidenceTorCorrespondence_comp_graph_val k a b ha hb q (r ≫ j)
      (by rw [Category.assoc, ← hsrc, hrsource])
      (by rw [Category.assoc, hrtarget])
    simpa only [finiteCyclePushforward_comp_apply] using h

/-- The same common-support construction, retaining all three exact cycle identities. -/
theorem exists_cech_incidence_pairing_over_common_support
    (a : pullback (C := Scheme) T.hom X.hom) (b : pullback (C := Scheme) X.hom V.hom)
    (ha : IsFiniteCorrespondencePoint T.hom X.hom a)
    (hb : IsFiniteCorrespondencePoint X.hom V.hom b)
    (q : V ⟶ Y) [Etale q.left] (C : Scheme.{u})
    (r : correspondenceIncidence T.hom X.hom V.hom a b ⟶ C) [IsFinite r]
    (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsFinite j]
    (hsrc : s ≫ pullback.fst T.hom V.hom = j ≫ pullback.fst T.hom Y.hom)
    (htgt : s ≫ pullback.snd T.hom V.hom ≫ q.left = j ≫ pullback.snd T.hom Y.hom)
    (hrsource : r ≫ s ≫ pullback.fst T.hom V.hom =
      correspondenceIncidenceLeft T.hom X.hom V.hom a b)
    (hrtarget : r ≫ j ≫ pullback.snd T.hom Y.hom =
      correspondenceIncidenceRight T.hom X.hom V.hom a b ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) =
        incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward s
          (finiteCyclePushforward r (incidenceTorCycle T.hom X.hom V.hom a b hb)) ∧
      ((incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb : Cor.mk T ⟶ Cor.mk V) ≫
        (graphFunctor k).map q).val =
        finiteCyclePushforward j
          (finiteCyclePushforward r (incidenceTorCycle T.hom X.hom V.hom a b hb)) := by
  obtain ⟨β, h₁, h₂, h₃, _⟩ :=
    exists_cech_incidence_pairing_over_common_support_with_point_lift
      k a b ha hb q C r s j hsrc htgt hrsource hrtarget
  exact ⟨β, h₁, h₂, h₃⟩

/-- Additive assembly of a finite signed presentation through an actual common
closed support. The concrete incidence-family endpoint below supplies these
three pairing identities from scheme maps, rather than assuming them. -/
theorem exists_cech_boundary_of_finite_presentation_with_point_property
    {I : Type v} [Fintype I] (α : Cor.mk T ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (C : Scheme.{u}) (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsClosedImmersion j]
    (γ : I → (Cor.mk T ⟶ Cor.mk V)) (δ : I → AlgebraicCycle C ℤ) (n : I → ℤ)
    (Q : ∀ v : pullback (C := Scheme) T.hom (Scheme.SmoothSite.etalePullback q q).hom,
      (integralComponentAt v).subscheme → Prop)
    (hα : ∑ i, n i • γ i = α)
    (hpair : ∀ i, ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) = γ i ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward s (δ i) ∧
      (γ i ≫ (graphFunctor k).map q).val = finiteCyclePushforward j (δ i) ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme, Q v z)
    (hzero : α ≫ (graphFunctor k).map q = 0) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) = α ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme, Q v z := by
  classical
  choose β hfirst hsecond hthird hpoint using hpair
  let Γ₁ : Cor.mk (Scheme.SmoothSite.etalePullback q q) ⟶ Cor.mk V :=
    (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q)
  let Γ₂ : Cor.mk (Scheme.SmoothSite.etalePullback q q) ⟶ Cor.mk V :=
    (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)
  let Γq : Cor.mk V ⟶ Cor.mk Y := (graphFunctor k).map q
  change ∀ i, β i ≫ Γ₁ = γ i at hfirst
  change ∀ i, (β i ≫ Γ₂).val = finiteCyclePushforward s (δ i) at hsecond
  change ∀ i, (γ i ≫ Γq).val = finiteCyclePushforward j (δ i) at hthird
  change α ≫ Γq = 0 at hzero
  let B : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q) := ∑ i, n i • β i
  let Δ : AlgebraicCycle C ℤ := ∑ i, n i • δ i
  let vV : (Cor.mk T ⟶ Cor.mk V) →+ AlgebraicCycle (pullback T.hom V.hom) ℤ :=
    (finiteCorrespondences T.hom V.hom).subtype
  let vY : (Cor.mk T ⟶ Cor.mk Y) →+ AlgebraicCycle (pullback T.hom Y.hom) ℤ :=
    (finiteCorrespondences T.hom Y.hom).subtype
  have hsecond' (i : I) :
      vV (β i ≫ Γ₂) =
        finiteCyclePushforward s (δ i) := hsecond i
  have hthird' (i : I) : vY (γ i ≫ Γq) =
      finiteCyclePushforward j (δ i) := hthird i
  have hbfirst : B ≫ Γ₁ = α := by
    dsimp only [B]
    rw [Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp, hfirst]
    exact hα
  have hΔ : finiteCyclePushforward j Δ = 0 := by
    calc
      _ = vY ((∑ i, n i • γ i) ≫ Γq) := by
        dsimp only [Δ]
        rw [Preadditive.sum_comp]
        simp only [Preadditive.zsmul_comp, map_sum, map_zsmul, hthird']
      _ = 0 := by rw [hα, hzero, map_zero]
  have hΔzero : Δ = 0 := finiteCyclePushforward_injective_of_isClosedImmersion j
    (hΔ.trans (map_zero _).symm)
  have hbsecond : B ≫ Γ₂ = 0 := by
    apply Subtype.ext
    change vV (B ≫ Γ₂) = vV 0
    calc
      _ = finiteCyclePushforward s Δ := by
        dsimp only [B, Δ]
        rw [Preadditive.sum_comp]
        simp only [Preadditive.zsmul_comp, map_sum, map_zsmul, hsecond']
      _ = _ := by rw [hΔzero, map_zero, map_zero]
  refine ⟨B, ?_, ?_⟩
  · change B ≫ Γ₁ - B ≫ Γ₂ = α
    rw [hbfirst, hbsecond, sub_zero]
  · intro v hv z
    have hval : B.val = ∑ i, n i • (β i).val := by
      change (finiteCorrespondences T.hom (Scheme.SmoothSite.etalePullback q q).hom).subtype
        (∑ i, n i • β i) = _
      simp only [map_sum, map_zsmul]
      rfl
    have hsum : (∑ i, n i • (β i).val v) ≠ 0 := by
      rw [hval] at hv
      simpa only [coe_sum, Finset.sum_apply, coe_zsmul, Pi.smul_apply] using hv
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    have hi' : (β i).val v ≠ 0 := by
      intro heq
      apply hi
      rw [heq, smul_zero]
    exact hpoint i v hi' z

/-- The same signed contraction without an additional point predicate. -/
theorem exists_cech_boundary_of_finite_presentation
    {I : Type v} [Fintype I] (α : Cor.mk T ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (C : Scheme.{u}) (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsClosedImmersion j]
    (γ : I → (Cor.mk T ⟶ Cor.mk V)) (δ : I → AlgebraicCycle C ℤ) (n : I → ℤ)
    (hα : ∑ i, n i • γ i = α)
    (hpair : ∀ i, ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) = γ i ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward s (δ i) ∧
      (γ i ≫ (graphFunctor k).map q).val = finiteCyclePushforward j (δ i))
    (hzero : α ≫ (graphFunctor k).map q = 0) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) = α := by
  have hpair' (i : I) : ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) = γ i ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward s (δ i) ∧
      (γ i ≫ (graphFunctor k).map q).val = finiteCyclePushforward j (δ i) ∧
      ∀ v, β.val v ≠ 0 → ∀ _z : (integralComponentAt v).subscheme, True := by
    obtain ⟨β, h₁, h₂, h₃⟩ := hpair i
    exact ⟨β, h₁, h₂, h₃, fun _ _ _ => trivial⟩
  obtain ⟨β, hβ, _⟩ := exists_cech_boundary_of_finite_presentation_with_point_property
    k α q C s j γ δ n (fun _ _ => True) hα hpair' hzero
  exact ⟨β, hβ⟩

/-- A concrete signed finite family of original incidence correspondences contracts
through literal maps to one closed support. All pairing and graph identities are
proved above; the caller supplies only the scheme maps and their projection equations. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/Contraction.lean: common-support pairing and finite signed \
contraction"
  "adaptation" "concrete native incidence-family application, with all pairing hypotheses \
discharged by actual maps"]
theorem exists_cech_boundary_of_incidence_presentation_with_point_lift
    {I : Type v} [Fintype I] (α : Cor.mk T ⟶ Cor.mk V)
    (a : I → pullback (C := Scheme) T.hom X.hom) (b : I → pullback (C := Scheme) X.hom V.hom)
    (ha : ∀ i, IsFiniteCorrespondencePoint T.hom X.hom (a i))
    (hb : ∀ i, IsFiniteCorrespondencePoint X.hom V.hom (b i))
    (n : I → ℤ) (q : V ⟶ Y) [Etale q.left] (C : Scheme.{u})
    (r : ∀ i, correspondenceIncidence T.hom X.hom V.hom (a i) (b i) ⟶ C)
    [∀ i, IsFinite (r i)]
    (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsClosedImmersion j]
    (hsrc : s ≫ pullback.fst T.hom V.hom = j ≫ pullback.fst T.hom Y.hom)
    (htgt : s ≫ pullback.snd T.hom V.hom ≫ q.left = j ≫ pullback.snd T.hom Y.hom)
    (hrsource : ∀ i, r i ≫ s ≫ pullback.fst T.hom V.hom =
      correspondenceIncidenceLeft T.hom X.hom V.hom (a i) (b i))
    (hrtarget : ∀ i, r i ≫ j ≫ pullback.snd T.hom Y.hom =
      correspondenceIncidenceRight T.hom X.hom V.hom (a i) (b i) ≫ q.left)
    (hα : ∑ i, n i • incidenceTorCorrespondence T.hom X.hom V.hom
      (a i) (b i) (ha i) (hb i) = α)
    (hzero : α ≫ (graphFunctor k).map q = 0) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) = α ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme,
        ∃ i, ∃ w : correspondenceIncidence T.hom X.hom V.hom (a i) (b i),
          correspondenceIncidenceLeft T.hom X.hom V.hom (a i) (b i) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom) z ∧
          correspondenceIncidenceRight T.hom X.hom V.hom (a i) (b i) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackFst q q).left) z ∧
          ((r i ≫ s) ≫ pullback.snd T.hom V.hom) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackSnd q q).left) z := by
  apply exists_cech_boundary_of_finite_presentation_with_point_property k α q C s j
    (fun i => incidenceTorCorrespondence T.hom X.hom V.hom (a i) (b i) (ha i) (hb i))
    (fun i => finiteCyclePushforward (r i) (incidenceTorCycle T.hom X.hom V.hom
      (a i) (b i) (hb i))) n
    (fun v z => ∃ i, ∃ w : correspondenceIncidence T.hom X.hom V.hom (a i) (b i),
      correspondenceIncidenceLeft T.hom X.hom V.hom (a i) (b i) w =
        ((integralComponentAt v).subschemeι ≫
          pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom) z ∧
      correspondenceIncidenceRight T.hom X.hom V.hom (a i) (b i) w =
        ((integralComponentAt v).subschemeι ≫
          pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
          (Scheme.SmoothSite.etalePullbackFst q q).left) z ∧
      ((r i ≫ s) ≫ pullback.snd T.hom V.hom) w =
        ((integralComponentAt v).subschemeι ≫
          pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
          (Scheme.SmoothSite.etalePullbackSnd q q).left) z) hα ?_ hzero
  intro i
  obtain ⟨β, h₁, h₂, h₃, hpoint⟩ :=
    exists_cech_incidence_pairing_over_common_support_with_point_lift
      k (a i) (b i) (ha i) (hb i) q C (r i) s j hsrc htgt (hrsource i) (hrtarget i)
  refine ⟨β, h₁, h₂, h₃, ?_⟩
  intro v hv z
  obtain ⟨w, hw⟩ := hpoint v hv z
  exact ⟨i, w, hw⟩

end AlgebraicGeometry.Cor
