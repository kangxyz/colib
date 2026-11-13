/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Product
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor

/-!
# Common factors in signed finite section cuts

Cancellation of a common nonzero factor holds for native zero cycles on the
original support. The four cuts all map into one whole finite product cut.
The common finite cut carries the signed equality to the actual correspondence
by its original source and target projections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme AffineLineFiber

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
  [IsIntegral P] [IsNoetherian P]
  (p : P ⟶ X.left) (q : P ⟶ Y.left) (h : p ≫ X.hom = q ≫ Y.hom)

set_option quotPrecheck false in
local notation "b" => (p ≫ X.hom)
set_option quotPrecheck false in
local notation "Z₀(" s ")" => fiber (sectionToAffineLine b s) (0 : k)
set_option quotPrecheck false in
local notation "i₀(" s ")" => inclusion (sectionToAffineLine b s) (0 : k)
set_option quotPrecheck false in
local notation "p₀(" s ")" => i₀(s) ≫ p

/-- The signed relative section cut cancels a shared nonzero factor on the
original integral support. -/
theorem signedSectionCutCorrespondence_mul_common [IsAffineHom p] [LocallyOfFiniteType p]
    (s t c : Γ(P, ⊤)) (hs : s ≠ 0) (ht : t ≠ 0) (hc : c ≠ 0)
    [IsFinite p₀(s)] [IsFinite p₀(t)] [IsFinite p₀(c)]
    [IsFinite p₀(s * c)] [IsFinite p₀(t * c)]
    (hsg : ∀ a : genericPoints Z₀(s), p₀(s) a.val ∈ genericPoints X.left)
    (htg : ∀ a : genericPoints Z₀(t), p₀(t) a.val ∈ genericPoints X.left)
    (hscg : ∀ a : genericPoints Z₀(s * c), p₀(s * c) a.val ∈ genericPoints X.left)
    (htcg : ∀ a : genericPoints Z₀(t * c), p₀(t * c) a.val ∈ genericPoints X.left) :
    signedSectionCutCorrespondence p q h (s * c) (t * c) hscg htcg =
      signedSectionCutCorrespondence p q h s t hsg htg := by
  let : Nonempty (⊤ : P.Opens) := ⟨⟨genericPoint P, by trivial⟩⟩
  let d := s * t * c
  let : IsFinite p₀(s * t) := isFinite_sectionZero_mul b p s t
  let : IsFinite p₀(d) := isFinite_sectionZero_mul b p (s * t) c
  let z (a : Γ(P, ⊤)) (ha : a ∣ d) := sectionZeroInclusionOfDvd b a d ha
  let C (a : Γ(P, ⊤)) (ha : a ∣ d) : AlgebraicCycle Z₀(d) ℤ :=
    finiteCyclePushforward (z a ha) (AlgebraicCycle.fundamentalCycle Z₀(a))
  have hz (a : Γ(P, ⊤)) (ha : a ∣ d) : z a ha ≫ i₀(d) = i₀(a) :=
    sectionZeroInclusionOfDvd_inclusion b a d ha
  have hC (a : Γ(P, ⊤)) (ha : a ∣ d) :
      finiteCyclePushforward (i₀(d)) (C a ha) = sectionZeroCycle b a := by
    simp only [C, finiteCyclePushforward_comp_apply, hz, sectionZeroCycle]
  have hd₁ : s ∣ d := ⟨t * c, by simp [d, mul_assoc]⟩
  have hd₂ : t ∣ d := ⟨s * c, by simp [d, mul_left_comm, mul_assoc]⟩
  have hd₃ : s * c ∣ d := ⟨t, by simp [d, mul_assoc, mul_comm c t]⟩
  have hd₄ : t * c ∣ d := ⟨s, by simp [d, mul_comm, mul_left_comm]⟩
  have heq : C (s * c) hd₃ - C (t * c) hd₄ = C s hd₁ - C t hd₂ := by
    apply finiteCyclePushforward_injective_of_isClosedImmersion (i₀(d))
    simp only [map_sub, hC]
    rw [sectionZeroCycle_sub_eq_principalCycle b _ _ (mul_ne_zero hs hc) (mul_ne_zero ht hc),
      sectionZeroCycle_sub_eq_principalCycle b s t hs ht]
    congr 1
    change P.germToFunctionField ⊤ (s * c) / P.germToFunctionField ⊤ (t * c) =
      P.germToFunctionField ⊤ s / P.germToFunctionField ⊤ t
    rw [map_mul, map_mul]
    exact mul_div_mul_right _ _
      ((map_ne_zero_iff _ (P.germToFunctionField_injective ⊤)).mpr hc)
  let m := sectionCutSupportMap p q h d
  have hm (a : Γ(P, ⊤)) (ha : a ∣ d) [IsFinite p₀(a)] :
      z a ha ≫ m = sectionCutSupportMap p q h a := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, z, m, sectionCutSupportMap_fst, sectionCutSupportMap_snd,
        sectionZeroInclusionOfDvd_inclusion_assoc]
  apply Subtype.ext
  have he := congrArg (finiteCyclePushforward m) heq
  change (sectionCutCorrespondence p q h (s * c) hscg).val -
      (sectionCutCorrespondence p q h (t * c) htcg).val =
    (sectionCutCorrespondence p q h s hsg).val - (sectionCutCorrespondence p q h t htg).val
  let : IsNoetherian Z₀(s) := isNoetherian_of_finiteType_of_isNoetherian (i₀(s))
  let : IsNoetherian Z₀(t) := isNoetherian_of_finiteType_of_isNoetherian (i₀(t))
  let : IsNoetherian Z₀(s * c) := isNoetherian_of_finiteType_of_isNoetherian (i₀(s * c))
  let : IsNoetherian Z₀(t * c) := isNoetherian_of_finiteType_of_isNoetherian (i₀(t * c))
  simp only [sectionCutCorrespondence_val]
  simpa only [C, map_sub, finiteCyclePushforward_comp_apply, hm] using he

end AlgebraicGeometry.Cor
