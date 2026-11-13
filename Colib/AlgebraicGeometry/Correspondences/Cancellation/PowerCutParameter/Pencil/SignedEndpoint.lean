/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Admissibility
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.Correspondence
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.Face
import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.GenericImage
import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.Pencil.CommonFactor
import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents

/-!
# The signed endpoints of the power-cut pencil

The scalar zero face gives the second power cut, and the scalar one face
gives the first. The common denominator factor cancels in the actual
finite-correspondence group after specializing both full zero schemes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction AffineLineFiber

private theorem sectionCutCorrespondence_congr_section {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}}
    (p : P ⟶ X.left) (q : P ⟶ Y.left) (h : p ≫ X.hom = q ≫ Y.hom)
    {s t : Γ(P, ⊤)} (e : s = t)
    [IsFinite (inclusion (sectionToAffineLine (p ≫ X.hom) s) 0 ≫ p)]
    [IsFinite (inclusion (sectionToAffineLine (p ≫ X.hom) t) 0 ≫ p)]
    (hs : ∀ x : genericPoints (fiber (sectionToAffineLine (p ≫ X.hom) s) 0),
      (inclusion (sectionToAffineLine (p ≫ X.hom) s) 0 ≫ p) x.val ∈ genericPoints X.left)
    (ht : ∀ x : genericPoints (fiber (sectionToAffineLine (p ≫ X.hom) t) 0),
      (inclusion (sectionToAffineLine (p ≫ X.hom) t) 0 ≫ p) x.val ∈ genericPoints X.left) :
    sectionCutCorrespondence p q h s hs = sectionCutCorrespondence p q h t ht := by
  subst t
  rfl

variable (k : Type u) [Field k] (X Y : SmoothSite (Spec (.of k)))
  (z : torusPowerCutAmbient k X Y)

set_option quotPrecheck false
local notation "Sₖ" => Spec (.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "A₁" => additiveGroupObject Sₖ
local notation "XG" => (product X T)
local notation "YG" => (product Y T)
local notation "V" => (torusPowerCutRetainedTarget k Y)
local notation "B" => (product X A₁)
local notation "j" => (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subschemeι
local notation "Pₜ" => (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subscheme
local notation "g" => (j ≫ pullback.fst (XG).hom (YG).hom)
local notation "g'" => torusPowerCutTarget k X Y z
local notation "b" => (g ≫ (XG).hom)
local notation "W" => pullback (C := Scheme) b (A₁).hom
local notation "p" => torusPowerCutPencilProjection k g
local notation "p₀" => torusSupportBaseProjection k g
local notation "qᵧ" => torusSupportBaseProjection k g'
local notation "r" => (j ≫ (torusPowerCutAmbientSchemeIso k X Y).hom)
local notation "J" => torusPowerCutPencilRetainedSupportMap k j
local notation "v" => (J ≫ pullback.snd (B).hom (V).hom)
local notation "v₀" => (r ≫ pullback.snd X.hom (V).hom)
local notation "d" => (productFst YG T ≫ productFst Y T)
local notation "t" => torusSupportCoordinate k g
local notation "u₀" => torusSupportCoordinate k g'
local notation "σ(" a ")" => nativeAdditiveParameterSection b a
local notation "φ(" a ")" => nativeAffineSection (.of k) X a
local notation "N(" n ")" => torusPowerCutNumerator t n
local notation "D(" n ")" => torusPowerCutDenominator t u₀ n
local notation "Z₀(" s ")" => fiber (sectionToAffineLine (p₀ ≫ X.hom) s) 0
local notation "i₀(" s ")" => inclusion (sectionToAffineLine (p₀ ≫ X.hom) s) 0
local notation "Z(" s ")" => fiber (sectionToAffineLine (p ≫ (B).hom) s) 0
local notation "i(" s ")" => inclusion (sectionToAffineLine (p ≫ (B).hom) s) 0
set_option quotPrecheck true

private theorem graph_comp_torusPowerCutPencilPrime_of_commonFactor
    (hz : IsFiniteCorrespondencePoint (XG).hom (YG).hom z)
    (m n ℓ : ℕ) (hℓ : TorusPowerCutAdmissibleAt k X Y z ℓ)
    (hP : TorusPowerCutPencilAdmissibleAt k X Y z u₀ (m + 1) (n + 1))
    (a : k) (c : Γ(Pₜ, ⊤)) (hc : IsFinite (i₀(c) ≫ p₀))
    (hN : (σ(a)).appTop (torusPowerCutPencilNumerator k g u₀ (m + 1) (n + 1)) = N(ℓ) * c)
    (hD : (σ(a)).appTop (torusPowerCutPencilDenominator k g u₀ (m + 1) (n + 1)) = D(ℓ) * c) :
    (graphFunctor k).map (φ(a)) ≫ torusPowerCutPencilPrime k X Y z u₀ (m + 1) (n + 1) hP =
      torusPowerCutPrime k X Y z ℓ hℓ := by
  let : IsFinite g := hz.1
  let : IsIntegral Pₜ := isIntegral_integralComponentAt z
  let : IsNoetherian (torusPowerCutAmbient k X Y) :=
    SmoothSite.isNoetherian_overField k (product XG YG)
  let : IsNoetherian Pₜ := isNoetherian_of_finiteType_of_isNoetherian j
  let τ := multiplicativeGroupBaseChange Sₖ ↘ Sₖ
  let g₀ : Pₜ ⟶ pullback X.hom τ := g
  let : IsFinite g₀ := hz.1
  let : IsAffineHom τ := by
    let qℤ := multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))
    let : IsAffineHom qℤ := by
      change IsAffineHom (Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.C : ULift.{u} ℤ →+* LaurentPolynomial (ULift.{u} ℤ))))
      infer_instance
    change IsAffineHom (pullback.snd qℤ (specULiftZIsTerminal.from Sₖ))
    infer_instance
  let : IsAffineHom (pullback.fst X.hom τ) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) X.hom τ inferInstance
  let : IsAffineHom p₀ := by
    change IsAffineHom (g₀ ≫ pullback.fst X.hom τ)
    exact MorphismProperty.comp_mem @IsAffineHom _ _ inferInstance inferInstance
  let : LocallyOfFiniteType τ := inferInstanceAs (LocallyOfFiniteType (T).hom)
  let : LocallyOfFiniteType (pullback.fst X.hom τ) :=
    MorphismProperty.pullback_fst (P := @LocallyOfFiniteType) X.hom τ inferInstance
  let : LocallyOfFiniteType p₀ := by
    change LocallyOfFiniteType (g₀ ≫ pullback.fst X.hom τ)
    exact MorphismProperty.comp_mem @LocallyOfFiniteType _ _ inferInstance inferInstance
  let f₀ : X.left ⟶ Sₖ := X.hom
  let : Smooth f₀ := inferInstanceAs (Smooth X.hom)
  have hgen (s : Γ(Pₜ, ⊤)) (hs : IsFinite (i₀(s) ≫ p₀)) :
      s ≠ 0 ∧ ∀ x : genericPoints Z₀(s), (i₀(s) ≫ p₀) x.val ∈ genericPoints X.left :=
    NativeTorusPolynomial.sectionCut_nonzero_and_generic_of_finite_torus_component f₀ g hz.2 s hs
  let : IsFinite (i₀(N(ℓ)) ≫ p₀) := hℓ.numerator_finite
  let : IsFinite (i₀(D(ℓ)) ≫ p₀) := hℓ.denominator_finite
  let : IsFinite (i₀(c) ≫ p₀) := hc
  let : IsFinite (i₀(N(ℓ) * c) ≫ p₀) := isFinite_sectionZero_mul (p₀ ≫ X.hom) p₀ (N(ℓ)) c
  let : IsFinite (i₀(D(ℓ) * c) ≫ p₀) := isFinite_sectionZero_mul (p₀ ≫ X.hom) p₀ (D(ℓ)) c
  let s := torusPowerCutPencilNumerator k g u₀ (m + 1) (n + 1)
  let t' := torusPowerCutPencilDenominator k g u₀ (m + 1) (n + 1)
  let : IsFinite (i(s) ≫ p) := by
    rw [torusPowerCutPencilProjection_over]
    exact hP.numerator_finite
  let : IsFinite (i(t') ≫ p) := by
    rw [torusPowerCutPencilProjection_over]
    exact hP.denominator_finite
  let : IsFinite (i₀((σ(a)).appTop s) ≫ p₀) := by
    rw [show (σ(a)).appTop s = N(ℓ) * c from hN]
    infer_instance
  let : IsFinite (i₀((σ(a)).appTop t') ≫ p₀) := by
    rw [show (σ(a)).appTop t' = D(ℓ) * c from hD]
    infer_instance
  have hs : ∀ x : genericPoints Z(s), (i(s) ≫ p) x.val ∈ genericPoints (B).left := by
    rw [torusPowerCutPencilProjection_over]
    exact hP.numerator_generic
  have ht : ∀ x : genericPoints Z(t'), (i(t') ≫ p) x.val ∈ genericPoints (B).left := by
    rw [torusPowerCutPencilProjection_over]
    exact hP.denominator_generic
  have hsa := (hgen ((σ(a)).appTop s) inferInstance).2
  have hta := (hgen ((σ(a)).appTop t') inferInstance).2
  have hsc := (hgen (N(ℓ) * c) inferInstance).2
  have htc := (hgen (D(ℓ) * c) inferInstance).2
  let h₀ := torusPowerCutPencilRetainedEndpoint_over k j
  let hW := torusPowerCutPencilRetainedSupport_over k j
  have hNs := graph_comp_torusPowerCutPencilSectionCut k j a s hP.numerator_nonzero hs hsa
  have hDt := graph_comp_torusPowerCutPencilSectionCut k j a t' hP.denominator_nonzero ht hta
  have hNcut := sectionCutCorrespondence_congr_section p₀ v₀ h₀ hN hsa hsc
  have hDcut := sectionCutCorrespondence_congr_section p₀ v₀ h₀ hD hta htc
  have hcancel := signedSectionCutCorrespondence_mul_common p₀ v₀ h₀ (N(ℓ)) (D(ℓ)) c
    (hgen _ hℓ.numerator_finite).1 (hgen _ hℓ.denominator_finite).1 (hgen _ hc).1
    hℓ.numerator_generic hℓ.denominator_generic hsc htc
  have hforget : v₀ ≫ (d).left = qᵧ := by
    have h := congrArg (fun f => f.left) (torusPowerCutAmbientIso_hom_target k X Y)
    change (torusPowerCutAmbientIso k X Y).hom.left ≫ (productSnd X V).left ≫
      (productFst YG T).left = (productSnd XG YG).left at h
    have htarget : r ≫ (productSnd X V).left ≫ (productFst YG T).left = g' :=
      (Category.assoc _ _ _).trans (congrArg (j ≫ ·) h)
    change (r ≫ (productSnd X V).left) ≫ (productFst YG T).left ≫ (productFst Y T).left =
      g' ≫ (productFst Y T).left
    simpa only [Category.assoc] using congrArg (· ≫ (productFst Y T).left) htarget
  change (graphFunctor k).map (φ(a)) ≫
    (signedSectionCutCorrespondence (X := B) (Y := V) (P := W) p v hW s t' hs ht ≫
      (graphFunctor k).map d) = _
  rw [← Category.assoc, signedSectionCutCorrespondence, Preadditive.comp_sub,
    hNs, hDt, hNcut, hDcut]
  change signedSectionCutCorrespondence p₀ v₀ h₀ (N(ℓ) * c) (D(ℓ) * c) hsc htc ≫
    (graphFunctor k).map d = _
  rw [hcancel, signedSectionCutCorrespondence_comp_graph]
  have hcongr (q₁ q₂ : Pₜ ⟶ Y.left) (he : q₁ = q₂)
      (h₁ : p₀ ≫ X.hom = q₁ ≫ Y.hom) (h₂ : p₀ ≫ X.hom = q₂ ≫ Y.hom) :
      signedSectionCutCorrespondence p₀ q₁ h₁ (N(ℓ)) (D(ℓ))
        hℓ.numerator_generic hℓ.denominator_generic =
      signedSectionCutCorrespondence p₀ q₂ h₂ (N(ℓ)) (D(ℓ))
        hℓ.numerator_generic hℓ.denominator_generic := by
    subst q₂
    rfl
  exact hcongr _ _ hforget _ _

/-- The two graph faces of the literal pencil are the original signed power cuts. -/
theorem torusPowerCutPencilPrime_endpoints
    (hz : IsFiniteCorrespondencePoint (XG).hom (YG).hom z)
    (m n : ℕ) (hm : TorusPowerCutAdmissibleAt k X Y z m)
    (hn : TorusPowerCutAdmissibleAt k X Y z n)
    (hP : TorusPowerCutPencilAdmissibleAt k X Y z u₀ (m + 1) (n + 1)) :
    (graphFunctor k).map (φ(0)) ≫ torusPowerCutPencilPrime k X Y z u₀ (m + 1) (n + 1) hP =
      torusPowerCutPrime k X Y z n hn ∧
    (graphFunctor k).map (φ(1)) ≫ torusPowerCutPencilPrime k X Y z u₀ (m + 1) (n + 1) hP =
      torusPowerCutPrime k X Y z m hm := by
  refine ⟨graph_comp_torusPowerCutPencilPrime_of_commonFactor k X Y z hz m n n hn hP 0
    (D(m)) hm.denominator_finite ?_ ?_,
    graph_comp_torusPowerCutPencilPrime_of_commonFactor k X Y z hz m n m hm hP 1
      (D(n)) hn.denominator_finite ?_ ?_⟩
  · exact torusPowerCutPencilNumerator_at_zero k g u₀ (m + 1) (n + 1)
  · exact (torusPowerCutPencilDenominator_at k g u₀ (m + 1) (n + 1) 0).trans (mul_comm _ _)
  · exact torusPowerCutPencilNumerator_at_one k g u₀ (m + 1) (n + 1)
  · exact torusPowerCutPencilDenominator_at k g u₀ (m + 1) (n + 1) 1

/-- A common exponent bound makes the pencil and both signed endpoints admissible. -/
theorem exists_torusPowerCutPencilPrime_endpoints
    (hz : IsFiniteCorrespondencePoint (XG).hom (YG).hom z) :
    ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      ∃ (hm : TorusPowerCutAdmissibleAt k X Y z m) (hn : TorusPowerCutAdmissibleAt k X Y z n)
        (hP : TorusPowerCutPencilAdmissibleAt k X Y z u₀ (m + 1) (n + 1)),
        (graphFunctor k).map (φ(0)) ≫ torusPowerCutPencilPrime k X Y z u₀ (m + 1) (n + 1) hP =
          torusPowerCutPrime k X Y z n hn ∧
        (graphFunctor k).map (φ(1)) ≫ torusPowerCutPencilPrime k X Y z u₀ (m + 1) (n + 1) hP =
          torusPowerCutPrime k X Y z m hm := by
  obtain ⟨N₁, h₁⟩ := exists_torusPowerCutAdmissibleAt k X Y z hz
  obtain ⟨N₂, h₂⟩ := exists_torusPowerCutPencilAdmissibleAt k X Y z hz u₀
  refine ⟨max N₁ N₂, fun m n hm hn => ?_⟩
  let hm' := h₁ m ((le_max_left _ _).trans hm)
  let hn' := h₁ n ((le_max_left _ _).trans hn)
  let hP := h₂ (m + 1) (n + 1)
    (((le_max_right _ _).trans hm).trans (Nat.le_succ m))
    (((le_max_right _ _).trans hn).trans (Nat.le_succ n))
  exact ⟨hm', hn', hP, torusPowerCutPencilPrime_endpoints k X Y z hz m n hm' hn' hP⟩

end AlgebraicGeometry.Cor
