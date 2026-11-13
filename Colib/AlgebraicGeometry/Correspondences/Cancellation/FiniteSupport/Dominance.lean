/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.Projection
import Colib.CategoryTheory.Limits.Shapes.Pullback.ParameterGraph
import Colib.RingTheory.Polynomial.LaurentFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Dominance of a finite change of the torus coordinate

Consider two finite maps from a support to the native relative torus with the
same projection to the original base. If the first map is dominant, each
residue-field fibre of the second map is surjective. A proper image in its
Laurent chart would make the support fibre finite over the residue field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme

private theorem isFinite_projection_of_not_surjective {k R : Type u} [Field k] [Field R]
    (a : Spec (.of R) ⟶ Spec (.of k)) {P : Scheme.{u}} (h : P ⟶ ambient a) [IsFinite h]
    (hn : ¬ Surjective h) : IsFinite (h ≫ pullback.fst a
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))) := by
  let e := nativeChartIso a
  let c := h ≫ e.inv
  let : IsFinite c := inferInstance
  let : IsAffine P := isAffine_of_isAffineHom c
  let L := LaurentPolynomial R
  let d := (ΓSpecIso (.of L)).inv
  let φ : L →+* Γ(P, ⊤) := c.appTop.hom.comp d.hom
  have hd : Function.Surjective d := (ConcreteCategory.bijective_of_isIso d).2
  have hφ : φ.Finite := c.finite_appTop.comp (RingHom.Finite.of_surjective d.hom hd)
  have hinj : ¬ Function.Injective φ := by
    intro hi
    let : IsDominant c := isDominant_of_of_appTop_injective (f := c)
      (Function.Injective.of_comp_right (f := c.appTop) (g := d) hi hd)
    apply hn
    have he : c ≫ e.hom = h := by simp [c]
    rw [← he]
    infer_instance
  have hR := LaurentPolynomial.finite_comp_C_of_not_injective φ hφ hinj
  have he : (ΓSpecIso (.of R)).inv ≫ (c ≫ chartProjection).appTop =
      CommRingCat.ofHom (φ.comp LaurentPolynomial.C) := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, chartProjection,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  have htop : ((c ≫ chartProjection).appTop.hom).Finite := by
    have hf : (((ΓSpecIso (.of R)).inv ≫ (c ≫ chartProjection).appTop).hom).Finite := by
      rw [he]
      exact hR
    have hf' := hf.comp (RingHom.Finite.of_surjective (ΓSpecIso (.of R)).hom.hom
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).hom).2)
    rwa [← CommRingCat.hom_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hf'
  have hf : IsFinite (c ≫ chartProjection) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite.{u})]
    exact ⟨inferInstance, htop⟩
  have hpr : e.inv ≫ chartProjection = pullback.fst a
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) :=
    chartInverse_projection a
  change IsFinite ((h ≫ e.inv) ≫ chartProjection) at hf
  rwa [Category.assoc, hpr] at hf

/-- Changing the torus coordinate preserves surjectivity when the two maps
are finite and have the same projection to the base. -/
theorem surjective_of_finite_of_dominant_torus {k : Type u} [Field k] {X P : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (g h : P ⟶ pullback f (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)))
    [IsFinite g] [IsDominant g] [IsFinite h]
    (he : g ≫ pullback.fst f (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) =
      h ≫ pullback.fst f (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))) :
    Surjective h := by
  constructor
  intro y
  let q := multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)
  let p := pullback.fst f q
  let x := p y
  let K := X.residueField x
  let j : Spec K ⟶ X := X.fromSpecResidueField x
  let t := pullbackParameterExtensionMap j f q
  let pK := pullback.fst (j ≫ f) q
  have ht : IsPullback t pK p j := pullbackParameterExtension_isPullback j f q
  let sg := pullback.snd g t
  let sh := pullback.snd h t
  have hg : IsPullback (pullback.fst g t) (sg ≫ pK) (g ≫ p) j :=
    (IsPullback.of_hasPullback g t).paste_vert ht
  have hh : IsPullback (pullback.fst h t) (sh ≫ pK) (g ≫ p) j := by
    change IsPullback _ _ (g ≫ pullback.fst f q) _
    rw [he]
    exact (IsPullback.of_hasPullback h t).paste_vert ht
  have hs : Surjective sh := by
    by_contra hn
    let : IsFinite sh := inferInstanceAs (IsFinite (pullback.snd h t))
    have hf : IsFinite (sh ≫ pK) := isFinite_projection_of_not_surjective (j ≫ f) sh hn
    let e := hg.isoPullback ≪≫ hh.isoPullback.symm
    have hproj : e.hom ≫ sh ≫ pK = sg ≫ pK := by
      simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, hh.isoPullback_inv_snd,
        hg.isoPullback_hom_snd]
    have hf' : IsFinite (sg ≫ pK) := by
      rw [← hproj]
      infer_instance
    let : Surjective g := inferInstance
    let : Surjective sg := MorphismProperty.pullback_snd (P := @Surjective.{u}) g t inferInstance
    let : IsFinite sg := inferInstanceAs (IsFinite (pullback.snd g t))
    exact not_isFinite_support_projection (j ≫ f) sg (IsLocalRing.closedPoint K) hf'
  obtain ⟨yK, hyK⟩ : y ∈ Set.range t := by
    have hy : y ∈ Set.range (pullback.fst p j) := by
      rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
      exact Set.mem_singleton_iff.mpr rfl
    obtain ⟨z, hz⟩ := hy
    use ht.isoPullback.inv z
    change (ht.isoPullback.inv ≫ t) z = y
    rwa [ht.isoPullback_inv_fst]
  obtain ⟨z, hz⟩ := sh.surjective yK
  use pullback.fst h t z
  change (pullback.fst h t ≫ h) z = y
  rw [pullback.condition, Scheme.Hom.comp_apply, show pullback.snd h t z = yK from hz, hyK]

end AlgebraicGeometry.NativeTorusPolynomial
