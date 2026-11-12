/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.AffineLine.GenericClosedFiber
public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFinite

/-! # Finiteness of the full compactification boundary near the generic base

The affine chart has a finite generic fiber because the boundary image is
closed and avoids the chart generic point. The other part lies in the
literal infinity section. The full closed boundary becomes finite after
shrinking the coefficient base.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Normalization/Compactification/`
`Boundary/RelativeInfinityFiniteBaseOpen.lean` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

open PolynomialLaurent RelativeCurve

variable (R : Type u) [CommRing R] [IsDomain R]

private theorem finite_nativeLine_generic_preimage
    {D : Scheme.{u}} (f : D ⟶ projectiveSpaceOverRing 1 (.of R)) [IsFinite f]
    (hη : NativeProjectiveLine.chart R (genericPoint (Spec (.of (Polynomial R)))) ∉ Set.range f) :
    ((f ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))) ⁻¹'
      {genericPoint (Spec (.of R))}).Finite := by
  let π := (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
  let j := NativeProjectiveLine.chart R
  let d := NativeProjectiveLine.infinity R
  let η := genericPoint (Spec (.of R))
  have hclosed : IsClosed (Set.range f) := by
    rw [← Set.image_univ]
    exact f.isClosedMap _ isClosed_univ
  have hfin := finite_polynomialProjection_generic_preimage_inter_closed R
    (hclosed.preimage j.continuous) hη
  have hsubset : Set.range f ∩ (π ⁻¹' {η}) ⊆
      j '' ((j ⁻¹' Set.range f) ∩ (polynomialProjection (.of R) ⁻¹' {η})) ∪ {d η} := by
    intro y hy
    by_cases hyj : y ∈ Set.range j
    · obtain ⟨z, rfl⟩ := hyj
      have hz : polynomialProjection (.of R) z = π (j z) :=
        (congrArg (fun m : Spec (.of (Polynomial R)) ⟶ Spec (.of R) => m z)
          (NativeProjectiveLine.chart_projection R)).symm
      exact Or.inl ⟨z, ⟨hy.1, hz.trans hy.2⟩, rfl⟩
    · obtain ⟨z, rfl⟩ : y ∈ Set.range d := by
        rwa [NativeProjectiveLine.range_infinity]
      have hz : π (d z) = z :=
        congrArg (fun m : Spec (.of R) ⟶ Spec (.of R) => m z)
          (NativeProjectiveLine.infinity_projection R)
      exact Or.inr (congrArg d (hz.symm.trans hy.2))
  exact (f.finite_preimage (((hfin.image j).union (Set.finite_singleton (d η))).subset
    hsubset)).subset (fun x hx => ⟨⟨x, rfl⟩, hx⟩)

variable [IsNoetherianRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R)))
  [Etale p] [QuasiCompact p] [IsSeparated p]

omit [IsSeparated p] in
/-- Every point of the relative normalization above the generic point of the
actual affine chart comes from the original étale source. -/
theorem mem_inclusion_of_over_chart_generic (c : compactification R p)
    (hc : toProjectiveLine R p c =
      NativeProjectiveLine.chart R (genericPoint (Spec (.of (Polynomial R))))) :
    c ∈ Set.range (inclusion R p) := by
  let η := genericPoint (Spec (.of (Polynomial R)))
  have hη : η ∈ genericPoints (Spec (.of (Polynomial R))) := by
    rw [genericPoints_eq_singleton]
    exact Set.mem_singleton _
  let : LocallyQuasiFinite p := EtaleCompactification.locallyQuasiFinite_of_etale p
  obtain ⟨V, hηV, hfin⟩ := (finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict
    p η hη).mp (p.finite_preimage_singleton η)
  let f := projectiveMap R p
  let g := V.1.ι ≫ NativeProjectiveLine.chart R
  let : IsFinite (p ∣_ V.1) := hfin
  have H₀ := (isPullback_morphismRestrict p V.1).flip
  have H : IsPullback (p ⁻¹ᵁ V.1).ι (p ∣_ V.1) f g :=
    IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono p V.1.ι
      (NativeProjectiveLine.chart R) _ H₀.isLimit)
  let : IsFinite (pullback.snd f g) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  let : Smooth g := inferInstanceAs (Smooth (V.1.ι ≫ NativeProjectiveLine.chart R))
  have hc' : f.fromNormalization c = g ⟨η, hηV⟩ := hc
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback f.fromNormalization g) c ⟨η, hηV⟩ hc'
  let e := (pullback.snd f g).toNormalization ≫ f.normalizationPullback g
  obtain ⟨z, hz⟩ := e.surjective y
  refine ⟨pullback.fst f g z, ?_⟩
  have he := congrArg (fun a : pullback f g ⟶ f.normalization => a z)
    (f.toNormalization_normalizationPullback_fst g)
  exact he.symm.trans ((congrArg (pullback.fst f.fromNormalization g) hz).trans hy)

/-- The actual compactification boundary has finite fiber over the original
coefficient generic point. -/
theorem finite_infinity_generic_preimage (k : Type u) [Field k] [Algebra k R]
    [Algebra.FiniteType k R] [IsIntegrallyClosed R] :
    ((infinityInclusion R p ≫ projection R p) ⁻¹' {genericPoint (Spec (.of R))}).Finite := by
  let : IsFinite (toProjectiveLine R p) := toProjectiveLine_finite R p k
  let d := infinityInclusion R p
  let f := d ≫ toProjectiveLine R p
  have hη : NativeProjectiveLine.chart R (genericPoint (Spec (.of (Polynomial R)))) ∉
      Set.range f := by
    rintro ⟨c, hc⟩
    have h := mem_inclusion_of_over_chart_generic R p (d c) hc
    have h' : d c ∈ Set.range (infinityInclusion R p) := ⟨c, rfl⟩
    rw [range_infinityInclusion R p] at h'
    exact h' h
  simpa only [projection, ← Category.assoc] using finite_nativeLine_generic_preimage R f hη

/-- The full boundary becomes finite on one actual open of the coefficient base. -/
theorem exists_base_open_finite_infinity (k : Type u) [Field k] [Algebra k R]
    [Algebra.FiniteType k R] [IsIntegrallyClosed R] :
    ∃ V : (Spec (.of R)).Opens, genericPoint (Spec (.of R)) ∈ V ∧
      IsFinite ((infinityInclusion R p ≫ projection R p) ∣_ V) := by
  let : IsFinite (toProjectiveLine R p) := toProjectiveLine_finite R p k
  exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton
    (infinityInclusion R p ≫ projection R p) _ (finite_infinity_generic_preimage R p k)

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
