/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.SmallEtaleIntegralRefinement
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.MarkedNormalComponentSections
public import Colib.AlgebraicGeometry.Divisors.SectionKernelCartesian

/-! # Two original sections in one fixed small-stage clopen

Connectedness is used only on the actual integral neighborhood. Its factored
maps are then pulled back to the small model. The resulting clopen need not be
irreducible, and the new small base is not asserted to be connected or integral.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme

/-- A connected source maps into the prescribed clopen as soon as one point does. -/
theorem exists_factor_through_clopen_of_preconnected
    {A C : Scheme.{u}} [PreconnectedSpace A]
    (f : A ⟶ C) (U : C.Opens) (hU : IsClopen (U : Set C))
    (a : A) (ha : f a ∈ U) :
    ∃ fU : A ⟶ U.toScheme, fU ≫ U.ι = f := by
  have hr : Set.range f ⊆ Set.range U.ι := by
    rw [Opens.range_ι]
    exact (isPreconnected_range f.continuous).subset_isClopen hU
      ⟨f a, Set.mem_range_self a, ha⟩
  exact ⟨IsOpenImmersion.lift U.ι f hr, IsOpenImmersion.lift_fac _ _ _⟩

/-- Pull back an actual section already factoring through the fixed open. No
connectedness of the new base or of the pulled-back open is required. -/
theorem exists_cartesianSection_through_preimage_open
    {C' C A' A : Scheme.{u}} (F : C' ⟶ C) (q' : C' ⟶ A')
    (q : C ⟶ A) (v : A' ⟶ A) (hp : IsPullback F q' q v)
    (σ : A ⟶ C) (hσ : σ ≫ q = 𝟙 A)
    (U : C.Opens) (φ : A' ⟶ U.toScheme) (hφ : φ ≫ U.ι = v ≫ σ) :
    ∃ σU : A' ⟶ (F ⁻¹ᵁ U).toScheme,
      σU ≫ (F ⁻¹ᵁ U).ι ≫ F = v ≫ σ ∧
      σU ≫ ((F ⁻¹ᵁ U).ι ≫ q') = 𝟙 A' := by
  let σ' : A' ⟶ C' := hp.lift (v ≫ σ) (𝟙 A')
    (by simp only [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hfst : σ' ≫ F = v ≫ σ := hp.lift_fst _ _ _
  have hsnd : σ' ≫ q' = 𝟙 A' := hp.lift_snd _ _ _
  have hr : Set.range σ' ⊆ Set.range (F ⁻¹ᵁ U).ι := by
    rw [Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    change F (σ' a) ∈ U
    have hw : σ' ≫ F = φ ≫ U.ι := hfst.trans hφ.symm
    have hpnt := congrArg (fun z : A' ⟶ C => z a) hw
    change (σ' ≫ F) a ∈ U
    rw [hpnt]
    exact (φ a).property
  let σU := IsOpenImmersion.lift (F ⁻¹ᵁ U).ι σ' hr
  have hfac : σU ≫ (F ⁻¹ᵁ U).ι = σ' := IsOpenImmersion.lift_fac _ _ _
  refine ⟨σU, ?_, ?_⟩
  · rw [← Category.assoc, hfac, hfst]
  · rw [← Category.assoc, hfac, hsnd]

namespace SmoothSite

/-- An actual integral intermediate base supplies both factors. Initiality then
returns a genuine small stage, retaining the old component's exact limit preimage.
All new whole-stage sections are obtained from the actual curve Cartesian square. -/
theorem exists_small_fixed_clopen_section_pair
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    [IsNormal X.left] [IsLocallyNoetherian X.left] [IsNormal N] [IsProper p]
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    (i : SmallEtaleNeighborhood X s)
    (U : ((etaleCurveDiagram X s p).obj i).Opens)
    (hU : IsClopen (U : Set ((etaleCurveDiagram X s p).obj i)))
    (x : (etaleCurveCone X B hX s p).pt)
    (hpre : (etaleCurveCone X B hX s p).π.app i ⁻¹ᵁ U = normalComponentOpen x)
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶
      (etaleCurveDiagram X s p).obj i)
    (hσ : σ ≫ (etaleCurveStructure X s p).app i = 𝟙 _)
    (hτ : τ ≫ (etaleCurveStructure X s p).app i = 𝟙 _)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj i) ≫ σ =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj i) ≫ τ)
    (hmem : σ ((etaleNeighborhoodMark X s.hom
      ((smallEtaleNeighborhoodInclusion X s).obj i))
        (IsLocalRing.closedPoint s.residueField)) ∈ U) :
    ∃ (a : Over i),
      let U' := (etaleCurveDiagram X s p).map a.hom ⁻¹ᵁ U
      IsClopen (U' : Set ((etaleCurveDiagram X s p).obj a.left)) ∧
      IsClosedImmersion U'.ι ∧
      (etaleCurveCone X B hX s p).π.app a.left ⁻¹ᵁ U' = normalComponentOpen x ∧
      ∃ (σU τU : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶ U'.toScheme),
        σU ≫ U'.ι ≫ (etaleCurveDiagram X s p).map a.hom =
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom ≫ σ ∧
        τU ≫ U'.ι ≫ (etaleCurveDiagram X s p).map a.hom =
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom ≫ τ ∧
        σU ≫ (U'.ι ≫ (etaleCurveStructure X s p).app a.left) = 𝟙 _ ∧
        τU ≫ (U'.ι ≫ (etaleCurveStructure X s p).app a.left) = 𝟙 _ ∧
        etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫ σU =
          etaleNeighborhoodMark X s.hom
            ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫ τU := by
  obtain ⟨A, v, hInt, hNoeth, hvOpen, hvClosed, a, t, ht⟩ :=
    exists_integral_etaleNeighborhood_with_small_refinement X s i
  let := hInt
  let g := ((etaleNeighborhoodToSmooth X s.hom).map v).left
  let t₁ := ((etaleNeighborhoodToSmooth X s.hom).map t).left
  let η := etaleNeighborhoodMark X s.hom A
  let ξ := etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)
  let μ := etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a.left)
  let b := (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom
  have hη : η ≫ g = ξ := etaleNeighborhoodMark_map X s.hom v
  have htb : t₁ ≫ g = b := by
    let G := etaleNeighborhoodToSmooth X s.hom ⋙ forgetScheme S
    exact (G.map_comp t v).symm.trans (congrArg G.map ht)
  have hηPoint : g (η (IsLocalRing.closedPoint s.residueField)) =
      ξ (IsLocalRing.closedPoint s.residueField) :=
    congrArg (fun z : Spec (.of s.residueField) ⟶
      ((etaleNeighborhoodToSmooth X s.hom).obj
        ((smallEtaleNeighborhoodInclusion X s).obj i)).left =>
      z (IsLocalRing.closedPoint s.residueField)) hη
  have hsMem : (g ≫ σ) (η (IsLocalRing.closedPoint s.residueField)) ∈ U := by
    exact (congrArg (fun z => σ z ∈ U) hηPoint).mpr hmem
  have htMem : (g ≫ τ) (η (IsLocalRing.closedPoint s.residueField)) ∈ U := by
    have hsame : σ (ξ (IsLocalRing.closedPoint s.residueField)) =
        τ (ξ (IsLocalRing.closedPoint s.residueField)) :=
      congrArg (fun z : Spec (.of s.residueField) ⟶
        (etaleCurveDiagram X s p).obj i => z (IsLocalRing.closedPoint s.residueField)) hmark
    exact (congrArg (fun z => z ∈ U) ((congrArg τ hηPoint).trans hsame.symm)).mpr hmem
  obtain ⟨φσ, hφσ⟩ := exists_factor_through_clopen_of_preconnected
    (g ≫ σ) U hU (η (IsLocalRing.closedPoint s.residueField)) hsMem
  obtain ⟨φτ, hφτ⟩ := exists_factor_through_clopen_of_preconnected
    (g ≫ τ) U hU (η (IsLocalRing.closedPoint s.residueField)) htMem
  let F := (etaleCurveDiagram X s p).map a.hom
  let U' := F ⁻¹ᵁ U
  have hp := etaleCurveDiagram_isPullback X s p a.hom
  have hφσ' : (t₁ ≫ φσ) ≫ U.ι = b ≫ σ :=
    (Category.assoc t₁ φσ U.ι).trans
      ((congrArg (fun z : ((etaleNeighborhoodToSmooth X s.hom).obj A).left ⟶
        (etaleCurveDiagram X s p).obj i => t₁ ≫ z) hφσ).trans
      ((Category.assoc t₁ g σ).symm.trans
        (congrArg (fun z : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i => z ≫ σ) htb)))
  have hφτ' : (t₁ ≫ φτ) ≫ U.ι = b ≫ τ :=
    (Category.assoc t₁ φτ U.ι).trans
      ((congrArg (fun z : ((etaleNeighborhoodToSmooth X s.hom).obj A).left ⟶
        (etaleCurveDiagram X s p).obj i => t₁ ≫ z) hφτ).trans
      ((Category.assoc t₁ g τ).symm.trans
        (congrArg (fun z : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i => z ≫ τ) htb)))
  obtain ⟨σU, hsF, hsq⟩ := exists_cartesianSection_through_preimage_open
    F ((etaleCurveStructure X s p).app a.left) ((etaleCurveStructure X s p).app i)
    b hp σ hσ U (t₁ ≫ φσ) hφσ'
  obtain ⟨τU, htF, htq⟩ := exists_cartesianSection_through_preimage_open
    F ((etaleCurveStructure X s p).app a.left) ((etaleCurveStructure X s p).app i)
    b hp τ hτ U (t₁ ≫ φτ) hφτ'
  have hU' : IsClopen (U' : Set ((etaleCurveDiagram X s p).obj a.left)) :=
    hU.preimage F.continuous
  have hclosed : IsClosedImmersion U'.ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Opens.range_ι]
    exact hU'.isClosed
  have hpre' : (etaleCurveCone X B hX s p).π.app a.left ⁻¹ᵁ U' = normalComponentOpen x := by
    change ((etaleCurveCone X B hX s p).π.app a.left ≫ F) ⁻¹ᵁ U = _
    rw [(etaleCurveCone X B hX s p).w a.hom]
    exact hpre
  refine ⟨a, hU', hclosed, hpre', σU, τU, hsF, htF, hsq, htq, ?_⟩
  apply (cancel_mono U'.ι).mp
  apply hp.hom_ext
  · have hμ : μ ≫ b = ξ :=
      etaleNeighborhoodMark_map X s.hom ((smallEtaleNeighborhoodInclusion X s).map a.hom)
    have hs : ((μ ≫ σU) ≫ U'.ι) ≫ F = ξ ≫ σ :=
      (Category.assoc (μ ≫ σU) U'.ι F).trans
        ((Category.assoc μ σU (U'.ι ≫ F)).trans
        ((congrArg (fun z : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶
          (etaleCurveDiagram X s p).obj i => μ ≫ z) hsF).trans
        ((Category.assoc μ b σ).symm.trans
          (congrArg (fun z : Spec (.of s.residueField) ⟶
            (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i => z ≫ σ) hμ))))
    have ht : ((μ ≫ τU) ≫ U'.ι) ≫ F = ξ ≫ τ :=
      (Category.assoc (μ ≫ τU) U'.ι F).trans
        ((Category.assoc μ τU (U'.ι ≫ F)).trans
        ((congrArg (fun z : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶
          (etaleCurveDiagram X s p).obj i => μ ≫ z) htF).trans
        ((Category.assoc μ b τ).symm.trans
          (congrArg (fun z : Spec (.of s.residueField) ⟶
            (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i => z ≫ τ) hμ))))
    exact hs.trans (hmark.trans ht.symm)
  · let q := (etaleCurveStructure X s p).app a.left
    have hs : ((μ ≫ σU) ≫ U'.ι) ≫ q = μ :=
      (Category.assoc (μ ≫ σU) U'.ι q).trans
        ((Category.assoc μ σU (U'.ι ≫ q)).trans
        ((congrArg (fun z : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left => μ ≫ z) hsq).trans
          (Category.comp_id μ)))
    have ht : ((μ ≫ τU) ≫ U'.ι) ≫ q = μ :=
      (Category.assoc (μ ≫ τU) U'.ι q).trans
        ((Category.assoc μ τU (U'.ι ≫ q)).trans
        ((congrArg (fun z : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶
          (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left => μ ≫ z) htq).trans
          (Category.comp_id μ)))
    exact hs.trans ht.symm

end SmoothSite
end AlgebraicGeometry.Scheme
