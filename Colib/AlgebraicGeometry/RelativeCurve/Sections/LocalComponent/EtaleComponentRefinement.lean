/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleIntegralBase

/-!
# The same curve component after an integral marked base refinement

The original curve and strict-local model retain their original pullback ordering. A clopen
base refinement gives an actual Cartesian clopen curve refinement. Consequently the marked
normal component is exactly the pullback of the previous component. This is compatible with
pulling back already descended roots, frames, sections and the entire boundary ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X.left) {N : Scheme.{u}} (p : N ⟶ X.left)

/-- Pull back the unchanged curve along an actual original neighborhood refinement. -/
def etaleNeighborhoodCurveMap {A C : EtaleNeighborhood X ξ} (f : C ⟶ A) :
    pullback p (etaleNeighborhoodHom X ξ C).left ⟶
      pullback p (etaleNeighborhoodHom X ξ A).left :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ ((etaleNeighborhoodToSmooth X ξ).map f).left) (by
      rw [Category.assoc, etaleNeighborhoodMap_hom]
      exact pullback.condition)

/-- The refinement retains the exact original curve projection. -/
@[reassoc (attr := simp)] theorem etaleNeighborhoodCurveMap_fst
    {A C : EtaleNeighborhood X ξ} (f : C ⟶ A) :
    etaleNeighborhoodCurveMap X ξ p f ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The refinement retains the exact original base map. -/
@[reassoc (attr := simp)] theorem etaleNeighborhoodCurveMap_snd
    {A C : EtaleNeighborhood X ξ} (f : C ⟶ A) :
    etaleNeighborhoodCurveMap X ξ p f ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ ((etaleNeighborhoodToSmooth X ξ).map f).left :=
  pullback.lift_snd _ _ _

/-- The original curve transition is genuinely Cartesian over the original base refinement. -/
theorem etaleNeighborhoodCurveMap_isPullback {A C : EtaleNeighborhood X ξ} (f : C ⟶ A) :
    IsPullback (etaleNeighborhoodCurveMap X ξ p f) (pullback.snd _ _)
      (pullback.snd _ _) (((etaleNeighborhoodToSmooth X ξ).map f).left) := by
  refine IsPullback.of_right ?_ (etaleNeighborhoodCurveMap_snd X ξ p f)
    (IsPullback.of_hasPullback p (etaleNeighborhoodHom X ξ A).left)
  rw [etaleNeighborhoodCurveMap_fst, etaleNeighborhoodMap_hom]
  exact IsPullback.of_hasPullback p (etaleNeighborhoodHom X ξ C).left

/-- A clopen integral base restriction pulls back to an open curve restriction. -/
instance etaleNeighborhoodCurveMap_isOpenImmersion {A C : EtaleNeighborhood X ξ}
    (f : C ⟶ A) [IsOpenImmersion (((etaleNeighborhoodToSmooth X ξ).map f).left)] :
    IsOpenImmersion (etaleNeighborhoodCurveMap X ξ p f) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (etaleNeighborhoodCurveMap_isPullback X ξ p f).flip inferInstance

/-- The same clopen integral base restriction also pulls back to a closed curve restriction. -/
instance etaleNeighborhoodCurveMap_isClosedImmersion {A C : EtaleNeighborhood X ξ}
    (f : C ⟶ A) [IsClosedImmersion (((etaleNeighborhoodToSmooth X ξ).map f).left)] :
    IsClosedImmersion (etaleNeighborhoodCurveMap X ξ p f) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (etaleNeighborhoodCurveMap_isPullback X ξ p f).flip inferInstance

variable (B : BigEtaleSite.{u}) (hX : B.Contains X.left) (s : GeometricPoint X.left)

/-- The literal original base cone leg, with its source and target schemes made explicit. -/
def etaleNeighborhoodBaseConeLeg (A : EtaleNeighborhood X s.hom) :
    strictHenselization B X.left hX s ⟶ ((etaleNeighborhoodToSmooth X s.hom).obj A).left :=
  (etaleNeighborhoodStrictHenselizationCone X B hX s).π.app A

/-- The typed base leg is the original structure map over the original base. -/
@[reassoc (attr := simp)] theorem etaleNeighborhoodBaseConeLeg_hom
    (A : EtaleNeighborhood X s.hom) :
    etaleNeighborhoodBaseConeLeg X B hX s A ≫ (etaleNeighborhoodHom X s.hom A).left =
      strictHenselizationToBase B X.left hX s :=
  etaleNeighborhoodStrictHenselizationCone_π_comp_hom X B hX s A

/-- The literal base cone leg factors through every original neighborhood refinement. -/
@[reassoc (attr := simp)] theorem etaleNeighborhoodBaseConeLeg_refinement
    {A C : EtaleNeighborhood X s.hom} (f : C ⟶ A) :
    etaleNeighborhoodBaseConeLeg X B hX s C ≫
      ((etaleNeighborhoodToSmooth X s.hom).map f).left =
        etaleNeighborhoodBaseConeLeg X B hX s A :=
  etaleNeighborhoodStrictHenselizationCone_refinement X B hX s f

/-- The actual strict-local curve projection, in the original compactification ordering. -/
def etaleNeighborhoodCurveConeLeg (A : EtaleNeighborhood X s.hom) :
    pullback p (strictHenselizationToBase B X.left hX s) ⟶
      pullback p (etaleNeighborhoodHom X s.hom A).left :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ etaleNeighborhoodBaseConeLeg X B hX s A) (by
      rw [Category.assoc, etaleNeighborhoodBaseConeLeg_hom]
      exact pullback.condition)

/-- Every projection keeps the original compactification map. -/
@[reassoc (attr := simp)] theorem etaleNeighborhoodCurveConeLeg_fst
    (A : EtaleNeighborhood X s.hom) :
    etaleNeighborhoodCurveConeLeg X p B hX s A ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- Every projection keeps the literal original strict-henselization cone leg on the base. -/
@[reassoc (attr := simp)] theorem etaleNeighborhoodCurveConeLeg_snd
    (A : EtaleNeighborhood X s.hom) :
    etaleNeighborhoodCurveConeLeg X p B hX s A ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ etaleNeighborhoodBaseConeLeg X B hX s A :=
  pullback.lift_snd _ _ _

/-- Pulling back stage data to the integral refinement keeps the exact original local map. -/
@[reassoc (attr := simp)] theorem etaleNeighborhoodCurveConeLeg_refinement
    {A C : EtaleNeighborhood X s.hom} (f : C ⟶ A) :
    etaleNeighborhoodCurveConeLeg X p B hX s C ≫ etaleNeighborhoodCurveMap X s.hom p f =
      etaleNeighborhoodCurveConeLeg X p B hX s A := by
  apply pullback.hom_ext
  · simp only [Category.assoc, etaleNeighborhoodCurveMap_fst, etaleNeighborhoodCurveConeLeg_fst]
  · rw [Category.assoc, etaleNeighborhoodCurveMap_snd, ← Category.assoc,
      etaleNeighborhoodCurveConeLeg_snd, Category.assoc,
      etaleNeighborhoodBaseConeLeg_refinement]
    exact (etaleNeighborhoodCurveConeLeg_snd X p B hX s A).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original-order curve cone leg is exactly the small cone leg through the two canonical
pullback symmetries. Both are maps of the same original compactification. -/
theorem etaleNeighborhoodCurveConeLeg_small_symmetry (i : SmallEtaleNeighborhood X s) :
    etaleNeighborhoodCurveConeLeg X p B hX s ((smallEtaleNeighborhoodInclusion X s).obj i) ≫
      (pullbackSymmetry p ((smallEtaleNeighborhoodOver X s).obj i).hom).hom =
        (etaleCurveConeOriginalIso X B hX s p).hom ≫ (etaleCurveCone X B hX s p).π.app i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      etaleCurveCone_π_fst]
    refine (etaleNeighborhoodCurveConeLeg_snd X p B hX s
      ((smallEtaleNeighborhoodInclusion X s).obj i)).trans ?_
    change pullback.snd p (strictHenselizationToBase B X.left hX s) ≫ _ =
      (pullbackSymmetry p (strictHenselizationToBase B X.left hX s)).hom ≫
        pullback.fst (strictHenselizationToBase B X.left hX s) p ≫ _
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
    rfl
  · simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
      etaleCurveCone_π_snd]
    exact (etaleNeighborhoodCurveConeLeg_fst X p B hX s
      ((smallEtaleNeighborhoodInclusion X s).obj i)).trans
        (pullbackSymmetry_hom_comp_snd p (strictHenselizationToBase B X.left hX s)).symm

/-- The original retained point stays in the original retained open at every actual
neighborhood, including the integral clopen refinement. -/
theorem etaleNeighborhoodCurveConeLeg_mem_retainedOpen
    {Y : Scheme.{u}} (j : Y ⟶ N)
    (x : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}))
    (hx : x ∈ Set.range (pullback.fst
      (pullback.fst p (strictHenselizationToBase B X.left hX s)) j))
    (A : EtaleNeighborhood X s.hom) :
    etaleNeighborhoodCurveConeLeg X p B hX s A x ∈ Set.range
      (pullback.fst (pullback.fst p (etaleNeighborhoodHom X s.hom A).left) j) := by
  rw [Pullback.range_fst] at hx ⊢
  change (etaleNeighborhoodCurveConeLeg X p B hX s A ≫ pullback.fst _ _) x ∈ Set.range j
  rw [etaleNeighborhoodCurveConeLeg_fst]
  exact hx

/-- The marked normal component after the clopen base refinement is the actual pullback of
the previous marked component, not a replacement curve. -/
theorem normalComponentOpen_etaleNeighborhoodCurveMap
    [IsLocallyNoetherian X.left] [IsNormal N] [IsProper p]
    {A C : EtaleNeighborhood X s.hom} (f : C ⟶ A)
    [IsOpenImmersion (((etaleNeighborhoodToSmooth X s.hom).map f).left)]
    (x : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u})) :
    etaleNeighborhoodCurveMap X s.hom p f ⁻¹ᵁ
      normalComponentOpen (etaleNeighborhoodCurveConeLeg X p B hX s A x) =
        normalComponentOpen (etaleNeighborhoodCurveConeLeg X p B hX s C x) := by
  have h := normalComponentOpen_preimage_of_isOpenImmersion
    (etaleNeighborhoodCurveMap X s.hom p f) (etaleNeighborhoodCurveConeLeg X p B hX s C x)
  simpa only [← Hom.comp_apply, etaleNeighborhoodCurveConeLeg_refinement] using h

/-- If the actual component model already recovers the original local component, the integral
clopen base refinement recovers that very same open subscheme. This applies after the common
root, frame and whole-ideal stage has been chosen. -/
theorem etaleNeighborhoodCurveConeLeg_component_preimage_eq_of_refinement
    [IsLocallyNoetherian X.left] [IsNormal N] [IsProper p]
    {A C : EtaleNeighborhood X s.hom} (f : C ⟶ A)
    [IsOpenImmersion (((etaleNeighborhoodToSmooth X s.hom).map f).left)]
    (x : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}))
    (U : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}).Opens)
    (hA : etaleNeighborhoodCurveConeLeg X p B hX s A ⁻¹ᵁ
      normalComponentOpen (etaleNeighborhoodCurveConeLeg X p B hX s A x) = U) :
    etaleNeighborhoodCurveConeLeg X p B hX s C ⁻¹ᵁ
      normalComponentOpen (etaleNeighborhoodCurveConeLeg X p B hX s C x) = U := by
  rw [← normalComponentOpen_etaleNeighborhoodCurveMap X p B hX s f x,
    ← Hom.comp_preimage, etaleNeighborhoodCurveConeLeg_refinement, hA]

set_option backward.isDefEq.respectTransparency false in
/-- The original-order normal component descends after any prescribed small common stage. -/
theorem exists_etaleNeighborhoodCurve_component_preimage_eq_over
    [IsLocallyNoetherian X.left] [IsNormal N] [IsProper p]
    (x : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}))
    (i₀ : SmallEtaleNeighborhood X s) :
    ∃ (i : SmallEtaleNeighborhood X s) (_ : i ⟶ i₀),
      let A := (smallEtaleNeighborhoodInclusion X s).obj i
      ((etaleNeighborhoodCurveConeLeg X p B hX s A ⁻¹ᵁ
        normalComponentOpen (etaleNeighborhoodCurveConeLeg X p B hX s A x)) :
          Set (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u})) =
            _root_.irreducibleComponent x := by
  obtain ⟨i, f, hi⟩ := exists_originalComponent_etaleCurve_preimage_eq_over X B hX s p x i₀
  refine ⟨i, f, ?_⟩
  let A := (smallEtaleNeighborhoodInclusion X s).obj i
  let L := etaleNeighborhoodCurveConeLeg X p B hX s A
  let e := pullbackSymmetry p ((smallEtaleNeighborhoodOver X s).obj i).hom
  have : IsNoetherian (pullback p ((smallEtaleNeighborhoodOver X s).obj i).hom) :=
    inferInstanceAs (IsNoetherian (pullback p (etaleNeighborhoodHom X s.hom A).left))
  have : IsNormal (pullback p ((smallEtaleNeighborhoodOver X s).obj i).hom) :=
    inferInstanceAs (IsNormal (pullback p (etaleNeighborhoodHom X s.hom A).left))
  have : IsNoetherian (pullback ((smallEtaleNeighborhoodOver X s).obj i).hom p) :=
    inferInstanceAs (IsNoetherian ((etaleCurveDiagram X s p).obj i))
  have : IsNormal (pullback ((smallEtaleNeighborhoodOver X s).obj i).hom p) :=
    inferInstanceAs (IsNormal ((etaleCurveDiagram X s p).obj i))
  have hs := normalComponentOpen_preimage_of_isOpenImmersion e.hom (L x)
  have h := congrArg (fun V ↦ L ⁻¹ᵁ V) hs
  rw [← Hom.comp_preimage] at h
  change (L ≫ e.hom) ⁻¹ᵁ normalComponentOpen ((L ≫ e.hom) x) =
    L ⁻¹ᵁ normalComponentOpen (L x) at h
  have hsym : L ≫ e.hom = (etaleCurveConeOriginalIso X B hX s p).hom ≫
      (etaleCurveCone X B hX s p).π.app i :=
    etaleNeighborhoodCurveConeLeg_small_symmetry X p B hX s i
  rw [hsym] at h
  exact (congrArg (fun V : (pullback p
      (strictHenselizationToBase B X.left hX s) : Scheme.{u}).Opens ↦
        (V : Set (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}))) h).symm.trans
          hi

set_option backward.isDefEq.respectTransparency false in
/-- After any root/frame common stage, construct an integral original affine neighborhood and
the same original strict-local curve component. The final curve map is an actual clopen
pullback, so already descended data can be retained without a new compactification. -/
theorem exists_integral_etaleNeighborhood_same_component
    [IsLocallyNoetherian X.left] [IsNormal X.left] [IsNormal N] [IsProper p]
    (x : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}))
    (i₀ : SmallEtaleNeighborhood X s) :
    ∃ (i : SmallEtaleNeighborhood X s) (_ : i ⟶ i₀)
      (C : EtaleNeighborhood X s.hom)
      (f : C ⟶ (smallEtaleNeighborhoodInclusion X s).obj i),
      IsIntegral ((etaleNeighborhoodToSmooth X s.hom).obj C).left ∧
      IsNoetherian ((etaleNeighborhoodToSmooth X s.hom).obj C).left ∧
      IsOpenImmersion (((etaleNeighborhoodToSmooth X s.hom).map f).left) ∧
      IsClosedImmersion (((etaleNeighborhoodToSmooth X s.hom).map f).left) ∧
      ((etaleNeighborhoodCurveConeLeg X p B hX s C ⁻¹ᵁ
        normalComponentOpen (etaleNeighborhoodCurveConeLeg X p B hX s C x)) :
          Set (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u})) =
            _root_.irreducibleComponent x := by
  have := isNormal_pullback_strictHenselizationToBase B hX s p
  have := isLocallyNoetherian_pullback_strictHenselizationToBase B hX s p
  obtain ⟨i, d, hi⟩ := exists_etaleNeighborhoodCurve_component_preimage_eq_over X p B hX s x i₀
  obtain ⟨C, f, hC, hNoeth, hOpen, hClosed, -⟩ :=
    exists_integral_etaleNeighborhood_refinement X s.hom
      ((smallEtaleNeighborhoodInclusion X s).obj i)
  have hA : etaleNeighborhoodCurveConeLeg X p B hX s
      ((smallEtaleNeighborhoodInclusion X s).obj i) ⁻¹ᵁ
        normalComponentOpen (etaleNeighborhoodCurveConeLeg X p B hX s
          ((smallEtaleNeighborhoodInclusion X s).obj i) x) = normalComponentOpen x :=
    SetLike.coe_injective hi
  refine ⟨i, d, C, f, hC, hNoeth, hOpen, hClosed, ?_⟩
  exact congrArg (fun V : (pullback p
      (strictHenselizationToBase B X.left hX s) : Scheme.{u}).Opens ↦
        (V : Set (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u})))
    (etaleNeighborhoodCurveConeLeg_component_preimage_eq_of_refinement X p B hX s f x
      (normalComponentOpen x) hA)

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.Scheme

/-- Restriction to the actual normal components along an open immersion is a genuine
Cartesian square. Subsequent pullbacks therefore preserve the full boundary scheme and ideal,
not merely the set of its points. -/
theorem normalComponentOpen_isPullback_of_isOpenImmersion
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormal X] [IsNormal Y] (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsPullback (f.resLE (normalComponentOpen (f x)) (normalComponentOpen x)
      (normalComponentOpen_preimage_of_isOpenImmersion f x).ge)
      (normalComponentOpen x).ι (normalComponentOpen (f x)).ι f := by
  apply IsOpenImmersion.isPullback
  · exact (Hom.resLE_comp_ι _ _).symm
  · simpa only [Opens.opensRange_ι] using
      normalComponentOpen_preimage_of_isOpenImmersion f x

/-- A morphism from a preconnected scheme lies entirely in the normal component containing
one of its points. This applies to the final integral affine neighborhood, which is not local. -/
theorem range_subset_normalComponent_of_preconnected
    {T X : Scheme.{u}} [PreconnectedSpace T] [IsLocallyNoetherian X] [IsNormal X]
    (f : T ⟶ X) (t : T) : Set.range f ⊆ Set.range (normalComponentOpen (f t)).ι := by
  rw [Opens.range_ι]
  exact (isPreconnected_range f.continuous).subset_isClopen
    (isClopen_normalComponentOpen (f t)) ⟨f t, Set.mem_range_self t, mem_normalComponentOpen _⟩

/-- Two original maps from a preconnected base that agree at the marking factor through one
actual integral component, retaining both entire original morphisms. -/
theorem exists_integral_component_lifts_of_preconnected
    {T X : Scheme.{u}} [PreconnectedSpace T] [IsLocallyNoetherian X] [IsNormal X]
    (s₀ s₁ : T ⟶ X) (t : T) (hs : s₀ t = s₁ t) :
    ∃ (a₀ a₁ : T ⟶ (normalComponentOpen (s₀ t)).toScheme),
      a₀ ≫ (normalComponentOpen (s₀ t)).ι = s₀ ∧
      a₁ ≫ (normalComponentOpen (s₀ t)).ι = s₁ := by
  have h₀ := range_subset_normalComponent_of_preconnected s₀ t
  have h₁ : Set.range s₁ ⊆ Set.range (normalComponentOpen (s₀ t)).ι := by
    rw [hs]
    exact range_subset_normalComponent_of_preconnected s₁ t
  exact ⟨IsOpenImmersion.lift _ s₀ h₀, IsOpenImmersion.lift _ s₁ h₁,
    IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry.Scheme
