/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedMarkedSquare
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedRefinement
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ProductResidual
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange

/-! # The original norm boundary under the common coefficient restriction -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

section OpenBase

variable {S P C D₁ D₂ : Scheme.{u}} (π : P ⟶ S) (V : S.Opens)

/-- The entire range of a restricted source is the inverse image of its
original range on the coefficient open. -/
theorem sourceBaseMap_range_preimage (f : C ⟶ P) :
    Set.range (sourceBaseMap π V f) =
      (compactificationOpen π V).ι ⁻¹' Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(sourceBaseOpen π V f).ι x,
      (congrArg (fun g => g x) (sourceBaseMap_original π V f)).symm⟩
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, _⟩ := Scheme.exists_preimage_of_isPullback
      (sourceBaseMap_isPullback π V f) y x hx.symm
    exact ⟨a, ha⟩

instance sourceBaseMap_isFiniteLocallyFree (f : C ⟶ P) [IsFiniteLocallyFree f] :
    IsFiniteLocallyFree (sourceBaseMap π V f) :=
  isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
    (sourceBaseMap_isPullback π V f).flip inferInstance

instance sourceBaseMap_isFinite (f : C ⟶ P) [IsFinite f] :
    IsFinite (sourceBaseMap π V f) :=
  MorphismProperty.of_isPullback (sourceBaseMap_isPullback π V f).flip inferInstance

instance sourceBaseMap_compactificationProjection_surjective (f : C ⟶ P)
    [Surjective (f ≫ π)] : Surjective (sourceBaseMap π V f ≫ compactificationProjection π V) := by
  rw [sourceBaseMap_projection]
  exact MorphismProperty.of_isPullback (isPullback_morphismRestrict (f ≫ π) V).flip
    (inferInstance : Surjective (f ≫ π))

/-- The original full inverse-infinity factor survives the coefficient restriction. -/
theorem exists_sourceBaseMap_inverseBoundary_factor (f : C ⟶ P)
    (d₁ : D₁ ⟶ C) (d₂ : D₂ ⟶ P) (bI : pullback f d₂ ⟶ D₁)
    (hbI : bI ≫ d₁ = pullback.fst f d₂) :
    ∃ bI' : pullback (sourceBaseMap π V f) (sourceBaseMap π V d₂) ⟶
        (sourceBaseOpen (f ≫ π) V d₁).toScheme,
      bI' ≫ sourceBaseMap (f ≫ π) V d₁ =
        pullback.fst (sourceBaseMap π V f) (sourceBaseMap π V d₂) := by
  let f' := sourceBaseMap π V f
  let d₂' := sourceBaseMap π V d₂
  let a := pullback.map f' d₂' f d₂ (compactificationOpen (f ≫ π) V).ι
    (sourceBaseOpen π V d₂).ι (compactificationOpen π V).ι
    (sourceBaseMap_original π V f) (sourceBaseMap_original π V d₂)
  let H := sourceBaseMap_isPullback (f ≫ π) V d₁
  have he : pullback.fst f' d₂' ≫ (compactificationOpen (f ≫ π) V).ι =
      (a ≫ bI) ≫ d₁ := by
    rw [Category.assoc, hbI]
    exact (pullback.lift_fst _ _ _).symm
  exact ⟨H.lift (pullback.fst f' d₂') (a ≫ bI) he, H.lift_fst _ _ _⟩

end OpenBase

section Residual

variable {P C Y Z P' C' Y' Z' D D' : Scheme.{u}}
  (f : C ⟶ P) [IsFinite f] (j : Y ⟶ C) [IsOpenImmersion j]
  (m : Z ⟶ P) (s : Z ⟶ Y) (H : IsPullback s (𝟙 Z) (j ≫ f) m)
  (f' : C' ⟶ P') [IsFinite f'] (j' : Y' ⟶ C') [IsOpenImmersion j']
  (m' : Z' ⟶ P') (s' : Z' ⟶ Y') (H' : IsPullback s' (𝟙 Z') (j' ≫ f') m')
  (iC : C' ⟶ C) (iP : P' ⟶ P) (iZ : Z' ⟶ Z)
  (hf : f' ≫ iP = iC ≫ f) (hm : m' ≫ iP = iZ ≫ m)
  (hj : Set.range j' = iC ⁻¹' Set.range j)
  (d : D ⟶ C) (d' : D' ⟶ C') (iD : D' ⟶ D) (HD : IsPullback d' iD iC d)

local notation "hs" => (markedSection_original_equation f j m s H)
local notation "hs'" => (markedSection_original_equation f' j' m' s' H')
local notation "R" => (residualMarkedFiberOpen f j m s hs)
local notation "R'" => (residualMarkedFiberOpen f' j' m' s' hs')

include hf hm hj HD in
omit [IsOpenImmersion j] [IsOpenImmersion j'] in
/-- The whole residual marked fiber factors through the restricted source boundary. -/
theorem exists_residualBoundary_factor_of_open_comparison
    (bE : (R).toScheme ⟶ D) (hbE : bE ≫ d = residualMarkedFiberMap f j m s hs) :
    ∃ bE' : (R').toScheme ⟶ D', bE' ≫ d' = residualMarkedFiberMap f' j' m' s' hs' := by
  let a := pullback.map f' m' f m iC iZ iP hf hm
  have ha : a ≫ pullback.fst f m = pullback.fst f' m' ≫ iC := pullback.lift_fst _ _ _
  have hrange : Set.range ((R').ι ≫ a) ⊆ Set.range (R).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change a x.val ∉ Set.range (markedFiberSection f j m s hs)
    intro hx
    have h := (mem_range_markedFiberSection_iff f j m s hs H _).mp hx
    change (a ≫ pullback.fst f m) x.val ∈ Set.range j at h
    rw [ha] at h
    have h' : pullback.fst f' m' x.val ∈ Set.range j' := by
      rw [hj]
      exact h
    exact x.property ((mem_range_markedFiberSection_iff f' j' m' s' hs' H' _).mpr h')
  let t := IsOpenImmersion.lift (R).ι ((R').ι ≫ a) hrange
  have ht : t ≫ (R).ι = (R').ι ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hcomp : t ≫ residualMarkedFiberMap f j m s hs =
      residualMarkedFiberMap f' j' m' s' hs' ≫ iC := by
    change t ≫ (R).ι ≫ pullback.fst f m = ((R').ι ≫ pullback.fst f' m') ≫ iC
    rw [← Category.assoc t, ht, Category.assoc, ha, Category.assoc]
  have he : residualMarkedFiberMap f' j' m' s' hs' ≫ iC = (t ≫ bE) ≫ d := by
    rw [Category.assoc, hbE]
    exact hcomp.symm
  exact ⟨HD.lift (residualMarkedFiberMap f' j' m' s' hs') (t ≫ bE) he, HD.lift_fst _ _ _⟩

end Residual

section FullParameter

variable {S X C Y : Scheme.{u}} (q : X ⟶ S) (V : S.Opens)
  (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X) (h : j ≫ π = p ≫ q)

/-- With the full parameter, the retained first source has exactly the
original inverse-image range. -/
theorem firstInclusion_range_preimage_top :
    Set.range (firstInclusion q ⊤ V π j p h) =
      (compactificationOpen π V).ι ⁻¹' Set.range j := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨pullback.fst p (parameterOpen q ⊤ V).ι y,
      (congrArg (fun f => f y) (firstInclusion_original q ⊤ V π j p h)).symm⟩
  · rintro ⟨y, hy⟩
    have hq : q (p y) ∈ V := by
      have he := congrArg (fun f : Y ⟶ S => f y) h
      change π (j y) = q (p y) at he
      rw [← he, hy]
      exact x.property
    let z : (parameterOpen q ⊤ V).toScheme := ⟨p y, ⟨trivial, hq⟩⟩
    obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback p (parameterOpen q ⊤ V).ι) y z rfl
    refine ⟨w, (compactificationOpen π V).ι.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun f => f w) (firstInclusion_original q ⊤ V π j p h)).trans
      ((congrArg j hw).trans hy)

/-- The original target range is preserved by the same coefficient restriction. -/
theorem targetInclusion_range_preimage_top (jA : X ⟶ C) (hA : jA ≫ π = (𝟙 X) ≫ q) :
    Set.range (targetInclusion q V π jA hA) =
      (compactificationOpen π V).ι ⁻¹' Set.range jA := by
  change Set.range (⇑(firstInclusion q ⊤ V π jA (𝟙 X) hA) ∘
    ⇑(inv (firstMap q ⊤ V (𝟙 X)))) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr (inv (firstMap q ⊤ V (𝟙 X))).surjective,
    Set.image_univ]
  exact firstInclusion_range_preimage_top q V π jA (𝟙 X) hA

/-- The original infinity boundary still covers the omitted target locus. -/
theorem targetInclusion_boundary_cover_top {D : Scheme.{u}}
    (jA : X ⟶ C) (hA : jA ≫ π = (𝟙 X) ≫ q) (d : D ⟶ C)
    (hcover : (Set.range jA)ᶜ ⊆ Set.range d) :
    (Set.range (targetInclusion q V π jA hA))ᶜ ⊆ Set.range (sourceBaseMap π V d) := by
  rw [targetInclusion_range_preimage_top, sourceBaseMap_range_preimage]
  intro x hx
  exact hcover hx

end FullParameter

section Paired

variable {S X Y P C Z D : Scheme.{u}} (q : X ⟶ S) (V : S.Opens)
  (π : P ⟶ S) (f : C ⟶ P) [IsFinite f]
  (jB : Y ⟶ C) [IsOpenImmersion jB] (jA : X ⟶ P) [IsOpenImmersion jA]
  (p : Y ⟶ X) (hRet : jB ≫ f = p ≫ jA)
  (hB : jB ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (d : D ⟶ C)

local notation "f'" => (sourceBaseMap π V f)
local notation "jB'" => (firstInclusion q ⊤ V (f ≫ π) jB p hB)
local notation "jA'" => (targetInclusion q V π jA hA)
local notation "p'" => (firstMap q ⊤ V p)
local notation "z'" => (markToParameter q ⊤ V z (fun _ _ ↦ trivial))
local notation "s'" => (closedLift q ⊤ V z (fun _ _ ↦ trivial) p s hs)
local notation "Hmark" => (pairedMark_isPullback f jB jA p hRet z s H)
local notation "Hslice" => (closedLift_isPullback q ⊤ V z (fun _ _ ↦ trivial) p s hs H)
local notation "hRet'" => (firstInclusion_comp_coefficientMap q V π jA hA f jB p hRet hB)
local notation "Hmark'" => (pairedMark_isPullback f' jB' jA' p' hRet' z' s' Hslice)
local notation "R" => (residualMarkedFiberOpen f jB (z ≫ jA) s
  (markedSection_original_equation f jB (z ≫ jA) s Hmark))
local notation "R'" => (residualMarkedFiberOpen f' jB' (z' ≫ jA') s'
  (markedSection_original_equation f' jB' (z' ≫ jA') s' Hmark'))

omit [IsOpenImmersion jB] in
/-- The entire residual marked factor in the refined diagram maps to the
original restricted source boundary. -/
theorem exists_refined_residualBoundary_factor (bE : (R).toScheme ⟶ D)
    (hbE : bE ≫ d = residualMarkedFiberMap f jB (z ≫ jA) s
      (markedSection_original_equation f jB (z ≫ jA) s Hmark)) :
    ∃ bE' : (R').toScheme ⟶ (sourceBaseOpen (f ≫ π) V d).toScheme,
      bE' ≫ sourceBaseMap (f ≫ π) V d =
        residualMarkedFiberMap f' jB' (z' ≫ jA') s'
          (markedSection_original_equation f' jB' (z' ≫ jA') s' Hmark') := by
  have hm : (z' ≫ jA') ≫ (compactificationOpen π V).ι = (markOpen q V z).ι ≫ (z ≫ jA) := by
    rw [Category.assoc, targetInclusion_original, ← Category.assoc, markToParameter_original,
      Category.assoc]
  exact exists_residualBoundary_factor_of_open_comparison f jB (z ≫ jA) s Hmark
    f' jB' (z' ≫ jA') s' Hmark'
    (compactificationOpen (f ≫ π) V).ι (compactificationOpen π V).ι (markOpen q V z).ι
    (sourceBaseMap_original π V f) hm (firstInclusion_range_preimage_top q V (f ≫ π) jB p hB)
    d (sourceBaseMap (f ≫ π) V d) (sourceBaseOpen (f ≫ π) V d).ι
    (sourceBaseMap_isPullback (f ≫ π) V d) bE hbE

end Paired

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
