/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleIntegralBase
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.PolynomialGeometry

/-!
# Retained geometry on the original etale-stage component

The stage is an actual original affine smooth-site neighborhood. On its actual normal component,
retain the original open and its whole closed boundary by native pullbacks. The retained open is
an affine smooth-site object, while the normal proper compactification need not be smooth.
Boundary finiteness here is not mistaken for boundary nonemptiness or surjectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Projectivity of the original structure map also holds for the native swapped pullback. -/
theorem isProjectiveMorphism_pullback_fst {N A T : Scheme.{u}}
    (p : N ⟶ A) (f : T ⟶ A) (hp : IsProjectiveMorphism p) :
    IsProjectiveMorphism (pullback.fst f p) := by
  obtain ⟨n, j, hj, hcomp⟩ := hp.baseChange f
  have := hj
  refine ⟨n, (pullbackSymmetry f p).hom ≫ j, inferInstance, ?_⟩
  rw [Category.assoc, hcomp, pullbackSymmetry_hom_comp_snd]

namespace SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N Y D : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The same actual normal component at an original etale stage retains the original affine
smooth open and full finite boundary. The displayed smooth-site object is the retained open,
not the strict henselization and not the normal proper compactification. -/
theorem retainedGeometry_etaleNeighborhood_normalComponent
    [IsLocallyNoetherian X.left] [IsAffine X.left] [IsNormal N] [IsAffine Y]
    (p : N ⟶ X.left) [IsProper p]
    (j : Y ⟶ N) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ p)]
    (b : D ⟶ N) [IsClosedImmersion b] [IsFinite (b ≫ p)]
    (hb : Set.range b = (Set.range j)ᶜ) (i : EtaleNeighborhood X s.hom)
    (x : (pullback p (etaleNeighborhoodHom X s.hom i).left : Scheme.{u}))
    (hx : x ∈ Set.range (pullback.fst
      (pullback.fst p (etaleNeighborhoodHom X s.hom i).left) j)) :
    let f := (etaleNeighborhoodHom X s.hom i).left
    let q := pullback.snd p f
    let j' := pullback.fst (pullback.fst p f) j
    let b' := pullback.fst (pullback.fst p f) b
    let U := normalComponentOpen x
    let r := pullback.fst U.ι j' ≫ U.ι ≫ q
    IsIntegral U.toScheme ∧ IsNoetherian U.toScheme ∧ IsProper (U.ι ≫ q) ∧
      (IsProjectiveMorphism p → IsProjectiveMorphism (U.ι ≫ q)) ∧
      IsIntegral (pullback U.ι j') ∧ IsNoetherian (pullback U.ι j') ∧
      IsAffine (pullback U.ι j') ∧ IsDominant (pullback.fst U.ι j') ∧
      SmoothOfRelativeDimension 1 r ∧ IsClosedImmersion (pullback.fst U.ι b') ∧
      IsFinite (pullback.fst U.ι b' ≫ U.ι ≫ q) ∧
      Set.range (pullback.fst U.ι b') = (Set.range (pullback.fst U.ι j'))ᶜ ∧
      ∃ (W : SmoothSite S) (e : W.left ≅ pullback U.ι j'),
        e.hom ≫ r ≫ ((etaleNeighborhoodToSmooth X s.hom).obj i).hom = W.hom := by
  intro f q j' b' U r
  have : IsNoetherian (pullback p f) :=
    etaleNeighborhood_pullback_isNoetherian X s.hom p i
  have : IsNormal (pullback p f) := etaleNeighborhood_pullback_isNormal X s.hom p i
  have : IsOpenImmersion j' := inferInstanceAs
    (IsOpenImmersion (pullback.fst (pullback.fst p f) j))
  have : IsClosedImmersion b' := inferInstanceAs
    (IsClosedImmersion (pullback.fst (pullback.fst p f) b))
  have : IsClosedImmersion U.ι := inferInstanceAs
    (IsClosedImmersion (normalComponentOpen x).ι)
  have : IsProper q := inferInstanceAs (IsProper (pullback.snd p f))
  have hsq := (IsPullback.of_hasPullback (pullback.fst p f) j).flip.paste_vert
    (IsPullback.of_hasPullback p f)
  have hsm : SmoothOfRelativeDimension 1 (j' ≫ q) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) hsq inferInstance
  have : IsAffineHom (j' ≫ q) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hsq inferInstance
  have : IsAffine (pullback (pullback.fst p f) j) := isAffine_of_isAffineHom (j' ≫ q)
  have : IsFinite (b' ≫ q) :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      ((IsPullback.of_hasPullback (pullback.fst p f) b).flip.paste_vert
        (IsPullback.of_hasPullback p f)) inferInstance
  have hbrange : Set.range b' = (Set.range j')ᶜ := by
    rw [Pullback.range_fst, Pullback.range_fst, hb]
    rfl
  have hx' : (⟨x, mem_normalComponentOpen x⟩ : U.toScheme) ∈
      Set.range (pullback.fst U.ι j') := by
    rw [Pullback.range_fst]
    exact hx
  obtain ⟨z, -⟩ := hx'
  have : Nonempty (pullback U.ι j' : Scheme.{u}) := ⟨z⟩
  have : IsIntegral (pullback U.ι j') := isIntegral_of_isOpenImmersion (pullback.fst U.ι j')
  have : IsAffine (pullback U.ι j') := isAffine_of_isAffineHom (pullback.snd U.ι j')
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ q)
  have : IsNoetherian U.toScheme := ⟨⟩
  have : IsLocallyNoetherian (pullback U.ι j') :=
    isLocallyNoetherian_of_isOpenImmersion (pullback.fst U.ι j')
  have : IsNoetherian (pullback U.ι j') := ⟨⟩
  have hsm' : SmoothOfRelativeDimension 1 r :=
    smoothOfRelativeDimension_normalComponentOpen q j' 1 x
  have hdom : IsDominant (pullback.fst U.ι j') :=
    ⟨(pullback.fst U.ι j').isOpenMap.isOpen_range.dense (Set.range_nonempty _)⟩
  let a : ((etaleNeighborhoodToSmooth X s.hom).obj i).left ⟶ S :=
    ((etaleNeighborhoodToSmooth X s.hom).obj i).hom
  have : Smooth r := SmoothOfRelativeDimension.smooth 1 r
  have : Smooth (r ≫ a) := inferInstance
  have : IsSeparated r := inferInstanceAs
    (IsSeparated (pullback.fst U.ι j' ≫ U.ι ≫ q))
  have : IsSeparated (r ≫ a) := inferInstance
  have : QuasiCompact (r ≫ a) := quasiCompact_of_compactSpace (r ≫ a)
  exact ⟨inferInstance, inferInstance, inferInstance,
    fun hp => isProjectiveMorphism_normalComponentOpen q
      (hp.baseChange f) x,
    inferInstance, inferInstance, inferInstance, hdom, hsm', inferInstance, inferInstance,
    range_normalComponentBoundary j' b' hbrange x, mk (r ≫ a), Iso.refl _, by
      change (𝟙 _ ≫ r ≫ a) = r ≫ a
      rw [Category.id_comp]⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every actual curve cone leg preserves membership in the original retained open. The
point can therefore be the specialization of either of the original strict-local sections. -/
theorem etaleCurveCone_mem_retainedOpen
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left) (p : N ⟶ X.left) (j : Y ⟶ N)
    (x : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}))
    (hx : x ∈ Set.range (pullback.fst
      (pullback.fst p (strictHenselizationToBase B X.left hX s)) j))
    (i : SmallEtaleNeighborhood X s) :
    ((etaleCurveConeOriginalIso X B hX s p).hom ≫
      (etaleCurveCone X B hX s p).π.app i) x ∈
        Set.range (pullback.fst (pullback.snd
          ((smallEtaleNeighborhoodOver X s).obj i).hom p) j) := by
  rw [Pullback.range_fst] at hx ⊢
  have h : ((etaleCurveConeOriginalIso X B hX s p).hom ≫
      (etaleCurveCone X B hX s p).π.app i) ≫
      pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p =
        pullback.fst p (strictHenselizationToBase B X.left hX s) := by
    rw [Category.assoc, etaleCurveCone_π_snd]
    exact pullbackSymmetry_hom_comp_snd _ _
  change (((etaleCurveConeOriginalIso X B hX s p).hom ≫
    (etaleCurveCone X B hX s p).π.app i) ≫
      pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p) x ∈ Set.range j
  rw [h]
  exact hx

/-- The actual component descends after any requested common stage, with its original retained
point. No stage nonemptiness or stage-component certificate is an input. -/
theorem exists_originalComponent_etaleCurve_retained_preimage_eq_over
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    [IsLocallyNoetherian X.left] [IsNormal N]
    (p : N ⟶ X.left) [IsProper p] (j : Y ⟶ N)
    (x : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}))
    (hx : x ∈ Set.range (pullback.fst
      (pullback.fst p (strictHenselizationToBase B X.left hX s)) j))
    (i₀ : SmallEtaleNeighborhood X s) :
    let c := etaleCurveCone X B hX s p
    let e := etaleCurveConeOriginalIso X B hX s p
    ∃ (i : SmallEtaleNeighborhood X s) (_ : i ⟶ i₀),
      (((e.hom ≫ c.π.app i) ⁻¹ᵁ normalComponentOpen ((e.hom ≫ c.π.app i) x)) :
        Set (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u})) =
          _root_.irreducibleComponent x ∧
      (e.hom ≫ c.π.app i) x ∈ Set.range (pullback.fst
        (pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p) j) := by
  obtain ⟨i, f, hi⟩ := exists_originalComponent_etaleCurve_preimage_eq_over X B hX s p x i₀
  exact ⟨i, f, hi, etaleCurveCone_mem_retainedOpen X s B hX p j x hx i⟩

end SmoothSite

end AlgebraicGeometry.Scheme
