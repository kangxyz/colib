/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleCurveFixedClopenSections
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRetainedTargetFamily
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.RetainedGeometry

/-! # Retained source and original target on the selected fixed clopen

First base-change the original affine retained source, then restrict it to the
actual final clopen. The target is the original map composed with the two
projections. Sections and the map to the base-target product are constructed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Actual base change followed by the chosen clopen restriction produces the
fixed retained target data needed by `EtaleStageOpenRetainedTargetFamily`. -/
theorem exists_fixedClopen_retained_target_pair
    {S : Scheme.{u}} {A A' T : SmoothSite S} (b : A' ⟶ A)
    {C C' Y : Scheme.{u}} (q : C ⟶ A.left) (q' : C' ⟶ A'.left)
    (F : C' ⟶ C) [IsAffineHom F] (hp : IsPullback F q' q b.left)
    (U : C'.Opens) [IsClosedImmersion U.ι]
    (j : Y ⟶ C) [IsAffine Y] [IsOpenImmersion j]
    [hSmoothOriginal : SmoothOfRelativeDimension 1 (j ≫ q)]
    (σ τ : A.left ⟶ C) (σY τY : A.left ⟶ Y)
    (hσY : σY ≫ j = σ) (hτY : τY ≫ j = τ)
    (σU τU : A'.left ⟶ U.toScheme)
    (hsF : σU ≫ U.ι ≫ F = b.left ≫ σ)
    (htF : τU ≫ U.ι ≫ F = b.left ≫ τ)
    (t : Y ⟶ T.left) (ht : t ≫ T.hom = j ≫ q ≫ A.hom)
    (f₀ g₀ : A ⟶ T) (hf₀ : f₀.left = σY ≫ t) (hg₀ : g₀.left = τY ≫ t) :
    let j₁ := pullback.fst F j
    let V := pullback U.ι j₁
    let jV := pullback.fst U.ι j₁
    IsAffine V ∧ IsOpenImmersion jV ∧ SmoothOfRelativeDimension 1 (jV ≫ U.ι ≫ q') ∧
    ∃ (σV τV : A'.left ⟶ V) (r : V ⟶ pullback A'.hom T.hom),
      σV ≫ jV = σU ∧ τV ≫ jV = τU ∧
      r ≫ pullback.fst A'.hom T.hom = jV ≫ U.ι ≫ q' ∧
      r ≫ pullback.snd A'.hom T.hom =
        pullback.snd U.ι j₁ ≫ pullback.snd F j ≫ t ∧
      (b ≫ f₀).left = σV ≫ r ≫ pullback.snd A'.hom T.hom ∧
      (b ≫ g₀).left = τV ≫ r ≫ pullback.snd A'.hom T.hom := by
  intro j₁ V jV
  let v₁ := pullback.snd F j
  let v₂ := pullback.snd U.ι j₁
  have hσ : (σU ≫ U.ι) ≫ F = (b.left ≫ σY) ≫ j := by
    simpa only [Category.assoc, hσY] using hsF
  have hτ : (τU ≫ U.ι) ≫ F = (b.left ≫ τY) ≫ j := by
    simpa only [Category.assoc, hτY] using htF
  let σ₁ := pullback.lift (σU ≫ U.ι) (b.left ≫ σY) hσ
  let τ₁ := pullback.lift (τU ≫ U.ι) (b.left ≫ τY) hτ
  let σV : A'.left ⟶ V := pullback.lift σU σ₁ (pullback.lift_fst _ _ _).symm
  let τV : A'.left ⟶ V := pullback.lift τU τ₁ (pullback.lift_fst _ _ _).symm
  have hsV : σV ≫ jV = σU := pullback.lift_fst _ _ _
  have htV : τV ≫ jV = τU := pullback.lift_fst _ _ _
  have hsOld : σV ≫ v₂ ≫ v₁ = b.left ≫ σY := by
    rw [← Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have htOld : τV ≫ v₂ ≫ v₁ = b.left ≫ τY := by
    rw [← Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have w₂ : jV ≫ U.ι = v₂ ≫ j₁ := pullback.condition
  have w₁ : j₁ ≫ F = v₁ ≫ j := pullback.condition
  have hbase : (jV ≫ U.ι ≫ q') ≫ b.left = (v₂ ≫ v₁ ≫ j) ≫ q := by
    calc
      _ = jV ≫ U.ι ≫ (q' ≫ b.left) := by simp only [Category.assoc]
      _ = jV ≫ U.ι ≫ (F ≫ q) := congrArg (fun z => jV ≫ U.ι ≫ z) hp.w.symm
      _ = ((jV ≫ U.ι) ≫ F) ≫ q := by simp only [Category.assoc]
      _ = ((v₂ ≫ j₁) ≫ F) ≫ q := congrArg (fun z => (z ≫ F) ≫ q) w₂
      _ = (v₂ ≫ (j₁ ≫ F)) ≫ q := by simp only [Category.assoc]
      _ = _ := congrArg (fun z => (v₂ ≫ z) ≫ q) w₁
  have hw : (jV ≫ U.ι ≫ q') ≫ A'.hom = (v₂ ≫ v₁ ≫ t) ≫ T.hom := by
    calc
      _ = (jV ≫ U.ι ≫ q') ≫ (b.left ≫ A.hom) :=
        congrArg (fun z => (jV ≫ U.ι ≫ q') ≫ z) b.w.symm
      _ = ((jV ≫ U.ι ≫ q') ≫ b.left) ≫ A.hom := (Category.assoc _ _ _).symm
      _ = ((v₂ ≫ v₁ ≫ j) ≫ q) ≫ A.hom := congrArg (fun z => z ≫ A.hom) hbase
      _ = (v₂ ≫ v₁) ≫ (j ≫ q ≫ A.hom) := by simp only [Category.assoc]
      _ = (v₂ ≫ v₁) ≫ (t ≫ T.hom) := congrArg (fun z => (v₂ ≫ v₁) ≫ z) ht.symm
      _ = _ := by simp only [Category.assoc]
  let r : V ⟶ pullback A'.hom T.hom :=
    pullback.lift (jV ≫ U.ι ≫ q') (v₂ ≫ v₁ ≫ t) hw
  have hr₁ : r ≫ pullback.fst A'.hom T.hom = jV ≫ U.ι ≫ q' := pullback.lift_fst _ _ _
  have hr₂ : r ≫ pullback.snd A'.hom T.hom = v₂ ≫ v₁ ≫ t := pullback.lift_snd _ _ _
  have hAff : IsAffine V := isAffine_of_isAffineHom (v₂ ≫ v₁)
  have hSmooth₁ : SmoothOfRelativeDimension 1 (j₁ ≫ q') :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      ((IsPullback.of_hasPullback F j).flip.paste_vert hp) inferInstance
  have hSmooth : SmoothOfRelativeDimension 1 (jV ≫ U.ι ≫ q') := by
    rw [← Category.assoc, w₂, Category.assoc]
    have h : SmoothOfRelativeDimension (0 + 1) (v₂ ≫ (j₁ ≫ q')) :=
      smoothOfRelativeDimension_comp 0 1 _ _
    exact h
  refine ⟨hAff, inferInstance, hSmooth, σV, τV, r, hsV, htV, hr₁, hr₂, ?_, ?_⟩
  · change b.left ≫ f₀.left = _
    calc
      _ = b.left ≫ (σY ≫ t) := congrArg (fun z => b.left ≫ z) hf₀
      _ = (b.left ≫ σY) ≫ t := (Category.assoc _ _ _).symm
      _ = (σV ≫ v₂ ≫ v₁) ≫ t := congrArg (fun z => z ≫ t) hsOld.symm
      _ = σV ≫ (v₂ ≫ v₁ ≫ t) := by simp only [Category.assoc]
      _ = _ := congrArg (fun z => σV ≫ z) hr₂.symm
  · change b.left ≫ g₀.left = _
    calc
      _ = b.left ≫ (τY ≫ t) := congrArg (fun z => b.left ≫ z) hg₀
      _ = (b.left ≫ τY) ≫ t := (Category.assoc _ _ _).symm
      _ = (τV ≫ v₂ ≫ v₁) ≫ t := congrArg (fun z => z ≫ t) htOld.symm
      _ = τV ≫ (v₂ ≫ v₁ ≫ t) := by simp only [Category.assoc]
      _ = _ := congrArg (fun z => τV ≫ z) hr₂.symm


/-- Instantiate the retained-target construction on the two actual small arrows
returned by `EtaleCurveFixedClopenSections`. The original retained source is only
pulled back; its target is never extended to the whole compactified curve. -/
theorem exists_etaleCurve_fixedClopen_retained_target_pair
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
    {i₀ i : SmallEtaleNeighborhood X s} (e : i ⟶ i₀) (a : Over i)
    (U : ((etaleCurveDiagram X s p).obj a.left).Opens) [IsClosedImmersion U.ι]
    {Y : Scheme.{u}} (j : Y ⟶ (etaleCurveDiagram X s p).obj i₀)
    [IsAffine Y] [IsOpenImmersion j]
    [hSmoothOriginal : SmoothOfRelativeDimension 1 (j ≫ (etaleCurveStructure X s p).app i₀)]
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i₀ ⟶
      (etaleCurveDiagram X s p).obj i₀)
    (σY τY : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i₀ ⟶ Y)
    (hσY : σY ≫ j = σ) (hτY : τY ≫ j = τ)
    (σi τi : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶
      (etaleCurveDiagram X s p).obj i)
    (hs₁ : σi ≫ (etaleCurveDiagram X s p).map e =
      (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map e ≫ σ)
    (ht₁ : τi ≫ (etaleCurveDiagram X s p).map e =
      (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map e ≫ τ)
    (σU τU : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶ U.toScheme)
    (hs₂ : σU ≫ U.ι ≫ (etaleCurveDiagram X s p).map a.hom =
      (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom ≫ σi)
    (ht₂ : τU ≫ U.ι ≫ (etaleCurveDiagram X s p).map a.hom =
      (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom ≫ τi)
    {T : SmoothSite S} (t : Y ⟶ T.left)
    (ht : t ≫ T.hom = j ≫ (etaleCurveStructure X s p).app i₀ ≫
      ((smallEtaleNeighborhoodToSmooth X s).obj i₀).hom)
    (f₀ g₀ : (smallEtaleNeighborhoodToSmooth X s).obj i₀ ⟶ T)
    (hf₀ : f₀.left = σY ≫ t) (hg₀ : g₀.left = τY ≫ t) :
    let F := (etaleCurveDiagram X s p).map (a.hom ≫ e)
    let b := (smallEtaleNeighborhoodToSmooth X s).map (a.hom ≫ e)
    let A' := (smallEtaleNeighborhoodToSmooth X s).obj a.left
    let q' := (etaleCurveStructure X s p).app a.left
    let j₁ := pullback.fst F j
    let V := pullback U.ι j₁
    let jV := pullback.fst U.ι j₁
    IsAffine V ∧ IsOpenImmersion jV ∧ SmoothOfRelativeDimension 1 (jV ≫ U.ι ≫ q') ∧
    ∃ (σV τV : A'.left ⟶ V) (r : V ⟶ pullback A'.hom T.hom),
      σV ≫ jV = σU ∧ τV ≫ jV = τU ∧
      r ≫ pullback.fst A'.hom T.hom = jV ≫ U.ι ≫ q' ∧
      r ≫ pullback.snd A'.hom T.hom =
        pullback.snd U.ι j₁ ≫ pullback.snd F j ≫ t ∧
      (b ≫ f₀).left = σV ≫ r ≫ pullback.snd A'.hom T.hom ∧
      (b ≫ g₀).left = τV ≫ r ≫ pullback.snd A'.hom T.hom := by
  intro F b A' q' j₁ V jV
  let D := etaleCurveDiagram X s p
  let G := smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S
  have hs : σU ≫ U.ι ≫ F = b.left ≫ σ := by
    calc
      _ = (σU ≫ U.ι ≫ D.map a.hom) ≫ D.map e :=
        (congrArg (fun z : D.obj a.left ⟶ D.obj i₀ => σU ≫ U.ι ≫ z)
          (D.map_comp a.hom e)).trans
        ((Category.assoc σU U.ι (D.map a.hom ≫ D.map e)).symm.trans
        ((Category.assoc (σU ≫ U.ι) (D.map a.hom) (D.map e)).symm.trans
          (congrArg (fun z => z ≫ D.map e) (Category.assoc σU U.ι (D.map a.hom)))))
      _ = (G.map a.hom ≫ σi) ≫ D.map e := congrArg (fun z => z ≫ D.map e) hs₂
      _ = G.map a.hom ≫ (σi ≫ D.map e) := Category.assoc _ _ _
      _ = G.map a.hom ≫ (G.map e ≫ σ) := congrArg (fun z => G.map a.hom ≫ z) hs₁
      _ = (G.map a.hom ≫ G.map e) ≫ σ := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun z => z ≫ σ) (G.map_comp a.hom e).symm
  have hτ : τU ≫ U.ι ≫ F = b.left ≫ τ := by
    calc
      _ = (τU ≫ U.ι ≫ D.map a.hom) ≫ D.map e :=
        (congrArg (fun z : D.obj a.left ⟶ D.obj i₀ => τU ≫ U.ι ≫ z)
          (D.map_comp a.hom e)).trans
        ((Category.assoc τU U.ι (D.map a.hom ≫ D.map e)).symm.trans
        ((Category.assoc (τU ≫ U.ι) (D.map a.hom) (D.map e)).symm.trans
          (congrArg (fun z => z ≫ D.map e) (Category.assoc τU U.ι (D.map a.hom)))))
      _ = (G.map a.hom ≫ τi) ≫ D.map e := congrArg (fun z => z ≫ D.map e) ht₂
      _ = G.map a.hom ≫ (τi ≫ D.map e) := Category.assoc _ _ _
      _ = G.map a.hom ≫ (G.map e ≫ τ) := congrArg (fun z => G.map a.hom ≫ z) ht₁
      _ = (G.map a.hom ≫ G.map e) ≫ τ := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun z => z ≫ τ) (G.map_comp a.hom e).symm
  exact exists_fixedClopen_retained_target_pair (hSmoothOriginal := hSmoothOriginal) b
    ((etaleCurveStructure X s p).app i₀) q' F
    (etaleCurveDiagram_isPullback X s p (a.hom ≫ e)) U j
    σ τ σY τY hσY hτY σU τU hs hτ t ht f₀ g₀ hf₀ hg₀

end AlgebraicGeometry.Scheme.SmoothSite
