/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenRetainedSections

/-! # The actual retained sections and target maps at every restarted stage

The fixed retained section factors and target map are pulled back through the
existing Cartesian stage squares. The two resulting original smooth-site maps
are the fixed maps precomposed with the actual neighborhood transition.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  {V : Scheme.{u}} (j : V ⟶ U.toScheme)

/-- The specified fixed retained factor lifted into the actual retained stage. -/
def etaleStageOpenRetainedSection
    (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (σV : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ V)
    (hσV : σV ≫ j = σ) (a : Over i) :
    (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶
      (etaleStageOpenBoundaryDiagram X s p i U j).obj a :=
  (etaleStageOpenBoundaryMap_isPullback X s p i U j a).lift
    (etaleStageOpenSection X s p i U σ hσ a)
    ((smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom ≫ σV)
    (by
      rw [etaleStageOpenSection_snd, Category.assoc, hσV])

@[simp, reassoc] theorem etaleStageOpenRetainedSection_map
    (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (σV : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ V)
    (hσV : σV ≫ j = σ) (a : Over i) :
    etaleStageOpenRetainedSection X s p i U j σ hσ σV hσV a ≫
      (etaleStageOpenBoundaryMap X s p i U j).app a =
      etaleStageOpenSection X s p i U σ hσ a :=
  IsPullback.lift_fst _ _ _ _

@[simp, reassoc] theorem etaleStageOpenRetainedSection_snd
    (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (σV : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ V)
    (hσV : σV ≫ j = σ) (a : Over i) :
    etaleStageOpenRetainedSection X s p i U j σ hσ σV hσV a ≫
      pullback.snd ((etaleCurveDiagram X s p).map a.hom) (j ≫ U.ι) =
      (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom ≫ σV :=
  IsPullback.lift_snd _ _ _ _

variable (T : SmoothSite S)
  (r : V ⟶ pullback ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom)

/-- The original retained target on the actual stage, with both actual projections. -/
def etaleStageOpenRetainedTarget
    (hr : r ≫ pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom =
      j ≫ U.ι ≫ (etaleCurveStructure X s p).app i) (a : Over i) :
    (etaleStageOpenBoundaryDiagram X s p i U j).obj a ⟶
      pullback ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom T.hom :=
  pullback.lift
    ((etaleStageOpenBoundaryMap X s p i U j).app a ≫
      (etaleStageOpenStructure X s p i U).app a)
    (pullback.snd ((etaleCurveDiagram X s p).map a.hom) (j ≫ U.ι) ≫
      r ≫ pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom)
    (by
      let ja := (etaleStageOpenBoundaryMap X s p i U j).app a
      let qa := (etaleStageOpenStructure X s p i U).app a
      let va := pullback.snd ((etaleCurveDiagram X s p).map a.hom) (j ≫ U.ι)
      let ua := pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι
      let ga := (smallEtaleNeighborhoodToSmooth X s).map a.hom
      have hga : ga.left ≫ ((smallEtaleNeighborhoodToSmooth X s).obj i).hom =
          ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom := ga.w
      have hq : ua ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = qa ≫ ga.left :=
        (etaleStageOpenStructure_isPullback X s p i U a).w
      have hj : ja ≫ ua = va ≫ j :=
        (etaleStageOpenBoundaryMap_isPullback X s p i U j a).w
      have hbase : (ja ≫ qa) ≫ ga.left =
          (va ≫ j) ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) := by
        have h₁ : (ja ≫ qa) ≫ ga.left =
            ja ≫ (ua ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) :=
          (Category.assoc _ _ _).trans (congrArg (fun z => ja ≫ z) hq.symm)
        have h₂ : ja ≫ (ua ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) =
            (va ≫ j) ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) hj)
        exact h₁.trans h₂
      have hleft : (ja ≫ qa) ≫ ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom =
          ((ja ≫ qa) ≫ ga.left) ≫ ((smallEtaleNeighborhoodToSmooth X s).obj i).hom := by
        exact (congrArg (fun z => (ja ≫ qa) ≫ z) hga.symm).trans
          (Category.assoc _ _ _).symm
      have hmiddle : ((ja ≫ qa) ≫ ga.left) ≫
          ((smallEtaleNeighborhoodToSmooth X s).obj i).hom =
          ((va ≫ j) ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) ≫
            ((smallEtaleNeighborhoodToSmooth X s).obj i).hom :=
        congrArg (fun z => z ≫ ((smallEtaleNeighborhoodToSmooth X s).obj i).hom) hbase
      have htarget : (va ≫ j) ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) =
          (va ≫ r) ≫ pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom := by
        have hr' : j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) =
            r ≫ pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom :=
          hr.symm
        have hpre : va ≫ (j ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) =
            va ≫ (r ≫ pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom) :=
          congrArg (fun z : V ⟶ ((smallEtaleNeighborhoodToSmooth X s).obj i).left => va ≫ z) hr'
        exact (Category.assoc va j _).trans
          (hpre.trans (Category.assoc va r _).symm)
      have hright : ((va ≫ j) ≫ (U.ι ≫ (etaleCurveStructure X s p).app i)) ≫
          ((smallEtaleNeighborhoodToSmooth X s).obj i).hom =
          (va ≫ r ≫ pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom) ≫
            T.hom := by
        have h₁ := congrArg
          (fun z => z ≫ ((smallEtaleNeighborhoodToSmooth X s).obj i).hom) htarget
        have h₂ : ((va ≫ r) ≫
            pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom) ≫
              ((smallEtaleNeighborhoodToSmooth X s).obj i).hom =
            (va ≫ r ≫ pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom) ≫
              T.hom := by
          simpa only [Category.assoc] using congrArg (fun z => (va ≫ r) ≫ z)
            (pullback.condition (f := ((smallEtaleNeighborhoodToSmooth X s).obj i).hom)
              (g := T.hom))
        exact h₁.trans h₂
      exact hleft.trans (hmiddle.trans hright))

variable (hr : r ≫ pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom =
  j ≫ U.ι ≫ (etaleCurveStructure X s p).app i)

@[simp, reassoc] theorem etaleStageOpenRetainedTarget_fst (a : Over i) :
    etaleStageOpenRetainedTarget X s p i U j T r hr a ≫
      pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom T.hom =
      (etaleStageOpenBoundaryMap X s p i U j).app a ≫
        (etaleStageOpenStructure X s p i U).app a :=
  pullback.lift_fst _ _ _

@[simp, reassoc] theorem etaleStageOpenRetainedTarget_snd (a : Over i) :
    etaleStageOpenRetainedTarget X s p i U j T r hr a ≫
      pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom T.hom =
      pullback.snd ((etaleCurveDiagram X s p).map a.hom) (j ≫ U.ι) ≫
        r ≫ pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom :=
  pullback.lift_snd _ _ _

/-- The stage target of the constructed retained section is the unchanged
original smooth-site map precomposed with the actual stage transition. -/
theorem etaleStageOpenRetainedSection_target
    (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (σV : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ V)
    (hσV : σV ≫ j = σ)
    (f₀ : (smallEtaleNeighborhoodToSmooth X s).obj i ⟶ T)
    (hf₀ : f₀.left = σV ≫ r ≫
      pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom) (a : Over i) :
    ((smallEtaleNeighborhoodToSmooth X s).map a.hom ≫ f₀).left =
      etaleStageOpenRetainedSection X s p i U j σ hσ σV hσV a ≫
        etaleStageOpenRetainedTarget X s p i U j T r hr a ≫
          pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom T.hom := by
  calc
    _ = ((smallEtaleNeighborhoodToSmooth X s).map a.hom).left ≫
        σV ≫ r ≫ pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom :=
      congrArg (fun z => ((smallEtaleNeighborhoodToSmooth X s).map a.hom).left ≫ z) hf₀
    _ = _ := by
      rw [etaleStageOpenRetainedTarget_snd]
      have h := etaleStageOpenRetainedSection_snd X s p i U j σ hσ σV hσV a
      exact (congrArg (fun z => z ≫ r ≫
        pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom) h).symm
        |>.trans (Category.assoc _ _ _)

include hr in
/-- Both original sections use the same actual target map at every shared index.
This produces the retained-stage family, rather than assuming a family producer. -/
theorem exists_etaleStageOpenRetainedTarget_pair
    (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
    (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
    (σV τV : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ V)
    (hσV : σV ≫ j = σ) (hτV : τV ≫ j = τ)
    (f₀ g₀ : (smallEtaleNeighborhoodToSmooth X s).obj i ⟶ T)
    (hf₀ : f₀.left = σV ≫ r ≫
      pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom)
    (hg₀ : g₀.left = τV ≫ r ≫
      pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj i).hom T.hom)
    (a : Over i) :
    ∃ (σa τa : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj a.left ⟶
        (etaleStageOpenBoundaryDiagram X s p i U j).obj a)
      (ra : (etaleStageOpenBoundaryDiagram X s p i U j).obj a ⟶
        pullback ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom T.hom),
      σa ≫ (etaleStageOpenBoundaryMap X s p i U j).app a =
        etaleStageOpenSection X s p i U σ hσ a ∧
      τa ≫ (etaleStageOpenBoundaryMap X s p i U j).app a =
        etaleStageOpenSection X s p i U τ hτ a ∧
      ra ≫ pullback.fst ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom T.hom =
        (etaleStageOpenBoundaryMap X s p i U j).app a ≫
          (etaleStageOpenStructure X s p i U).app a ∧
      ((smallEtaleNeighborhoodToSmooth X s).map a.hom ≫ f₀).left =
        σa ≫ ra ≫ pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom T.hom ∧
      ((smallEtaleNeighborhoodToSmooth X s).map a.hom ≫ g₀).left =
        τa ≫ ra ≫ pullback.snd ((smallEtaleNeighborhoodToSmooth X s).obj a.left).hom T.hom := by
  exact ⟨etaleStageOpenRetainedSection X s p i U j σ hσ σV hσV a,
    etaleStageOpenRetainedSection X s p i U j τ hτ τV hτV a,
    etaleStageOpenRetainedTarget X s p i U j T r hr a,
    etaleStageOpenRetainedSection_map X s p i U j σ hσ σV hσV a,
    etaleStageOpenRetainedSection_map X s p i U j τ hτ τV hτV a,
    etaleStageOpenRetainedTarget_fst X s p i U j T r hr a,
    etaleStageOpenRetainedSection_target X s p i U j T r hr σ hσ σV hσV f₀ hf₀ a,
    etaleStageOpenRetainedSection_target X s p i U j T r hr τ hτ τV hτV g₀ hg₀ a⟩

end AlgebraicGeometry.Scheme.SmoothSite
