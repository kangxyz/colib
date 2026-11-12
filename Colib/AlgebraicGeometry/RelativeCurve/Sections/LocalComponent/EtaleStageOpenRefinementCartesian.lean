/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenIntegralBaseRefinement

/-! # The actual refined curve remains Cartesian over the fixed stage open -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  (a : Over i) (Anew : EtaleNeighborhood X s.hom)
  (v : Anew ⟶ (smallEtaleNeighborhoodInclusion X s).obj a.left)

/-- The composite square is constructed from the actual stage square and the
literal base change. It is not an additional compatibility input. -/
theorem etaleStageOpenRefinement_fixed_isPullback :
    let g := ((etaleNeighborhoodToSmooth X s.hom).map v).left
    let q := (etaleStageOpenStructure X s p i U).app a
    IsPullback
      (pullback.fst q g ≫ pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι)
      (pullback.snd q g)
      (U.ι ≫ (etaleCurveStructure X s p).app i)
      (g ≫ (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom) := by
  intro g q
  exact (IsPullback.of_hasPullback q g).paste_horiz
    (etaleStageOpenStructure_isPullback X s p i U a)

/-- The actual projection to the fixed model is etale, including for the original
integral neighborhood outside the chosen small indexing category. -/
theorem etaleStageOpenRefinement_fixed_etale :
    let g := ((etaleNeighborhoodToSmooth X s.hom).map v).left
    let q := (etaleStageOpenStructure X s p i U).app a
    Etale (pullback.fst q g ≫
      pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι) := by
  intro g q
  have hg : Etale g := by
    change Etale (((AffineEtale.Spec X.left).map v.hom).left)
    infer_instance
  have hi : Etale ((smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom) := by
    change Etale (((AffineEtale.Spec X.left).map
      (((smallEtaleNeighborhoodInclusion X s).map a.hom).hom)).left)
    infer_instance
  have hcomp : Etale (g ≫
      (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom) := inferInstance
  exact MorphismProperty.of_isPullback (P := @Etale)
    (etaleStageOpenRefinement_fixed_isPullback X s p i U a Anew v).flip hcomp

end AlgebraicGeometry.Scheme.SmoothSite
