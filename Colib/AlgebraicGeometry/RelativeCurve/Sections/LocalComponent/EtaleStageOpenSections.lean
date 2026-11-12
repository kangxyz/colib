/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenDiagram
public import Colib.AlgebraicGeometry.Divisors.SectionKernelCartesian

/-! # Actual sections of the restarted component system

A section already factored into the selected finite-stage open is lifted by the
actual Cartesian squares. Compatibility is proved, not supplied as a certificate.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)

/-- The actual component-stage structure maps to the unchanged neighborhood bases. -/
def etaleStageOpenStructure : etaleStageOpenDiagram X s p i U ⟶
    Over.forget i ⋙ smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S where
  app a := pullback.fst ((etaleCurveDiagram X s p).map a.hom) U.ι ≫ (etaleCurveStructure X s
    p).app a.left
  naturality a b v := by
    change pullback.lift _ _ _ ≫
      (pullback.fst ((etaleCurveDiagram X s p).map b.hom) U.ι ≫ (etaleCurveStructure X s p).app
        b.left) =
      (pullback.fst ((etaleCurveDiagram X s p).map a.hom) U.ι ≫ (etaleCurveStructure X s p).app
        a.left) ≫
        (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map v.left
    simp only [pullback.lift_fst_assoc, Category.assoc]
    exact congrArg (fun f => pullback.fst ((etaleCurveDiagram X s p).map a.hom) U.ι ≫ f)
      ((etaleCurveStructure X s p).naturality v.left)

/-- The exact transition preserves the projection to the fixed selected open. -/
@[simp, reassoc] theorem etaleStageOpenDiagram_map_snd {a b : Over i} (v : a ⟶ b) :
    (etaleStageOpenDiagram X s p i U).map v ≫ pullback.snd ((etaleCurveDiagram X s p).map b.hom)
      U.ι = pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι :=
  pullback.lift_snd _ _ _

/-- Each restarted stage is Cartesian over the selected finite-stage component curve. -/
theorem etaleStageOpenStructure_isPullback (a : Over i) :
    IsPullback (pullback.snd ((etaleCurveDiagram X s p).map a.hom) U.ι)
      ((etaleStageOpenStructure X s p i U).app a)
      (U.ι ≫ (etaleCurveStructure X s p).app i) ((smallEtaleNeighborhoodToSmooth X s ⋙
        forgetScheme S).map a.hom) :=
  (IsPullback.of_hasPullback ((etaleCurveDiagram X s p).map a.hom) U.ι).flip.paste_vert
    (etaleCurveDiagram_isPullback X s p a.hom)

/-- The actual component transition is Cartesian over its actual base transition. -/
theorem etaleStageOpenDiagram_isPullback {a b : Over i} (v : a ⟶ b) :
    IsPullback ((etaleStageOpenDiagram X s p i U).map v) ((etaleStageOpenStructure X s p i U).app a)
      ((etaleStageOpenStructure X s p i U).app b) ((smallEtaleNeighborhoodToSmooth X s ⋙
        forgetScheme S).map v.left) := by
  refine IsPullback.of_right ?_ ((etaleStageOpenStructure X s p i U).naturality v)
    (etaleStageOpenStructure_isPullback X s p i U b)
  rw [etaleStageOpenDiagram_map_snd, ← Functor.map_comp, Over.w]
  exact etaleStageOpenStructure_isPullback X s p i U a

variable (σ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
  (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 ((smallEtaleNeighborhoodToSmooth X s ⋙
    forgetScheme S).obj i))

/-- The specified original section lifted to an actual restarted stage. -/
def etaleStageOpenSection (a : Over i) : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme
  S).obj a.left ⟶ (etaleStageOpenDiagram X s p i U).obj a :=
  (etaleStageOpenStructure_isPullback X s p i U a).lift ((smallEtaleNeighborhoodToSmooth X s ⋙
    forgetScheme S).map a.hom ≫ σ) (𝟙 _)
    (by simp only [Category.assoc, hσ, Category.comp_id, Category.id_comp])

@[simp, reassoc] theorem etaleStageOpenSection_snd (a : Over i) :
    etaleStageOpenSection X s p i U σ hσ a ≫ pullback.snd ((etaleCurveDiagram X s p).map a.hom)
      U.ι =
      (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map a.hom ≫ σ := IsPullback.lift_fst
        _ _ _ _

@[simp, reassoc] theorem etaleStageOpenSection_structure (a : Over i) :
    etaleStageOpenSection X s p i U σ hσ a ≫
      (etaleStageOpenStructure X s p i U).app a = 𝟙 _ := IsPullback.lift_snd _ _ _ _

/-- The original section lifts commute with every actual transition, with no
compatibility supplied as an input. -/
theorem etaleStageOpenSection_naturality {a b : Over i} (v : a ⟶ b) :
    etaleStageOpenSection X s p i U σ hσ a ≫ (etaleStageOpenDiagram X s p i U).map v =
      (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map v.left ≫ etaleStageOpenSection X
        s p i U σ hσ b := by
  apply (etaleStageOpenStructure_isPullback X s p i U b).hom_ext
  · simp only [Category.assoc, etaleStageOpenDiagram_map_snd,
      etaleStageOpenSection_snd]
    rw [← Category.assoc, ← Functor.map_comp, Over.w]
  · rw [Category.assoc, (etaleStageOpenStructure X s p i U).naturality v]
    simp only [Category.assoc, etaleStageOpenSection_structure_assoc,
      etaleStageOpenSection_structure, Category.comp_id]
    rfl

/-- The actual lifted sections form Cartesian section squares, ready for the
full-kernel base-change comparison. -/
theorem etaleStageOpenSection_isPullback {a b : Over i} (v : a ⟶ b) :
    IsPullback (etaleStageOpenSection X s p i U σ hσ a) ((smallEtaleNeighborhoodToSmooth X s ⋙
      forgetScheme S).map v.left)
      ((etaleStageOpenDiagram X s p i U).map v) (etaleStageOpenSection X s p i U σ hσ b) :=
  Scheme.isPullback_section_of_isPullback ((etaleStageOpenDiagram X s p i U).map v)
    ((etaleStageOpenStructure X s p i U).app a)
    ((etaleStageOpenStructure X s p i U).app b) ((smallEtaleNeighborhoodToSmooth X s ⋙
      forgetScheme S).map v.left)
    (etaleStageOpenDiagram_isPullback X s p i U v)
    (etaleStageOpenSection X s p i U σ hσ a) (etaleStageOpenSection X s p i U σ hσ b)
    (etaleStageOpenSection_structure X s p i U σ hσ a)
    (etaleStageOpenSection_structure X s p i U σ hσ b)
    (etaleStageOpenSection_naturality X s p i U σ hσ v)

end AlgebraicGeometry.Scheme.SmoothSite
