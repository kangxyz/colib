/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.Boundary
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineChartMorphisms

/-!
# Transport the original projective-line cover and coordinate charts

The cover and each coordinate chart are transported to the actual base-changed curve using
native cartesian squares for the projective and affine lines. The original curve projection,
finite cover and chart equations are retained. These are the inputs needed to establish that
the full boundary meets the same strict-local component as the original sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {A R : Type u} [CommRing A] [CommRing R]
  {X Y : Scheme.{u}} (p : X ⟶ Spec (.of A)) (f : A →+* R)

/-- The original projective-line map on the actual base-changed curve. -/
def projectiveLineCoverBaseChange (π : X ⟶ projectiveLine A)
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    pullback p (Spec.map (CommRingCat.ofHom f)) ⟶ projectiveLine R :=
  (isPullback_projectiveLineMap f).lift (pullback.fst p _ ≫ π) (pullback.snd p _)
    (by rw [Category.assoc, hπ, pullback.condition])

/-- The transported map retains the original projective coordinate map. -/
@[reassoc (attr := simp)] theorem projectiveLineCoverBaseChange_map
    (π : X ⟶ projectiveLine A) (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    projectiveLineCoverBaseChange p f π hπ ≫ projectiveLineMap f =
      pullback.fst p (Spec.map (CommRingCat.ofHom f)) ≫ π :=
  (isPullback_projectiveLineMap f).lift_fst _ _ _

/-- The transported finite cover lies over the unchanged actual base projection. -/
@[reassoc (attr := simp)] theorem projectiveLineCoverBaseChange_structure
    (π : X ⟶ projectiveLine A) (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    projectiveLineCoverBaseChange p f π hπ ≫ (projectiveLine R ↘ Spec (.of R)) =
      pullback.snd p (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_projectiveLineMap f).lift_snd _ _ _

/-- The transported cover is the actual base change of the original finite cover. -/
theorem isPullback_projectiveLineCoverBaseChange
    (π : X ⟶ projectiveLine A) (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    IsPullback (pullback.fst p (Spec.map (CommRingCat.ofHom f)))
      (projectiveLineCoverBaseChange p f π hπ) π (projectiveLineMap f) := by
  have houter : IsPullback (pullback.fst p (Spec.map (CommRingCat.ofHom f)))
      (projectiveLineCoverBaseChange p f π hπ ≫ (projectiveLine R ↘ Spec (.of R)))
      (π ≫ (projectiveLine A ↘ Spec (.of A))) (Spec.map (CommRingCat.ofHom f)) := by
    simpa only [hπ, projectiveLineCoverBaseChange_structure] using
      IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom f))
  exact houter.of_bot (projectiveLineCoverBaseChange_map p f π hπ).symm
    (isPullback_projectiveLineMap f)

/-- Finiteness of the original projective-line cover survives on this actual base change. -/
instance isFinite_projectiveLineCoverBaseChange
    (π : X ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    IsFinite (projectiveLineCoverBaseChange p f π hπ) :=
  MorphismProperty.of_isPullback (isPullback_projectiveLineCoverBaseChange p f π hπ) inferInstance

/-- The original affine coordinate chart on its actual base-changed source. -/
def affineLineChartBaseChange (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p) :
    pullback (pullback.fst p (Spec.map (CommRingCat.ofHom f))) j ⟶ Spec (.of (Polynomial R)) :=
  (isPullback_Spec_map_mapRingHom f).lift (pullback.snd _ j ≫ a)
    (pullback.fst _ j ≫ pullback.snd p _) (by
      rw [Category.assoc, ha, ← Category.assoc, ← pullback.condition, Category.assoc,
        pullback.condition, Category.assoc])

/-- The transported coordinate map preserves the original affine coordinate. -/
@[reassoc (attr := simp)] theorem affineLineChartBaseChange_map
    (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p) :
    affineLineChartBaseChange p f j a ha ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) =
        pullback.snd (pullback.fst p (Spec.map (CommRingCat.ofHom f))) j ≫ a :=
  (isPullback_Spec_map_mapRingHom f).lift_fst _ _ _

/-- The transported affine chart lies over the actual base projection. -/
@[reassoc (attr := simp)] theorem affineLineChartBaseChange_structure
    (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p) :
    affineLineChartBaseChange p f j a ha ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
        pullback.fst (pullback.fst p (Spec.map (CommRingCat.ofHom f))) j ≫
          pullback.snd p (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_Spec_map_mapRingHom f).lift_snd _ _ _

/-- The transported affine coordinate map is the actual base change of the original one. -/
theorem isPullback_affineLineChartBaseChange
    (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p) :
    IsPullback (pullback.snd (pullback.fst p (Spec.map (CommRingCat.ofHom f))) j)
      (affineLineChartBaseChange p f j a ha) a
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))) := by
  have houter := (IsPullback.of_hasPullback
    (pullback.fst p (Spec.map (CommRingCat.ofHom f))) j).flip.paste_vert
      (IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom f)))
  have houter' : IsPullback (pullback.snd (pullback.fst p (Spec.map (CommRingCat.ofHom f))) j)
      (affineLineChartBaseChange p f j a ha ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
      (a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
      (Spec.map (CommRingCat.ofHom f)) := by
    simpa only [ha, affineLineChartBaseChange_structure] using houter
  exact houter'.of_bot (affineLineChartBaseChange_map p f j a ha).symm
    (isPullback_Spec_map_mapRingHom f)

/-- Etaleness of the same original coordinate chart survives actual base change. -/
instance etale_affineLineChartBaseChange
    (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A))) [Etale a]
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p) :
    Etale (affineLineChartBaseChange p f j a ha) :=
  MorphismProperty.of_isPullback (isPullback_affineLineChartBaseChange p f j a ha) inferInstance

/-- The original compactification chart equation is retained after base change. -/
theorem affineLineChartBaseChange_comp_XChart
    (π : X ⟶ projectiveLine A) (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A) :
    pullback.fst (pullback.fst p (Spec.map (CommRingCat.ofHom f))) j ≫
      projectiveLineCoverBaseChange p f π hπ =
        affineLineChartBaseChange p f j a ha ≫ projectiveLineXChart R := by
  apply (isPullback_projectiveLineMap f).hom_ext
  · simp only [Category.assoc, projectiveLineCoverBaseChange_map,
      projectiveLineXChart_comp_projectiveLineMap, affineLineChartBaseChange_map_assoc]
    rw [← Category.assoc, pullback.condition, Category.assoc, hj]
  · simp only [Category.assoc, projectiveLineCoverBaseChange_structure,
      projectiveLineXChart_comp_structureMorphism]
    exact (affineLineChartBaseChange_structure p f j a ha).symm

end AlgebraicGeometry.Scheme
