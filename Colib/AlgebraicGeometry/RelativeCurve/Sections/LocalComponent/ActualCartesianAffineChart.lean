/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualCartesianProjectiveLineCover

/-! # Affine coordinates on the actual Cartesian chart pullback

The chart source is literally pullback v j on the specified actual curve.
The comparison with the native base-change source preserves both projections.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- Pull back the same chart along an actual isomorphism over its original curve. -/
def chartPullbackOverIso {P Q T Y : Scheme.{u}} (e : P ≅ Q)
    (v : P ⟶ T) (w : Q ⟶ T) (he : e.hom ≫ w = v) (j : Y ⟶ T) :
    pullback v j ≅ pullback w j where
  hom := pullback.lift (pullback.fst v j ≫ e.hom) (pullback.snd v j) (by
    rw [Category.assoc, he, pullback.condition])
  inv := pullback.lift (pullback.fst w j ≫ e.inv) (pullback.snd w j) (by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc, pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]

@[simp, reassoc] theorem chartPullbackOverIso_hom_fst
    {P Q T Y : Scheme.{u}} (e : P ≅ Q)
    (v : P ⟶ T) (w : Q ⟶ T) (he : e.hom ≫ w = v) (j : Y ⟶ T) :
    (chartPullbackOverIso e v w he j).hom ≫ pullback.fst w j =
      pullback.fst v j ≫ e.hom := pullback.lift_fst _ _ _

@[simp, reassoc] theorem chartPullbackOverIso_hom_snd
    {P Q T Y : Scheme.{u}} (e : P ≅ Q)
    (v : P ⟶ T) (w : Q ⟶ T) (he : e.hom ≫ w = v) (j : Y ⟶ T) :
    (chartPullbackOverIso e v w he j).hom ≫ pullback.snd w j =
      pullback.snd v j := pullback.lift_snd _ _ _

variable {A R : Type u} [CommRing A] [CommRing R]
  {X X' Y : Scheme.{u}}
  (p : X ⟶ Spec (.of A)) (f : A →+* R)
  (v : X' ⟶ X) (q : X' ⟶ Spec (.of R))
  (h : IsPullback v q p (Spec.map (CommRingCat.ofHom f)))
  (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
  (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p)

/-- The actual chart coordinate; its source is not replaced by the native model. -/
def affineLineChartOfActualCartesian : pullback v j ⟶ Spec (.of (Polynomial R)) :=
  (chartPullbackOverIso h.isoPullback v (pullback.fst p (Spec.map (CommRingCat.ofHom f)))
    h.isoPullback_hom_fst j).hom ≫ affineLineChartBaseChange p f j a ha

instance affineLineChartOfActualCartesian_etale [Etale a] :
    Etale (affineLineChartOfActualCartesian p f v q h j a ha) := by
  unfold affineLineChartOfActualCartesian
  infer_instance

@[reassoc] theorem affineLineChartOfActualCartesian_map :
    affineLineChartOfActualCartesian p f v q h j a ha ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) =
      pullback.snd v j ≫ a := by
  rw [affineLineChartOfActualCartesian, Category.assoc, affineLineChartBaseChange_map,
    ← Category.assoc, chartPullbackOverIso_hom_snd]

@[reassoc] theorem affineLineChartOfActualCartesian_structure :
    affineLineChartOfActualCartesian p f v q h j a ha ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      pullback.fst v j ≫ q := by
  rw [affineLineChartOfActualCartesian, Category.assoc, affineLineChartBaseChange_structure,
    ← Category.assoc, chartPullbackOverIso_hom_fst, Category.assoc,
    h.isoPullback_hom_snd]

/-- The finite-cover/chart equation on the actual retained or independent chart pullback. -/
theorem affineLineChartOfActualCartesian_comp_XChart
    (π : X ⟶ projectiveLine A)
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A) :
    pullback.fst v j ≫ projectiveLineCoverOfActualCartesian p f v q h π hπ =
      affineLineChartOfActualCartesian p f v q h j a ha ≫ projectiveLineXChart R := by
  rw [affineLineChartOfActualCartesian, Category.assoc,
    ← affineLineChartBaseChange_comp_XChart p f π hπ j a ha hj,
    ← Category.assoc, chartPullbackOverIso_hom_fst]
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Scheme
