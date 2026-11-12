/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualCartesianAffineChart

/-! # The original chart on the literal pullback to an actual clopen model -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme
variable {A R : Type u} [CommRing A] [CommRing R]
  {X X' U Y : Scheme.{u}}
  (p : X ⟶ Spec (.of A)) (f : A →+* R)
  (v : X' ⟶ X) (q : X' ⟶ Spec (.of R))
  (h : IsPullback v q p (Spec.map (CommRingCat.ofHom f)))
  (k : U ⟶ X') (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
  (ha : a ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = j ≫ p)

/-- The source is the actual direct pullback, not an unidentified nested chart. -/
def affineChartOfActualClopen : pullback (k ≫ v) j ⟶ Spec (.of (Polynomial R)) :=
  (pullbackRightPullbackFstIso v j k).inv ≫
    pullback.snd k (pullback.fst v j) ≫ affineLineChartOfActualCartesian p f v q h j a ha

instance affineChartOfActualClopen_etale [IsOpenImmersion k] [Etale a] :
    Etale (affineChartOfActualClopen p f v q h k j a ha) := by
  unfold affineChartOfActualClopen
  infer_instance

@[reassoc] theorem affineChartOfActualClopen_structure :
    affineChartOfActualClopen p f v q h k j a ha ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      pullback.fst (k ≫ v) j ≫ (k ≫ q) := by
  simp only [affineChartOfActualClopen, Category.assoc,
    affineLineChartOfActualCartesian_structure, pullbackRightPullbackFstIso_inv_snd_fst_assoc]

@[reassoc] theorem affineChartOfActualClopen_map :
    affineChartOfActualClopen p f v q h k j a ha ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) =
      pullback.snd (k ≫ v) j ≫ a := by
  simp only [affineChartOfActualClopen, Category.assoc,
    affineLineChartOfActualCartesian_map, pullbackRightPullbackFstIso_inv_snd_snd_assoc]

theorem affineChartOfActualClopen_cover
    (π : X ⟶ projectiveLine A)
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A) :
    pullback.fst (k ≫ v) j ≫ (k ≫ projectiveLineCoverOfActualCartesian p f v q h π hπ) =
      affineChartOfActualClopen p f v q h k j a ha ≫ projectiveLineXChart R := by
  simp only [affineChartOfActualClopen, Category.assoc]
  rw [← affineLineChartOfActualCartesian_comp_XChart p f v q h j a ha π hπ hj]
  simp only [pullbackRightPullbackFstIso_inv_snd_fst_assoc]

end AlgebraicGeometry.Scheme
