/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualClopenAffineChart

/-! # Original coordinates on the unchanged retained source -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme
variable {A R : Type u} [CommRing A] [CommRing R]
  {X X' U Y V : Scheme.{u}}
  (p : X ⟶ Spec (.of A)) (f : A →+* R)
  (v : X' ⟶ X) (q : X' ⟶ Spec (.of R))
  (h : IsPullback v q p (Spec.map (CommRingCat.ofHom f)))
  (k : U ⟶ X') (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
  (ha : a ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = j ≫ p)
  (jV : V ⟶ U) (vY : V ⟶ Y) (hV : IsPullback jV vY (k ≫ v) j)

/-- Coordinates on the specified retained source, not a replacement chart. -/
def affineChartOfActualRetained : V ⟶ Spec (.of (Polynomial R)) :=
  hV.isoPullback.hom ≫ affineChartOfActualClopen p f v q h k j a ha

instance affineChartOfActualRetained_etale [IsOpenImmersion k] [Etale a] :
    Etale (affineChartOfActualRetained p f v q h k j a ha jV vY hV) := by
  unfold affineChartOfActualRetained
  infer_instance

@[reassoc] theorem affineChartOfActualRetained_structure :
    affineChartOfActualRetained p f v q h k j a ha jV vY hV ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      jV ≫ (k ≫ q) := by
  rw [affineChartOfActualRetained, Category.assoc,
    affineChartOfActualClopen_structure, ← Category.assoc, hV.isoPullback_hom_fst]

@[reassoc] theorem affineChartOfActualRetained_map :
    affineChartOfActualRetained p f v q h k j a ha jV vY hV ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) = vY ≫ a := by
  rw [affineChartOfActualRetained, Category.assoc,
    affineChartOfActualClopen_map, ← Category.assoc, hV.isoPullback_hom_snd]

theorem affineChartOfActualRetained_cover
    (π : X ⟶ projectiveLine A)
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A) :
    jV ≫ (k ≫ projectiveLineCoverOfActualCartesian p f v q h π hπ) =
      affineChartOfActualRetained p f v q h k j a ha jV vY hV ≫ projectiveLineXChart R := by
  rw [affineChartOfActualRetained, Category.assoc,
    ← affineChartOfActualClopen_cover p f v q h k j a ha π hπ hj]
  exact (congrArg (fun z => z ≫
    (k ≫ projectiveLineCoverOfActualCartesian p f v q h π hπ))
      hV.isoPullback_hom_fst).symm.trans (Category.assoc _ _ _)

end AlgebraicGeometry.Scheme
