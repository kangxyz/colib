/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Neighborhood
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Topology
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Étale points from separably closed field-valued neighborhoods

A separably closed field-valued marking lifts through étale covering families.
Affine refinement then supplies the lift required by the native cofiltered
point constructor on the original smooth étale site. Adapted from the smooth
Nisnevich neighborhood point construction, using Mathlib's separably closed
étale lifting theorem instead of residue-field splitting.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  (X : SmoothSite S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ X.left)

/-- A covering sieve lifts every map from a pointed neighborhood after refinement. -/
theorem etaleNeighborhoodCoverLift
    ⦃Y : SmoothSite S⦄ (R : Sieve Y) (hR : R ∈ etaleTopology S Y)
    ⦃A : EtaleNeighborhood X ξ⦄ (a : (etaleNeighborhoodToSmooth X ξ).obj A ⟶ Y) :
    ∃ (Z : SmoothSite S) (g : Z ⟶ Y) (_ : R g) (B : EtaleNeighborhood X ξ)
      (q : B ⟶ A) (b : (etaleNeighborhoodToSmooth X ξ).obj B ⟶ Z),
      b ≫ g = (etaleNeighborhoodToSmooth X ξ).map q ≫ a := by
  let F := etaleNeighborhoodToSmooth X ξ
  let p := etaleNeighborhoodHom X ξ A
  let m := etaleNeighborhoodMark X ξ A
  obtain ⟨Q, hQ, hQle⟩ :=
    mem_etaleTopology_iff.mp ((etaleTopology S).pullback_stable a hR)
  obtain ⟨ι, Z, k, rfl⟩ := Q.exists_eq_ofArrows
  obtain ⟨hk, hsurj⟩ := (ofArrows_mem_etalePrecoverage_iff k).mp hQ
  obtain ⟨i, z, hz⟩ := hsurj (m default)
  let : Etale (k i).left := hk i
  obtain ⟨t, ht, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (k i).left m z hz
  have ht' : t ≫ ((k i).left ≫ p.left) = ξ := by
    rw [← Category.assoc, ht]
    exact etaleNeighborhoodMark_hom X ξ A
  let : Etale p.left := inferInstanceAs (Etale ((etaleNeighborhoodHom X ξ A).left))
  obtain ⟨B, j, hj, hmark⟩ :=
    exists_etaleNeighborhood_refinement X ξ ((k i).left ≫ p.left) t ht'
  have hw : (j ≫ (k i).left) ≫ (etaleNeighborhoodHom X ξ A).left =
      (etaleNeighborhoodHom X ξ B).left := by
    simpa only [p, Category.assoc] using hj
  have hm : etaleNeighborhoodMark X ξ B ≫ (j ≫ (k i).left) =
      etaleNeighborhoodMark X ξ A := by
    rw [← Category.assoc, hmark, ht]
  let q := etaleNeighborhoodHomMk X ξ (j ≫ (k i).left) hw hm
  let b : F.obj B ⟶ Z i := homMk j (by
    calc
      j ≫ (Z i).hom = j ≫ (k i).left ≫ p.left ≫ X.hom := by
        rw [← MorphismProperty.Over.w (k i), ← MorphismProperty.Over.w p]
      _ = (j ≫ ((k i).left ≫ p.left)) ≫ X.hom := by simp only [Category.assoc]
      _ = _ := by rw [hj, MorphismProperty.Over.w])
  refine ⟨Z i, k i ≫ a, hQle (Z i) (k i) ⟨i⟩, B, q, b, ?_⟩
  have hb : b ≫ k i = F.map q :=
    MorphismProperty.Over.Hom.ext (etaleNeighborhoodHomMk_map_left X ξ _ _ _).symm
  rw [← Category.assoc, hb]

/-- The native étale point associated to a separably closed field-valued marking. -/
@[colib_tag "COL-1057", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/CategoryTheory/Sites/Point/OfIsCofiltered.lean:135-145"
  "ingredient" "Native point constructor; the original smooth-etale neighborhood lifting \
    condition is proved here."]
def etaleNeighborhoodPoint : (etaleTopology S).Point.{max u w} :=
  let := etaleNeighborhoodInitiallySmall.{u,w} X ξ
  GrothendieckTopology.Point.ofIsCofiltered.{max u w}
    (etaleNeighborhoodToSmooth X ξ) (etaleNeighborhoodCoverLift X ξ)

end AlgebraicGeometry.Scheme.SmoothSite
