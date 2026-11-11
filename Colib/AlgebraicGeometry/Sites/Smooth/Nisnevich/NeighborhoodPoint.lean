/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Neighborhood
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered

/-!
# Points from affine Nisnevich neighborhoods

At a smooth scheme and one of its points, pull the covering sieve back to an
affine étale neighborhood. The residue-field isomorphism at the marked point
lifts its field-valued map. An affine refinement supplies the neighborhood
used by the native cofiltered-diagram point constructor.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  (X : SmoothSite S) (x : X.left)

/-- A covering sieve lifts every map from a pointed neighborhood after refinement. -/
theorem nisnevichNeighborhoodCoverLift
    ⦃Y : SmoothSite S⦄ (R : Sieve Y) (hR : R ∈ nisnevichTopology S Y)
    ⦃A : NisnevichNeighborhood X x⦄ (a : (nisnevichNeighborhoodToSmooth X x).obj A ⟶ Y) :
    ∃ (Z : SmoothSite S) (g : Z ⟶ Y) (_ : R g) (B : NisnevichNeighborhood X x)
      (q : B ⟶ A) (b : (nisnevichNeighborhoodToSmooth X x).obj B ⟶ Z),
      b ≫ g = (nisnevichNeighborhoodToSmooth X x).map q ≫ a := by
  let F := nisnevichNeighborhoodToSmooth X x
  let p := nisnevichNeighborhoodHom X x A
  let m := nisnevichNeighborhoodMark X x A
  obtain ⟨Q, hQ, hQle⟩ :=
    mem_nisnevichTopology_iff.mp ((nisnevichTopology S).pullback_stable a hR)
  obtain ⟨ι, Z, k, rfl⟩ := Q.exists_eq_ofArrows
  have hQ' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (k i).left) ∈
      Nisnevich.precoverage (F.obj A).left := by
    have h := mem_nisnevichPrecoverage_iff.mp hQ
    rw [Presieve.map_ofArrows] at h
    exact h
  obtain ⟨_, _, ⟨i⟩, t, ht⟩ := Nisnevich.exists_lift_of_mem_precoverage hQ' _ m
  let : Etale (k i).left := etale_of_mem_nisnevichPrecoverage hQ ⟨i⟩
  have ht' : t ≫ ((k i).left ≫ p.left) = X.left.fromSpecResidueField x := by
    rw [← Category.assoc, ht]
    exact nisnevichNeighborhoodMark_hom X x A
  let : Etale p.left := inferInstanceAs (Etale ((nisnevichNeighborhoodHom X x A).left))
  obtain ⟨B, j, hj, hmark⟩ :=
    exists_nisnevichNeighborhood_refinement X x ((k i).left ≫ p.left) t ht'
  have hw : (j ≫ (k i).left) ≫ (nisnevichNeighborhoodHom X x A).left =
      (nisnevichNeighborhoodHom X x B).left := by
    simpa only [p, Category.assoc] using hj
  have hm : nisnevichNeighborhoodMark X x B ≫ (j ≫ (k i).left) =
      nisnevichNeighborhoodMark X x A := by
    rw [← Category.assoc, hmark, ht]
  let q := nisnevichNeighborhoodHomMk X x (j ≫ (k i).left) hw hm
  let b : F.obj B ⟶ Z i := homMk j (by
    calc
      j ≫ (Z i).hom = j ≫ (k i).left ≫ p.left ≫ X.hom := by
        rw [← MorphismProperty.Over.w (k i), ← MorphismProperty.Over.w p]
      _ = (j ≫ ((k i).left ≫ p.left)) ≫ X.hom := by simp only [Category.assoc]
      _ = _ := by rw [hj, MorphismProperty.Over.w])
  refine ⟨Z i, k i ≫ a, hQle (Z i) (k i) ⟨i⟩, B, q, b, ?_⟩
  have hb : b ≫ k i = F.map q :=
    MorphismProperty.Over.Hom.ext (nisnevichNeighborhoodHomMk_map_left X x _ _ _).symm
  rw [← Category.assoc, hb]

/-- The native Nisnevich point associated to the affine étale neighborhoods of
the canonical residue point of a smooth scheme. -/
def nisnevichNeighborhoodPoint : (nisnevichTopology S).Point.{max u w} :=
  let := nisnevichNeighborhoodInitiallySmall.{u,w} X x
  GrothendieckTopology.Point.ofIsCofiltered.{max u w}
    (nisnevichNeighborhoodToSmooth X x) (nisnevichNeighborhoodCoverLift X x)

end AlgebraicGeometry.Scheme.SmoothSite
