/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
public import Colib.AlgebraicGeometry.Simplex.Contraction

/-!
# Restriction along the actual simplex projection

The native affine-line homotopy makes the pullback along the original
simplex projection invertible for any A¹-invariant presheaf. Its inverse
is restriction along the vertex-zero section.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u v w

namespace AlgebraicGeometry.A1

variable (R : Type u) [CommRing R] {A : Type v} [Category.{w} A]

/-- The original simplex projection induces an isomorphism for invariant coefficients. -/
def simplexProjectionPullbackIso (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
    (hP : IsInvariant (.of R) P) (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    P.obj (op U) ≅ P.obj (op (product U (AlgebraicSimplex.smoothSiteObj R n))) := by
  let D := AlgebraicSimplex.smoothSiteObj R n
  let Z := product U D
  let p : Z ⟶ U := productFst U D
  let s : U ⟶ Z := AlgebraicSimplex.simplexZeroSection R n U
  let H : affineLineCylinder.obj Z ⟶ Z := AlgebraicSimplex.relativeSimplexContraction R n U
  have hs : s ≫ p = 𝟙 U := AlgebraicSimplex.simplexZeroSection_projection R n U
  have h₀ : nativeAffineSection (.of R) Z 0 ≫ H = p ≫ s :=
    AlgebraicSimplex.nativeAffineSection_comp_relativeSimplexContraction_zero R n U
  have h₁ : nativeAffineSection (.of R) Z 1 ≫ H = 𝟙 Z :=
    AlgebraicSimplex.nativeAffineSection_comp_relativeSimplexContraction_one R n U
  have hsections : sectionPullback (.of R) P Z 0 = sectionPullback (.of R) P Z 1 := by
    let : IsIso (projectionPullback (.of R) P Z) := hP Z
    apply (cancel_epi (projectionPullback (.of R) P Z)).mp
    simp only [projectionPullback_sectionPullback]
  have hmap (a : R) :
      P.map (nativeAffineSection (.of R) Z a ≫ H).op =
        P.map H.op ≫ sectionPullback (.of R) P Z a := by
    rw [sectionPullback, op_comp, P.map_comp]
  have hfix : P.map (p ≫ s).op = 𝟙 (P.obj (op Z)) := calc
    _ = P.map (nativeAffineSection (.of R) Z 0 ≫ H).op :=
      congrArg (fun f : Z ⟶ Z => P.map f.op) h₀.symm
    _ = P.map H.op ≫ sectionPullback (.of R) P Z 0 := hmap 0
    _ = P.map H.op ≫ sectionPullback (.of R) P Z 1 :=
      congrArg (P.map H.op ≫ ·) hsections
    _ = P.map (nativeAffineSection (.of R) Z 1 ≫ H).op := (hmap 1).symm
    _ = P.map (𝟙 Z).op := congrArg (fun f : Z ⟶ Z => P.map f.op) h₁
    _ = _ := by rw [op_id, P.map_id]
  exact
    { hom := P.map p.op
      inv := P.map s.op
      hom_inv_id := by rw [← P.map_comp, ← op_comp, hs, op_id, P.map_id]
      inv_hom_id := by rw [← P.map_comp, ← op_comp]; exact hfix }

/-- The forward isomorphism is pullback along the actual simplex projection. -/
theorem simplexProjectionPullbackIso_hom (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
    (hP : IsInvariant (.of R) P) (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (simplexProjectionPullbackIso R P hP U n).hom =
      P.map (productFst U (AlgebraicSimplex.smoothSiteObj R n)).op :=
  rfl

/-- Invariant coefficients invert the original simplex projection. -/
theorem isIso_simplexProjectionPullback (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)
    (hP : IsInvariant (.of R) P) (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    IsIso (P.map (productFst U (AlgebraicSimplex.smoothSiteObj R n)).op) :=
  inferInstanceAs (IsIso (simplexProjectionPullbackIso R P hP U n).hom)

end AlgebraicGeometry.A1

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The graph of the actual simplex projection acts invertibly on invariant transfers. -/
theorem isIso_transfer_simplexProjection (P : PresheafWithTransfers.{v} k)
    (hP : P.IsA1Invariant) (U : SmoothSite (Spec (.of k))) (n : ℕ) :
    IsIso (transfer P ((Cor.graphFunctor k).map
      (productFst U (AlgebraicSimplex.smoothSiteObj k n)))) :=
  A1.isIso_simplexProjectionPullback k ((toPresheaf k).obj P) hP U n

end AlgebraicGeometry.PresheafWithTransfers
