/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ContractionHI

/-!
# Actual contraction preserves coefficient homotopy invariance

Factor exchange identifies the precise affine projections. The inverse descends
from polynomial evaluation through the actual surjective quotient. The final
polynomial-projection corollary reconnects the original coefficient predicate.
Adapted from `Motivic/Transfers/Presheaf/ContractionInvariance.lean:68-120`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction

variable {k : Type u} [Field k]

/-- Coefficient HI passes to every actual geometrically integral smooth parameter. -/
theorem withParameter_isA1Invariant (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] : IsA1Invariant (withParameter P T) := by
  intro X
  change IsIso (transfer P ((Cor.parameterProduct T).map
    ((Cor.graphFunctor k).map
      (SmoothSite.productFst X (SmoothSite.additiveGroupObject (Spec (.of k)))))))
  rw [Cor.parameterProduct_graph]
  let e := P.obj.mapIso ((Cor.graphFunctor k).mapIso
    (productSwapRight X (SmoothSite.additiveGroupObject (Spec (.of k))) T)).op
  have h : A1.projectionPullback (.of k) ((toPresheaf k).obj P)
      (SmoothSite.product X T) ≫ e.hom =
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productMap
          (SmoothSite.productFst X (SmoothSite.additiveGroupObject (Spec (.of k))))
          (𝟙 T))) := by
    change transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productFst (SmoothSite.product X T)
          (SmoothSite.additiveGroupObject (Spec (.of k))))) ≫
      transfer P ((Cor.graphFunctor k).map (productSwapRight X _ T).hom) = _
    rw [← transfer_comp, ← Functor.map_comp, productSwapRight_hom_fst]
  let := hP (SmoothSite.product X T)
  rw [← h]
  infer_instance

/-- The genuine Laurent quotient preserves ordinary coefficient HI. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/ContractionInvariance.lean:92-120"
  "adaptation" "Actual signed-transfer quotient and actual affine projection, no sheaf premise"]
theorem contraction_isA1Invariant (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) : IsA1Invariant (contraction P) := by
  intro X
  let R := CommRingCat.of k
  let Q := (toPresheaf k).obj (contraction P)
  let L := (toPresheaf k).obj (torusSections P)
  let η := (toPresheaf k).map (toContraction P)
  let p := A1.projectionPullback R Q X
  let s := A1.sectionPullback R Q X 0
  have hp : p ≫ s = 𝟙 _ := A1.projectionPullback_sectionPullback R Q X 0
  have hs : s ≫ p = 𝟙 _ := by
    have hep : Epi (η.app (op (affineLineCylinder.obj X))) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (toContraction_surjective P (Cor.mk (affineLineCylinder.obj X)))
    apply (cancel_epi (η.app (op (affineLineCylinder.obj X)))).mp
    have hn := η.naturality (nativeAffineSection R X 0).op
    have hm := η.naturality ((projection (SmoothSite.additiveGroupObject (Spec R))).app X).op
    change A1.sectionPullback R L X 0 ≫ η.app (op X) =
      η.app (op (affineLineCylinder.obj X)) ≫ s at hn
    change A1.projectionPullback R L X ≫ η.app (op (affineLineCylinder.obj X)) =
      η.app (op X) ≫ p at hm
    rw [← Category.assoc, ← hn, Category.assoc, ← hm, ← Category.assoc]
    have hL := withParameter_isA1Invariant P hP
      (SmoothSite.multiplicativeGroupObject (Spec R))
    rw [A1.sectionPullback_projectionPullback R L hL X 0,
      Category.id_comp, Category.comp_id]
  exact ⟨⟨s, hp, hs⟩⟩

/-- The result holds for the exact original polynomial coefficient projection. -/
theorem contraction_polynomial_projection_isIso (P : PresheafWithTransfers.{v} k)
    (hP : ∀ X : SmoothSite (Spec (.of k)),
      IsIso (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productFst X (polynomialAffineLine (.of k))))))
    (X : SmoothSite (Spec (.of k))) :
    IsIso (transfer (contraction P) ((Cor.graphFunctor k).map
      (SmoothSite.productFst X (polynomialAffineLine (.of k))))) :=
  (isA1Invariant_iff_polynomial_projection (contraction P)).mp
    (contraction_isA1Invariant P ((isA1Invariant_iff_polynomial_projection P).mpr hP)) X

end AlgebraicGeometry.PresheafWithTransfers
