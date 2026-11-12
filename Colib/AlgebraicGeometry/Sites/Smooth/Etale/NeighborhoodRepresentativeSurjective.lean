/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtalePreimage

/-! # Assemble actual neighborhood representative preimages

This is the colimit assembly step only. Its representative-wise premise must be
proved geometrically before using it to close a dimension induction.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {X T : SmoothSite S} [IsAffine X.left] [IsAffine T.left]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {ξ : Spec (.of Ω) ⟶ X.left} {ζ : Spec (.of Ω) ⟶ T.left}

/-- Pulling an actual representative to its own marked neighborhood is its
object evaluation, not a newly chosen representative. -/
theorem toEtaleNeighborhoodValue_pullback_own
    (A : EtaleNeighborhood X ξ)
    (Q : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    toEtaleNeighborhoodValue X ξ A Q ≫
      etaleNeighborhoodValuePullback (etaleNeighborhoodHom X ξ A)
        (etaleNeighborhoodMark_hom X ξ A) Q =
      toEtaleNeighborhoodValueFromObject ((etaleNeighborhoodToSmooth X ξ).obj A)
        (etaleNeighborhoodMark X ξ A) Q := by
  let U := (etaleNeighborhoodToSmooth X ξ).obj A
  let η := etaleNeighborhoodMark X ξ A
  let C := etaleNeighborhoodSelf U η
  rw [toEtaleNeighborhoodValue_pullback_of_compatible
    (A := C) (g := etaleNeighborhoodHom U η C)
    (hg := by rfl) (hm := etaleNeighborhoodMark_hom U η C)]
  rfl

/-- Producing preimages for every actual affine neighborhood representative is
enough for surjectivity on the original marked neighborhood value. -/
theorem etaleNeighborhoodValuePullback_surjective_of_representatives
    (g : X ⟶ T) (hg : ξ ≫ g.left = ζ)
    (Q : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hrep : ∀ (A : EtaleNeighborhood X ξ)
      (b : Q.obj (op ((etaleNeighborhoodToSmooth X ξ).obj A))),
      ∃ z : etaleNeighborhoodValue T ζ Q,
        etaleNeighborhoodValuePullback (etaleNeighborhoodHom X ξ A ≫ g)
          (by change etaleNeighborhoodMark X ξ A ≫
                ((etaleNeighborhoodHom X ξ A).left ≫ g.left) = ζ
              rw [← Category.assoc, etaleNeighborhoodMark_hom, hg]) Q z =
        toEtaleNeighborhoodValueFromObject ((etaleNeighborhoodToSmooth X ξ).obj A)
          (etaleNeighborhoodMark X ξ A) Q b) :
    Function.Surjective (etaleNeighborhoodValuePullback g hg Q) := by
  intro y
  obtain ⟨A, b, rfl⟩ := exists_etaleNeighborhood_representative X ξ Q y
  obtain ⟨z, hz⟩ := hrep A b
  refine ⟨z, ?_⟩
  rw [etaleNeighborhoodValuePullback_comp _ g (etaleNeighborhoodMark_hom X ξ A) hg Q] at hz
  have heval := ConcreteCategory.congr_hom (toEtaleNeighborhoodValue_pullback_own A Q) b
  have heq := hz.trans heval.symm
  have h := congrArg (fun w =>
    (etaleNeighborhoodValueEtaleIso (etaleNeighborhoodHom X ξ A)
      (etaleNeighborhoodMark_hom X ξ A) Q).inv w) heq
  have hcancel := ConcreteCategory.congr_hom
    (etaleNeighborhoodValueEtaleIso (etaleNeighborhoodHom X ξ A)
      (etaleNeighborhoodMark_hom X ξ A) Q).hom_inv_id
  exact (hcancel _).symm.trans (h.trans (hcancel _))
end AlgebraicGeometry.Scheme.SmoothSite
