/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Polynomial.ZeroCoordinateEtale
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtaleChange

/-! # The actual base case of finite-coefficient-field neighborhood induction

At dimension zero an actual étale coordinate chart is already étale over the
original ground field. Its structural neighborhood pullback is therefore an
isomorphism for every presheaf on the original smooth site.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- The zero-coordinate structural pullback is an actual isomorphism, with no
rigidity or lower-dimensional induction assumption. -/
theorem isIso_structuralNeighborhoodPullback_of_zeroCoordinates
    (K E : Type u) [Field K] [Field E] [Algebra K E]
    [Module.Finite K E] [Algebra.IsSeparable K E]
    (X : SmoothSite (Spec (.of K))) [IsAffine X.left]
    (q : X.left ⟶ Spec (.of (MvPolynomial (Fin 0) E))) [Etale q]
    (hq : q ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin 0) E))) = X.hom)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left)
    (F : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso (etaleNeighborhoodValuePullback
      (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
        X ⟶ base (Spec (.of K))) (ξ := ξ) rfl F) := by
  have hzero := finiteSeparable_zeroCoordinate_structure_etale K E
    (MvPolynomial (Fin 0) E) (AlgHom.id E _) (by
      exact RingHom.Etale.of_bijective Function.bijective_id)
  let : Etale (Spec.map (CommRingCat.ofHom
    (algebraMap K (MvPolynomial (Fin 0) E)))) := hzero
  let : Etale X.hom := hq ▸ inferInstance
  let g : X ⟶ base (Spec (.of K)) :=
    homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp)
  let : Etale g.left := inferInstanceAs (Etale X.hom)
  exact (etaleNeighborhoodValueEtaleIso g (ξ := ξ) rfl F).isIso_hom

end AlgebraicGeometry.Scheme.SmoothSite
