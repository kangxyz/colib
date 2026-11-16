/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorsionSubpresheaf
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodMono

/-! # Reduction from sectionwise torsion to fixed-exponent rigidity

No common annihilator is required. Each original presheaf section lies in a
fixed-exponent transfer subpresheaf. Original neighborhood representatives and
refinements pass the fixed-exponent rigidity theorem to the whole presheaf.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable {k : Type u} [Field k]
local instance : IsAffine (SmoothSite.base (Spec (.of k))).left :=
  inferInstanceAs (IsAffine (Spec (.of k)))

/-- Every section has a positive annihilator invertible in the ground field;
the annihilator may depend on both the object and the section. -/
def IsPrimeToCharacteristicTorsion (P : PresheafWithTransfers.{u + 1} k) : Prop :=
  ∀ (V : SmoothSite (Spec (.of k))) (x : sections P ((Cor.graphFunctor k).obj V)),
    ∃ m : ℕ, 0 < m ∧ IsUnit (m : k) ∧ m • x = 0

/-- Any original germ comes from one actual finite-exponent subpresheaf. -/
theorem exists_torsionSubpresheaf_neighborhood_lift
    (P : PresheafWithTransfers.{u + 1} k) (hP : IsPrimeToCharacteristicTorsion P)
    (X : SmoothSite (Spec (.of k))) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X.left)
    (z : etaleNeighborhoodValue X ξ ((toPresheaf.{u + 1} k).obj P)) :
    ∃ (n : ℕ) (_ : IsUnit ((n + 1 : ℕ) : k))
      (y : etaleNeighborhoodValue X ξ
        ((toPresheaf.{u + 1} k).obj (torsionSubpresheaf.{u, u + 1} P (n + 1)))),
      (etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map
        ((toPresheaf.{u + 1} k).map (torsionInclusion.{u, u + 1} P (n + 1))) y = z := by
  obtain ⟨A, x, rfl⟩ := exists_etaleNeighborhood_representative X ξ ((toPresheaf.{u + 1} k).obj P) z
  obtain ⟨m, hm, hn, hx⟩ := hP ((etaleNeighborhoodToSmooth X ξ).obj A) x
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let Q := (toPresheaf.{u + 1} k).obj (torsionSubpresheaf.{u, u + 1} P (n + 1))
  let y : Q.obj (op ((etaleNeighborhoodToSmooth X ξ).obj A)) := ⟨x, hx⟩
  refine ⟨n, hn, toEtaleNeighborhoodValue X ξ A Q y, ?_⟩
  exact congrArg (fun f => f y) (toEtaleNeighborhoodValue_naturality X ξ
    ((toPresheaf.{u + 1} k).map (torsionInclusion.{u, u + 1} P (n + 1))) A)

/-- The actual torsion inclusion is injective on every original neighborhood value. -/
theorem torsionInclusion_neighborhood_injective
    (P : PresheafWithTransfers.{u + 1} k) (n : ℕ)
    (X : SmoothSite (Spec (.of k))) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X.left) :
    Function.Injective ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map
      ((toPresheaf.{u + 1} k).map (torsionInclusion.{u, u + 1} P n))) :=
  etaleNeighborhoodValue_map_injective X ξ _ (fun _ => Subtype.val_injective)

/-- Structural germs are rigid without a uniform annihilator. -/
theorem isIso_structuralPullback_of_torsionSubpresheaf_pullbacks
    (P : PresheafWithTransfers.{u + 1} k)
    (hT : IsPrimeToCharacteristicTorsion P)
    (hB : ∀ (n : ℕ), IsUnit ((n + 1 : ℕ) : k) →
      ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
        (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left),
        IsIso (etaleNeighborhoodValuePullback
          (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) :
            X ⟶ SmoothSite.base (Spec (.of k))) (ξ := ξ) rfl
          ((toPresheaf.{u + 1} k).obj (torsionSubpresheaf.{u, u + 1} P (n + 1)))))
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left) :
    IsIso (etaleNeighborhoodValuePullback
      (homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp) : X ⟶ SmoothSite.base (Spec (.of k)))
      (ξ := ξ) rfl ((toPresheaf.{u + 1} k).obj P)) := by
  let f : X ⟶ SmoothSite.base (Spec (.of k)) := homMk X.hom (by
    change X.hom ≫ 𝟙 _ = X.hom; simp)
  let η : Spec (.of Ω) ⟶ (SmoothSite.base (Spec (.of k))).left := ξ ≫ f.left
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨n, hn, y, hy⟩ := exists_torsionSubpresheaf_neighborhood_lift P hT
      (SmoothSite.base (Spec (.of k))) η z
    let a := (toPresheaf.{u + 1} k).map (torsionInclusion.{u, u + 1} P (n + 1))
    let Q := (toPresheaf.{u + 1} k).obj (torsionSubpresheaf.{u, u + 1} P (n + 1))
    have hi := hB n hn X Ω ξ
    have he := congrArg (fun g => g y) (etaleNeighborhoodValuePullback_naturality f rfl a)
    have hzero : etaleNeighborhoodValuePullback f rfl Q y = 0 := by
      apply torsionInclusion_neighborhood_injective P (n + 1) X ξ
      rw [map_zero]
      change etaleNeighborhoodValuePullback f rfl ((toPresheaf.{u + 1} k).obj P)
        ((etaleNeighborhoodPoint.{u, u + 1}
          (SmoothSite.base (Spec (.of k))) η).presheafFiber.map a y) = _ at he
      exact he.symm.trans ((congrArg
        (etaleNeighborhoodValuePullback f rfl ((toPresheaf.{u + 1} k).obj P)) hy).trans hz)
    have hyzero := (ConcreteCategory.bijective_of_isIso
      (etaleNeighborhoodValuePullback f rfl Q)).1
      (hzero.trans (map_zero _).symm)
    rw [← hy, hyzero]
    exact map_zero _
  · intro z
    obtain ⟨n, hn, y, hy⟩ := exists_torsionSubpresheaf_neighborhood_lift P hT X ξ z
    let a := (toPresheaf.{u + 1} k).map (torsionInclusion.{u, u + 1} P (n + 1))
    let Q := (toPresheaf.{u + 1} k).obj (torsionSubpresheaf.{u, u + 1} P (n + 1))
    have hi := hB n hn X Ω ξ
    obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso
      (etaleNeighborhoodValuePullback f rfl Q)).2 y
    refine ⟨(etaleNeighborhoodPoint.{u, u + 1}
      (SmoothSite.base (Spec (.of k))) η).presheafFiber.map a w, ?_⟩
    have he := congrArg (fun g => g w) (etaleNeighborhoodValuePullback_naturality f rfl a)
    exact he.trans ((congrArg
      ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map a) hw).trans hy)

end AlgebraicGeometry.PresheafWithTransfers
