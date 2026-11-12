/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.AffineLine.Open.AffineLineOpenMonicShrinking
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.PolynomialMoving
public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.LaurentCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Colib.RingTheory.Smooth.Localization

/-!
# Laurent local vanishing after shrinking the base

A monic boundary gives an injective restriction of an A¹-invariant
coefficient on the whole puncture. A generic open zero therefore vanishes
on the whole torus above one principal open of the original base.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Laurent/` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`, files
`RestrictionInjective.lean`, `GenericOpenZero.lean` and `NeighborhoodZero.lean`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe v u

namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

open _root_.AlgebraicGeometry.Scheme
open _root_.Algebra.Smooth

variable {k R S : Type u} [Field k] [CommRing R] [IsDomain R] [CommRing S]
  [Algebra k R] [Algebra.Smooth k R] [Algebra k S] [Algebra.Smooth k S]

attribute [local instance] laurent_smooth away_smooth

/-- Relative Laurent restriction is injective after the genuine monic/coprime presentation.
The coefficient presheaf is still an arbitrary HI presheaf with transfers over k. -/
theorem laurent_principal_restriction_injective
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (g : R[X]) (hg : g.Monic) (hXg : IsCoprime Polynomial.X g) :
    Function.Injective (P.transfer ((Cor.graphFunctor k).map
      (narrowInclusion (k := k) Polynomial.X g))) := by
  let : IsNoetherianRing (LaurentPolynomial R) :=
    Algebra.FiniteType.isNoetherianRing k (LaurentPolynomial R)
  have hu : IsUnit (((Polynomial.X : R[X]).map (algebraMap R (LaurentPolynomial R))).eval
      (LaurentPolynomial.T 1)) := by
    simpa using (LaurentPolynomial.isUnit_T (R := R) 1)
  obtain ⟨β, hβ⟩ := exists_moving_action (k := k) Polynomial.X g monic_X hg hXg
    (LaurentPolynomial.T 1) hu (laurentSiteIso (k := k) (R := R)).hom
    (laurentSiteIso_coordinate (k := k) (R := R))
  have he : Function.Injective
      (P.transfer ((Cor.graphFunctor k).map (laurentSiteIso (k := k) (R :=
          R)).hom)) :=
    (ConcreteCategory.bijective_of_isIso _).injective
  intro x y hxy
  apply he
  exact (ConcreteCategory.congr_hom (hβ P hP) x).trans
    ((congrArg (fun z => (P.transfer β) z) hxy).trans
      (ConcreteCategory.congr_hom (hβ P hP) y).symm)

omit [IsDomain R] in
/-- The two actual restrictions into the original puncture agree. -/
theorem punctured_open_square (φ : R →ₐ[k] S) (W : (Spec (.of R[X])).Opens)
    (hWX : W ≤ principalOpen Polynomial.X) (g : S[X])
    (hWg : principalOpen (Polynomial.X * g) ≤ (lineMap φ).left ⁻¹ᵁ W) :
    narrowInclusion (k := k) Polynomial.X g ≫ puncturedBaseMap φ =
      openMapOfLE φ W (principalOpen (Polynomial.X * g)) hWg ≫
        originalInclusion (k := k) (principalOpen Polynomial.X) W hWX := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (principalOpen (Polynomial.X : R[X])).ι).mp
  have h1 : (narrowInclusion (k := k) Polynomial.X g).left ≫
      (principalOpen (Polynomial.X : S[X])).ι =
      (principalOpen (Polynomial.X * g)).ι :=
    Scheme.homOfLE_ι _ (PrimeSpectrum.basicOpen_mul_le_left Polynomial.X g)
  have h2 : (puncturedBaseMap φ).left ≫ (principalOpen (Polynomial.X : R[X])).ι =
      (principalOpen (Polynomial.X : S[X])).ι ≫ (lineMap φ).left :=
    openMapOfLE_inclusion _ _ _ _
  have h3 : (originalInclusion (k := k) (principalOpen Polynomial.X) W hWX).left ≫
      (principalOpen (Polynomial.X : R[X])).ι = W.ι := Scheme.homOfLE_ι _ hWX
  have h4 := openMapOfLE_inclusion φ W (principalOpen (Polynomial.X * g)) hWg
  change ((_ ≫ _) ≫ _) = ((_ ≫ _) ≫ _)
  rw [Category.assoc, h2, ← Category.assoc, h1, Category.assoc, h3, h4]

/-- A section vanishing on an original nonempty open of the relative torus vanishes
on the entire torus after one actual principal shrinking of the smooth integral base. -/
theorem exists_base_shrink_restriction_eq_zero
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (W : (Spec (.of R[X])).Opens)
    (hW : (W : Set (Spec (.of R[X]))).Nonempty) (hWX : W ≤ principalOpen Polynomial.X)
    (s : P.sections (Cor.mk (openSite (k := k) (Polynomial.X : R[X]))))
    (hs : P.transfer ((Cor.graphFunctor k).map
      (originalInclusion (k := k) (principalOpen Polynomial.X) W hWX)) s = 0) :
    ∃ r : R, r ≠ 0 ∧ P.transfer ((Cor.graphFunctor k).map
      (puncturedBaseMap (IsScalarTower.toAlgHom k R (Localization.Away r)))) s = 0 := by
  obtain ⟨r, hr, g, hg, _, hXg, hWg⟩ :=
    AffineLineOpenMonicShrinking.exists_coprime_monic_punctured_open R W hW
  let R' := Localization.Away r
  let : IsDomain R' := Localization.Away.isDomain hr
  let φ : R →ₐ[k] R' := IsScalarTower.toAlgHom k R R'
  let b := puncturedBaseMap φ
  let i := originalInclusion (k := k) (principalOpen Polynomial.X) W hWX
  let u := narrowInclusion (k := k) Polynomial.X g
  let v := openMapOfLE φ W (principalOpen (Polynomial.X * g)) hWg
  have hcomm : u ≫ b = v ≫ i := punctured_open_square φ W hWX g hWg
  refine ⟨r, hr, ?_⟩
  apply laurent_principal_restriction_injective P hP g hg hXg
  have hz : P.transfer ((Cor.graphFunctor k).map u)
      (P.transfer ((Cor.graphFunctor k).map b) s) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← PresheafWithTransfers.transfer_comp,
      ← Functor.map_comp, hcomm, Functor.map_comp,
          PresheafWithTransfers.transfer_comp,
      ConcreteCategory.comp_apply]
    change P.transfer ((Cor.graphFunctor k).map v)
      (P.transfer ((Cor.graphFunctor k).map i) s) = 0
    rw [hs]
    exact map_zero (P.transfer ((Cor.graphFunctor k).map v)).hom
  exact hz.trans (map_zero (P.transfer ((Cor.graphFunctor k).map u)).hom).symm

/-- A zero on an original open neighborhood gives a zero torus section after
principal base localization. -/
theorem exists_base_shrink_of_neighborhood_zero
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (W : (openSite (k := k) (Polynomial.X : R[X])).left.Opens)
    (hW : (W : Set (openSite (k := k) (Polynomial.X : R[X])).left).Nonempty)
    (s : P.sections (Cor.mk (openSite (k := k) (Polynomial.X : R[X]))))
    (hs : P.transfer ((Cor.graphFunctor k).map
      (_root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion
        (openSite (k := k) (Polynomial.X : R[X])) W)) s = 0) :
    ∃ r : R, r ≠ 0 ∧ P.transfer ((Cor.graphFunctor k).map
      (puncturedBaseMap (IsScalarTower.toAlgHom k R (Localization.Away r)))) s = 0 := by
  let j := W.ι ≫ (principalOpen (Polynomial.X : R[X])).ι
  let V := j.opensRange
  have hV : (V : Set (Spec (.of R[X]))).Nonempty := by
    obtain ⟨x, hx⟩ := hW
    exact ⟨j ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
  have hVX : V ≤ principalOpen Polynomial.X := by
    rintro x ⟨y, rfl⟩
    exact (W.ι y).property
  let t : V.toScheme ⟶ W.toScheme := IsOpenImmersion.lift j V.ι (by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl)
  have ht : t ≫ j = V.ι := IsOpenImmersion.lift_fac _ _ _
  have htX : t ≫ W.ι = (Spec (.of R[X])).homOfLE hVX := by
    apply (cancel_mono (principalOpen (Polynomial.X : R[X])).ι).mp
    rw [Category.assoc, ht, Scheme.homOfLE_ι]
  let b : originalOpenSite (k := k) V ⟶
      (SmoothSite.opensFunctor (openSite (k := k) (Polynomial.X : R[X]))).obj W :=
    SmoothSite.homMk t (by
      change t ≫ (W.ι ≫ ((principalOpen (Polynomial.X : R[X])).ι ≫ _)) = V.ι ≫ _
      rw [← Category.assoc, htX, ← Category.assoc, Scheme.homOfLE_ι])
  have hb : b ≫ _root_.AlgebraicGeometry.Scheme.SmoothSite.openInclusion
      (openSite (k := k) (Polynomial.X : R[X])) W =
      originalInclusion (k := k) (principalOpen Polynomial.X) V hVX := by
    apply MorphismProperty.Over.Hom.ext
    exact htX
  apply exists_base_shrink_restriction_eq_zero P hP V hV hVX s
  rw [← hb, Functor.map_comp, PresheafWithTransfers.transfer_comp,
      ConcreteCategory.comp_apply, hs]
  exact map_zero (P.transfer ((Cor.graphFunctor k).map b)).hom

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
