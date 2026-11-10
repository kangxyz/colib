/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialClosedImmersion

/-!
# A coordinate chart of the existing native torus ambient

The codomain remains the actual source-first pullback of the Stacks torus.
The auxiliary affine chart is compared by explicit inverse maps, preserving
the source projection and forward coordinate. It is never substituted for
the target of the correspondence group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial Opposite

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]

/-- A Laurent ring map is determined by coefficients and the positive coordinate. -/
theorem laurentRingHom_ext {a b : LaurentPolynomial R →+* A}
    (hC : ∀ r, a (LaurentPolynomial.C r) = b (LaurentPolynomial.C r))
    (hX : a (LaurentPolynomial.T 1) = b (LaurentPolynomial.T 1)) : a = b := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : R[X]))
  apply Polynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      toLaurent_C] using hC r
  · simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      toLaurent_X] using hX

/-- The forward coordinate unit of the auxiliary affine chart. -/
def chartUnit : (LaurentPolynomial R)ˣ := (LaurentPolynomial.isUnit_T 1).unit

@[simp] theorem chartUnit_val : (chartUnit (R := R)).val = LaurentPolynomial.T 1 :=
  IsUnit.unit_spec _

/-- The chart's actual projection to the affine source. -/
def chartProjection : Spec (.of (LaurentPolynomial R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- The explicit coordinate chart map to the original native torus ambient. -/
def chartMap (f : Spec (.of R) ⟶ S) : Spec (.of (LaurentPolynomial R)) ⟶ ambient f :=
  pullback.lift chartProjection (nativeAffineTorusPoint (chartProjection ≫ f) chartUnit).left
    (nativeTorusPoint_over _ _).symm

@[reassoc (attr := simp)] theorem chartMap_fst (f : Spec (.of R) ⟶ S) :
    chartMap f ≫ pullback.fst _ _ = chartProjection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem chartMap_snd (f : Spec (.of R) ⟶ S) :
    chartMap f ≫ pullback.snd _ _ =
      (nativeAffineTorusPoint (chartProjection ≫ f) chartUnit).left :=
  pullback.lift_snd _ _ _

/-- The reverse chart homomorphism uses the actual ambient coefficients and unit. -/
def chartRingHom (f : Spec (.of R) ⟶ S) : LaurentPolynomial R →+* Γ(ambient f, ⊤) :=
  LaurentPolynomial.eval₂ (ambientCoefficient f) (ambientCoordinate f)

@[simp] theorem chartRingHom_C (f : Spec (.of R) ⟶ S) (r : R) :
    chartRingHom f (LaurentPolynomial.C r) = ambientCoefficient f r := by
  simp [chartRingHom]

@[simp] theorem chartRingHom_T (f : Spec (.of R) ⟶ S) :
    chartRingHom f (LaurentPolynomial.T 1) = (ambientCoordinate f).val := by
  simp [chartRingHom]

/-- The actual inverse morphism defined by the global-section adjunction. -/
def chartInverse (f : Spec (.of R) ⟶ S) : ambient f ⟶ Spec (.of (LaurentPolynomial R)) :=
  (ΓSpec.adjunction.homEquiv (ambient f) (op (.of (LaurentPolynomial R))))
    (CommRingCat.ofHom (chartRingHom f)).op

theorem chartInverse_appTop (f : Spec (.of R) ⟶ S) :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv ≫ (chartInverse f).appTop =
      CommRingCat.ofHom (chartRingHom f) :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

theorem chartMap_appTop_coefficient (f : Spec (.of R) ⟶ S) (r : R) :
    (chartMap f).appTop (ambientCoefficient f r) =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.C r) := by
  have hi := congrArg (fun k => k.appTop) (chartMap_fst f)
  rw [Scheme.Hom.comp_appTop] at hi
  change ((pullback.fst f (multiplicativeGroupBaseChange S ↘ S)).appTop ≫ (chartMap f).appTop)
      ((Scheme.ΓSpecIso (.of R)).inv r) = _
  rw [hi]
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom LaurentPolynomial.C)) r).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem chartMap_appTop_coordinate (f : Spec (.of R) ⟶ S) :
    (chartMap f).appTop (ambientCoordinate f).val =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.T 1) := by
  have hi := congrArg (fun k => k.appTop) (chartMap_snd f)
  rw [Scheme.Hom.comp_appTop] at hi
  change ((pullback.snd f (multiplicativeGroupBaseChange S ↘ S)).appTop ≫ (chartMap f).appTop)
      (multiplicativeGroupBaseChangeCoordinate S).val = _
  rw [hi]
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom).1
  rw [CommRingCat.hom_inv_apply]
  have h := congrArg Units.val
    (nativeAffineTorusPoint_coordinate (chartProjection ≫ f) (chartUnit (R := R)))
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
      ((nativeAffineTorusPoint (chartProjection ≫ f) (chartUnit (R := R))).left.appTop
        (multiplicativeGroupBaseChangeCoordinate S).val) = (chartUnit (R := R)).val at h
  exact h.trans chartUnit_val

theorem chartMap_appTop_chartRingHom (f : Spec (.of R) ⟶ S) :
    (chartMap f).appTop.hom.comp (chartRingHom f) =
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom := by
  apply laurentRingHom_ext
  · intro r
    simpa only [RingHom.comp_apply, chartRingHom_C] using chartMap_appTop_coefficient f r
  · simpa only [RingHom.comp_apply, chartRingHom_T] using chartMap_appTop_coordinate f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Recover an arbitrary native torus point from its actual forward coordinate. -/
theorem nativeTorusPoint_recover {T : Scheme.{u}} (a : T ⟶ S)
    (t : Over.mk a ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S) :
    nativeTorusPoint a (Units.map t.left.appTop.hom.toMonoidHom
      (multiplicativeGroupBaseChangeCoordinate S)) = t := by
  let e := (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv
    (X := Over.mk a)
  obtain ⟨v, hv⟩ := e.symm.surjective t
  have ht : nativeTorusPoint a v = t := hv
  rw [← ht, nativeTorusPoint_coordinate]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] theorem chartInverse_projection (f : Spec (.of R) ⟶ S) :
    chartInverse f ≫ chartProjection = pullback.fst _ _ := by
  apply ext_to_Spec
  simp only [Scheme.Γ_obj, Scheme.Γ_map_op]
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, chartProjection,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, chartInverse_appTop]
  apply CommRingCat.hom_ext
  ext r
  exact chartRingHom_C f r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem chartInverse_unit (f : Spec (.of R) ⟶ S) :
    Units.map (chartInverse f).appTop.hom.toMonoidHom
      (specGlobalUnit (chartUnit (R := R))) =
      ambientCoordinate f := by
  apply Units.ext
  change (chartInverse f).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (chartUnit (R := R)).val) =
    (ambientCoordinate f).val
  rw [chartUnit_val]
  calc
    _ = (CommRingCat.ofHom (chartRingHom f)) (LaurentPolynomial.T 1) :=
      (CommRingCat.comp_apply (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv
        (chartInverse f).appTop (LaurentPolynomial.T 1)).symm.trans
          (ConcreteCategory.congr_hom (chartInverse_appTop f) (LaurentPolynomial.T 1))
    _ = (ambientCoordinate f).val := chartRingHom_T f

@[reassoc] theorem chartInverse_torusPoint (f : Spec (.of R) ⟶ S) :
    chartInverse f ≫ (nativeAffineTorusPoint (chartProjection ≫ f) chartUnit).left =
      pullback.snd _ _ := by
  rw [nativeAffineTorusPoint, ← nativeTorusPoint_comp_left, chartInverse_unit,
    ← Category.assoc, chartInverse_projection]
  let t : Over.mk (pullback.fst f (multiplicativeGroupBaseChange S ↘ S) ≫ f) ⟶
      Scheme.asOver (multiplicativeGroupBaseChange S) S :=
    Over.homMk (pullback.snd _ _) (pullback.condition.symm)
  exact congrArg (fun k => k.left) (nativeTorusPoint_recover _ t)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Both explicit maps are inverse, with the original source projection retained. -/
def nativeChartIso (f : Spec (.of R) ⟶ S) :
    Spec (.of (LaurentPolynomial R)) ≅ ambient f where
  hom := chartMap f
  inv := chartInverse f
  hom_inv_id := by
    apply ext_to_Spec
    simp only [Scheme.Γ_obj, Scheme.Γ_map_op]
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, chartInverse_appTop,
      Scheme.Hom.id_appTop, Category.comp_id]
    apply CommRingCat.hom_ext
    exact chartMap_appTop_chartRingHom f
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, chartMap_fst, chartInverse_projection, Category.id_comp]
    · simp only [Category.assoc, chartMap_snd, Category.id_comp]
      exact chartInverse_torusPoint f

end AlgebraicGeometry.NativeTorusPolynomial
