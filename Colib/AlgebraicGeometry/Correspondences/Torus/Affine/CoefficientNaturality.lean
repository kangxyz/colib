/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.CycleRationalFunction
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Whole coefficient fibers of native affine torus supports

The coefficient map can be noninjective and nonflat. The entire quotient by the
mapped polynomial is the actual scheme-theoretic fiber of each native support.
The support is finite flat by its produced polynomial presentation. Its fiber
therefore gives a native finite correspondence with every generic stalk length,
and this correspondence is the mapped whole polynomial cycle.

This is a span base-change theorem. The comparison with native Tor composition
by a left graph is a separate missing theorem and is not assumed here.

Implementation source: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Aglib/AlgebraicGeometry/BaseChange/Affine/AdjoinRootBaseChange.lean` and
`AlgebraicGeometry/Correspondences/Torus/Affine/PolynomialBaseChange.lean`.
The quotient universal property is reused; support and cycles are native Colib.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial Stacks.Chow

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]

/-- The actual quotient specialization is Cartesian, including nonreduced fibers. -/
theorem specialization_isPullback (a : R →+* A) (p : R[X]) :
    IsPullback (projection (p.map a)) (specialization a p)
      (Spec.map (CommRingCat.ofHom a)) (projection p) := by
  have square : CommRingCat.ofHom a ≫ CommRingCat.ofHom (AdjoinRoot.of (p.map a)) =
      CommRingCat.ofHom (AdjoinRoot.of p) ≫
        CommRingCat.ofHom (AdjoinRoot.map a p (p.map a) dvd_rfl) := by
    ext r
    simp
  have hp : IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom (AdjoinRoot.of p))
      (CommRingCat.ofHom (AdjoinRoot.of (p.map a)))
      (CommRingCat.ofHom (AdjoinRoot.map a p (p.map a) dvd_rfl)) := by
    apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ square)
    apply PushoutCocone.isColimitAux'
    intro s
    have hc : s.inl.hom.comp a = s.inr.hom.comp (AdjoinRoot.of p) :=
      congrArg CommRingCat.Hom.hom s.condition
    have hr : (p.map a).eval₂ s.inl.hom (s.inr (AdjoinRoot.root p)) = 0 := by
      rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
    let d : CommRingCat.of (AdjoinRoot (p.map a)) ⟶ s.pt :=
      CommRingCat.ofHom (AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr)
    refine ⟨d, ?_, ?_, ?_⟩
    · ext r
      change AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr
        (AdjoinRoot.of (p.map a) r) = s.inl r
      simp
    · apply CommRingCat.hom_ext
      apply AdjoinRoot.ringHom_ext
      · ext r
        change AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr
          (AdjoinRoot.map a p (p.map a) dvd_rfl (AdjoinRoot.of p r)) =
            s.inr (AdjoinRoot.of p r)
        simpa using RingHom.congr_fun hc r
      · change AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr
          (AdjoinRoot.map a p (p.map a) dvd_rfl (AdjoinRoot.root p)) =
            s.inr (AdjoinRoot.root p)
        simp
    · intro m hm hn
      apply CommRingCat.hom_ext
      apply AdjoinRoot.ringHom_ext
      · ext r
        have h := congrArg (fun f => f r) hm
        change m (AdjoinRoot.of (p.map a) r) = s.inl r at h
        change m (AdjoinRoot.of (p.map a) r) =
          AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr
            (AdjoinRoot.of (p.map a) r)
        simpa using h
      · have hroot := congrArg (fun f => f (AdjoinRoot.root p)) hn
        change m (AdjoinRoot.map a p (p.map a) dvd_rfl (AdjoinRoot.root p)) =
          s.inr (AdjoinRoot.root p) at hroot
        change m (AdjoinRoot.root (p.map a)) =
          AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr
            (AdjoinRoot.root (p.map a))
        simpa using hroot
  exact isPullback_SpecMap_of_isPushout _ _ _ _ hp

/-- The actual native ambient map induced by a change of coefficients. -/
def coefficientAmbientMap (f : Spec (.of R) ⟶ S) (a : R →+* A) :
    ambient (Spec.map (CommRingCat.ofHom a) ≫ f) ⟶ ambient f :=
  pullback.map _ _ _ _ (Spec.map (CommRingCat.ofHom a))
    (𝟙 (multiplicativeGroupBaseChange S)) (𝟙 S) (by simp) (by simp)

/-- Both coordinates of the whole polynomial quotient commute with specialization. -/
@[reassoc] theorem inclusion_coefficientAmbientMap
    (f : Spec (.of R) ⟶ S) (a : R →+* A) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    inclusion (Spec.map (CommRingCat.ofHom a) ≫ f) (p.map a)
        (map_constant_isUnit a p hu) ≫ coefficientAmbientMap f a =
      specialization a p ≫ inclusion f p hu := by
  apply pullback.hom_ext
  · simp only [coefficientAmbientMap, Category.assoc, pullback.map, pullback.lift_fst,
      inclusion_fst_assoc, inclusion_fst]
    exact (specialization_projection a p).symm
  · simp only [coefficientAmbientMap, Category.assoc, pullback.map, pullback.lift_snd,
      Category.comp_id, inclusion_snd]
    exact torusPoint_specialization f a p hu

namespace PrimePoint

variable [IsDomain R] [IsIntegrallyClosed R]
variable {f : Spec (.of R) ⟶ S} (Z : PrimePoint f)

set_option backward.isDefEq.respectTransparency false in
/-- Flatness belongs to the actual finite support, not to the coefficient map. -/
instance projectionFlat : Flat Z.projection := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat) Z.polynomialSupportIso.hom,
    Z.polynomialSupportIso_projection]
  exact projection_flat Z.coordinatePolynomial Z.coordinatePolynomial_monic

/-- The whole scheme-theoretic coefficient fiber of the original native support. -/
abbrev coefficientFiber (a : R →+* A) : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom a)) Z.projection

/-- The mapped polynomial quotient, with its actual maps, is the support fiber. -/
theorem coefficientFiber_isPullback (a : R →+* A) :
    IsPullback (NativeTorusPolynomial.projection (Z.coordinatePolynomial.map a))
      (specialization a Z.coordinatePolynomial ≫ Z.polynomialSupportIso.hom)
      (Spec.map (CommRingCat.ofHom a)) Z.projection := by
  apply (specialization_isPullback a Z.coordinatePolynomial).of_iso
    (Iso.refl _) (Iso.refl _) Z.polynomialSupportIso (Iso.refl _)
  · simp
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using Z.polynomialSupportIso_projection.symm

/-- A whole-fiber isomorphism, retaining nilpotents and all repeated factors. -/
def coefficientFiberIso (a : R →+* A) :
    Spec (.of (AdjoinRoot (Z.coordinatePolynomial.map a))) ≅ Z.coefficientFiber a :=
  (Z.coefficientFiber_isPullback a).isoPullback

@[reassoc (attr := simp)] theorem coefficientFiberIso_fst (a : R →+* A) :
    (Z.coefficientFiberIso a).hom ≫ pullback.fst _ _ =
      NativeTorusPolynomial.projection (Z.coordinatePolynomial.map a) :=
  (Z.coefficientFiber_isPullback a).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem coefficientFiberIso_snd (a : R →+* A) :
    (Z.coefficientFiberIso a).hom ≫ pullback.snd _ _ =
      specialization a Z.coordinatePolynomial ≫ Z.polynomialSupportIso.hom :=
  (Z.coefficientFiber_isPullback a).isoPullback_hom_snd

/-- The original support fiber maps into the actual native source-torus product. -/
def coefficientFiberMap (a : R →+* A) :
    Z.coefficientFiber a ⟶ ambient (Spec.map (CommRingCat.ofHom a) ≫ f) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Z.inclusion ≫ pullback.snd _ _) (by
      have hZ : Z.projection ≫ f =
          (Z.inclusion ≫ pullback.snd f (multiplicativeGroupBaseChange S ↘ S)) ≫
            (multiplicativeGroupBaseChange S ↘ S) := by
        change (Z.inclusion ≫
          pullback.fst f (multiplicativeGroupBaseChange S ↘ S)) ≫ f = _
        simpa only [Category.assoc] using congrArg
          (fun q : ambient f ⟶ S => Z.inclusion ≫ q)
          (pullback.condition (f := f) (g := multiplicativeGroupBaseChange S ↘ S))
      rw [← Category.assoc, pullback.condition]
      simpa only [Category.assoc] using congrArg
        (fun q : Z.support ⟶ S =>
          pullback.snd (Spec.map (CommRingCat.ofHom a)) Z.projection ≫ q) hZ)

omit [IsDomain R] [IsIntegrallyClosed R] in
@[reassoc (attr := simp)] theorem coefficientFiberMap_fst (a : R →+* A) :
    Z.coefficientFiberMap a ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

omit [IsDomain R] [IsIntegrallyClosed R] in
@[reassoc (attr := simp)] theorem coefficientFiberMap_snd (a : R →+* A) :
    Z.coefficientFiberMap a ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Z.inclusion ≫ pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The whole-fiber isomorphism preserves the source and forward torus coordinate. -/
@[reassoc] theorem coefficientFiberIso_map (a : R →+* A) :
    (Z.coefficientFiberIso a).hom ≫ Z.coefficientFiberMap a =
      NativeTorusPolynomial.inclusion (Spec.map (CommRingCat.ofHom a) ≫ f)
        (Z.coordinatePolynomial.map a)
        (map_constant_isUnit a Z.coordinatePolynomial Z.coordinatePolynomial_constant_isUnit) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, coefficientFiberMap_fst, coefficientFiberIso_fst, inclusion_fst]
  · simp only [Category.assoc, coefficientFiberMap_snd, coefficientFiberIso_snd_assoc,
      polynomialSupportIso_inclusion_assoc, inclusion_snd]
    exact (torusPoint_specialization f a Z.coordinatePolynomial
      Z.coordinatePolynomial_constant_isUnit).symm

instance coefficientFiberMapFinite (a : R →+* A) : IsFinite (Z.coefficientFiberMap a) := by
  have : IsSeparated (multiplicativeGroupBaseChange S ↘ S) := by
    change IsSeparated (pullback.snd
      (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S))
    infer_instance
  have : IsFinite (Z.coefficientFiberMap a ≫ pullback.fst _ _) := by
    rw [coefficientFiberMap_fst]
    infer_instance
  exact IsFinite.of_comp _ (pullback.fst _ _)

variable [IsNoetherianRing A]

instance coefficientFiberNoetherian (a : R →+* A) : IsNoetherian (Z.coefficientFiber a) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)
  toCompactSpace := inferInstance

/-- The actual whole fiber fundamental cycle pushed into the native ambient.
This definition is not asserted to be graph precomposition. -/
def coefficientFiberCycle (a : R →+* A) :
    finiteCorrespondences (Spec.map (CommRingCat.ofHom a) ≫ f)
      (multiplicativeGroupBaseChange S ↘ S) := by
  letI : IsSeparated (multiplicativeGroupBaseChange S ↘ S) := by
    change IsSeparated (pullback.snd
      (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S))
    infer_instance
  letI : LocallyOfFiniteType (multiplicativeGroupBaseChange S ↘ S) := by
    change LocallyOfFiniteType (pullback.snd
      (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S))
    infer_instance
  letI : IsFinite (Z.coefficientFiberMap a ≫ pullback.fst _ _) := by
    rw [coefficientFiberMap_fst]
    infer_instance
  letI : Flat (Z.coefficientFiberMap a ≫ pullback.fst _ _) := by
    rw [coefficientFiberMap_fst]
    infer_instance
  exact finiteFlatSpanFundamental _ _ (Z.coefficientFiberMap a)

/-- The producer retains the original fiber's actual generic stalk lengths. -/
theorem coefficientFiberCycle_val (a : R →+* A) :
    (Z.coefficientFiberCycle a).val =
      finiteCyclePushforward (Z.coefficientFiberMap a)
        (AlgebraicCycle.fundamentalCycle (Z.coefficientFiber a)) := rfl

/-- The actual fiber fundamental cycle is the entire mapped polynomial cycle. -/
theorem coefficientFiberCycle_eq_polynomialCycle (a : R →+* A) :
    Z.coefficientFiberCycle a =
      polynomialCycle (Spec.map (CommRingCat.ofHom a) ≫ f)
        (Z.coordinatePolynomial.map a) (Z.coordinatePolynomial_monic.map a)
        (map_constant_isUnit a Z.coordinatePolynomial Z.coordinatePolynomial_constant_isUnit) := by
  have := inclusion_isClosedImmersion (Spec.map (CommRingCat.ofHom a) ≫ f)
    (Z.coordinatePolynomial.map a)
    (map_constant_isUnit a Z.coordinatePolynomial Z.coordinatePolynomial_constant_isUnit)
  apply Subtype.ext
  rw [coefficientFiberCycle_val, polynomialCycle_val]
  simpa only [finiteCyclePushforward_fundamentalCycle_iso, coefficientFiberIso_map] using
    (finiteCyclePushforward_comp_apply (Z.coefficientFiberIso a).hom
      (Z.coefficientFiberMap a)
      (AlgebraicCycle.fundamentalCycle
        (Spec (.of (AdjoinRoot (Z.coordinatePolynomial.map a))))))

end PrimePoint

end AlgebraicGeometry.NativeTorusPolynomial
