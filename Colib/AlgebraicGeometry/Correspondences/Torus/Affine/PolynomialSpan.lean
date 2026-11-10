/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.UnitPoints
public import Colib.AlgebraicGeometry.GroupScheme.Smooth
public import Colib.RingTheory.AdjoinRoot.UnitNorm
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Actual polynomial-quotient spans into the native torus

The left map is `Spec (R[X]/(p)) → Spec R`. The right map represents the
literal forward root unit in that quotient, in the existing Stacks torus
over the original base. A monic polynomial makes the left map finite flat
and the map into the correspondence ambient scheme finite.

These are geometric maps, not a formal cycle presentation. A fundamental
cycle with its genuine generic stalk lengths must still be assigned before
this span can be called the polynomial finite correspondence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]

/-- The actual structural morphism of the polynomial quotient. -/
def projection (p : R[X]) : Spec (.of (AdjoinRoot p)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.of p))

/-- A monic equation gives a finite structural map, with no reducedness premise. -/
theorem projection_isFinite (p : R[X]) (hp : p.Monic) : IsFinite (projection p) := by
  let := hp.finite_adjoinRoot
  apply (IsFinite.SpecMap_iff _).mpr
  change (AdjoinRoot.of p).Finite
  rw [← AdjoinRoot.algebraMap_eq, RingHom.finite_algebraMap]
  infer_instance

/-- The same structural map is flat, using its actual finite free power basis. -/
theorem projection_flat (p : R[X]) (hp : p.Monic) : Flat (projection p) := by
  let := hp.free_adjoinRoot
  apply Flat.SpecMap_iff.mpr
  change (AdjoinRoot.of p).Flat
  rw [← AdjoinRoot.algebraMap_eq, RingHom.flat_algebraMap_iff]
  infer_instance

/-- The actual quotient-coordinate point of the native torus over the original base. -/
def torusPoint (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    Over.mk (projection p ≫ f) ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S :=
  nativeAffineTorusPoint (projection p ≫ f) (AdjoinRoot.rootUnit p hu)

/-- The torus-valued leg is over the same original base map. -/
@[reassoc] theorem torusPoint_over
    (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (torusPoint f p hu).left ≫ (multiplicativeGroupBaseChange S ↘ S) = projection p ≫ f :=
  Over.w _

/-- Pull the native forward coordinate back along the actual torus-valued leg. -/
def coordinateUnit (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (AdjoinRoot p)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of (AdjoinRoot p))).hom.hom.toMonoidHom
    (Units.map (torusPoint f p hu).left.appTop.hom.toMonoidHom
      (multiplicativeGroupBaseChangeCoordinate S))

/-- The coordinate of the geometric span is the original root, not its inverse. -/
@[simp] theorem coordinateUnit_eq_rootUnit
    (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    coordinateUnit f p hu = AdjoinRoot.rootUnit p hu :=
  nativeAffineTorusPoint_coordinate _ _

/-- Its value is the literal class of `X` in `R[X]/(p)`. -/
theorem coordinateUnit_val
    (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (coordinateUnit f p hu : AdjoinRoot p) = AdjoinRoot.root p := by
  rw [coordinateUnit_eq_rootUnit, AdjoinRoot.rootUnit_val]

/-- The genuine map to the native source-first correspondence ambient scheme. -/
def inclusion (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    Spec (.of (AdjoinRoot p)) ⟶ pullback f (multiplicativeGroupBaseChange S ↘ S) :=
  pullback.lift (projection p) (torusPoint f p hu).left (torusPoint_over f p hu).symm

@[reassoc (attr := simp)] theorem inclusion_fst
    (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    inclusion f p hu ≫ pullback.fst _ _ = projection p := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem inclusion_snd
    (f : Spec (.of R) ⟶ S) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    inclusion f p hu ≫ pullback.snd _ _ = (torusPoint f p hu).left := by
  exact pullback.lift_snd _ _ _

/-- The actual map to the native correspondence ambient scheme is finite. -/
theorem inclusion_isFinite (f : Spec (.of R) ⟶ S) (p : R[X])
    (hp : p.Monic) (hu : IsUnit (p.coeff 0)) : IsFinite (inclusion f p hu) := by
  have : IsFinite (inclusion f p hu ≫ pullback.fst _ _) := by
    rw [inclusion_fst]
    exact projection_isFinite p hp
  have : IsSeparated (multiplicativeGroupBaseChange S ↘ S) := by
    change IsSeparated (pullback.snd
      (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S))
    infer_instance
  exact IsFinite.of_comp _ (pullback.fst _ _)

/-- The quotient map induced by any specialization of coefficients. -/
def specialization (a : R →+* A) (p : R[X]) :
    Spec (.of (AdjoinRoot (p.map a))) ⟶ Spec (.of (AdjoinRoot p)) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.map a p (p.map a) (dvd_refl _)))

/-- The original source map is retained by the actual quotient specialization. -/
@[reassoc] theorem specialization_projection (a : R →+* A) (p : R[X]) :
    specialization a p ≫ projection p = projection (p.map a) ≫ Spec.map (CommRingCat.ofHom a) := by
  unfold specialization projection
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact AdjoinRoot.map_of a p (p.map a) (dvd_refl _) r

/-- The mapped constant coefficient remains a unit, even for noninjective maps. -/
theorem map_constant_isUnit (a : R →+* A) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    IsUnit ((p.map a).coeff 0) := by
  simpa only [coeff_map] using hu.map a

/-- Specializing coefficients sends the actual forward root unit to the actual root unit. -/
theorem specialization_rootUnit (a : R →+* A) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    Units.map (AdjoinRoot.map a p (p.map a) (dvd_refl _)).toMonoidHom
      (AdjoinRoot.rootUnit p hu) =
      AdjoinRoot.rootUnit (p.map a) (map_constant_isUnit a p hu) := by
  apply Units.ext
  simp only [Units.coe_map, AdjoinRoot.rootUnit_val]
  exact AdjoinRoot.map_root a p (p.map a) (dvd_refl _)

/-- The actual torus-valued leg commutes with arbitrary coefficient specialization. -/
theorem torusPoint_specialization (f : Spec (.of R) ⟶ S)
    (a : R →+* A) (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (torusPoint (Spec.map (CommRingCat.ofHom a) ≫ f) (p.map a)
      (map_constant_isUnit a p hu)).left = specialization a p ≫ (torusPoint f p hu).left := by
  have h := nativeAffineTorusPoint_natural (projection p ≫ f)
    (AdjoinRoot.map a p (p.map a) (dvd_refl _)) (AdjoinRoot.rootUnit p hu)
  rw [specialization_rootUnit] at h
  change (nativeAffineTorusPoint (specialization a p ≫ (projection p ≫ f)) _).left =
    specialization a p ≫ (torusPoint f p hu).left at h
  rw [← Category.assoc, specialization_projection, Category.assoc] at h
  exact h

end AlgebraicGeometry.NativeTorusPolynomial
