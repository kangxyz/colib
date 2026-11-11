/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AlgebraicSimplex.Units
public import Colib.AlgebraicGeometry.Simplex.AffineRelativeComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.Presheaf

/-!
# Global units on the actual affine relative-simplex projection

The genuine polynomial-units theorem is carried through ΓSpec, the existing
coefficient pullback square and the canonical affine chart. The resulting
isomorphism is the pullback on units by the original scheme projection.
Adapted from AffineSimplexUnitComplex and AffineSchemeUnitProjection at
motivic revision a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite

universe u

namespace AlgebraicSimplex

variable {k R : Type u} [CommRing k] [CommRing R] [_root_.IsReduced R]

/-- The ordinary additive unit functor sends the actual constant map to an isomorphism. -/
instance isIso_ringUnits_constant (n : ℕ) :
    IsIso (ringUnitsFunctor.map (CommRingCat.ofHom (constant R n))) := by
  let e : Additive Rˣ ≃+ Additive (CoordinateRing R n)ˣ :=
    AddEquiv.ofBijective (Units.map (constant R n).toMonoidHom).toAdditive
      (units_constant_bijective R n)
  change IsIso
    (AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of (Additive Rˣ))
      (Y := AddCommGrpCat.of (Additive (CoordinateRing R n)ˣ)) e).hom
  infer_instance

omit [_root_.IsReduced R] in
/-- ΓSpec identifies the genuine structure projection with the constant ring map. -/
theorem structureMap_appTop (n : ℕ) :
    (structureMap R n).appTop =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom (constant R n) ≫
        (Scheme.ΓSpecIso (.of (CoordinateRing R n))).inv := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (constant R n))
  simpa only [structureMap, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun f => f ≫ (Scheme.ΓSpecIso (.of (CoordinateRing R n))).inv) h

instance isIso_units_structureMap (n : ℕ) :
    IsIso (ringUnitsFunctor.map (structureMap R n).appTop) := by
  rw [structureMap_appTop, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- The actual coefficient pullback retains the same isomorphism on global units. -/
instance isIso_units_affineRelativeProjection (c : k →+* R) (n : ℕ) :
    IsIso (ringUnitsFunctor.map
      (pullback.snd (structureMap k n) (Spec.map (CommRingCat.ofHom c))).appTop) := by
  rw [← (mapCoefficients_isPullback c n).isoPullback_inv_snd,
    Scheme.Hom.comp_appTop, Functor.map_comp]
  infer_instance

/-- No chosen affine presentation is required: the map is the actual projection. -/
theorem isIso_units_affineSchemeProjection {X : Scheme.{u}}
    [IsAffine X] [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of k)) (n : ℕ) :
    IsIso (ringUnitsFunctor.map (pullback.snd (structureMap k n) f).appTop) := by
  let c : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  let e := pullback.map (structureMap k n) (Spec.map (CommRingCat.ofHom c))
    (structureMap k n) f (𝟙 _) X.isoSpec.inv (𝟙 _)
      (by simp) (by simpa [c] using (isoSpec_inv_map f).symm)
  have he : IsIso e := by dsimp [e]; infer_instance
  have h : e ≫ pullback.snd (structureMap k n) f =
      pullback.snd (structureMap k n) (Spec.map (CommRingCat.ofHom c)) ≫ X.isoSpec.inv :=
    pullback.lift_snd _ _ _
  have hmap := congrArg (fun g => ringUnitsFunctor.map g.appTop) h
  simp only [Scheme.Hom.comp_appTop, Functor.map_comp] at hmap
  have : IsIso (ringUnitsFunctor.map (pullback.snd (structureMap k n) f).appTop ≫
      ringUnitsFunctor.map e.appTop) := by
    rw [hmap]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (ringUnitsFunctor.map e.appTop)

end AlgebraicSimplex
