/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.AffineLine.Open.AffineLineZeroNeighborhoodBaseShrink
public import Colib.AlgebraicGeometry.Correspondences.Graph.AffineLineEndpointCoefficient
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.SimplexFaceCoordinates
public import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Ambient
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.NativeSections
public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.Basic

/-!
# Original simplex cofaces as Cartesian polynomial endpoints

The polynomial chart identifies the actual coface with evaluation at zero.
Its transverse parameter is flat. The same endpoint square remains
Cartesian after taking the product with an arbitrary smooth source.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme SmoothSite PolynomialSectionPencil
open AlgebraicGeometry.PolynomialOpenQuotient
open scoped Simplicial

universe u

namespace AlgebraicSimplex

variable (k : Type u) [Field k] {n : ℕ} (i : Fin (n + 2))

private def facePolynomialSpecIso :
    Spec (.of (CoordinateRing k (n + 1))) ≅ Spec (.of (Polynomial (CoordinateRing k n))) :=
  Scheme.Spec.mapIso (facePolynomialEquiv k i).symm.toRingEquiv.toCommRingCatIso.op

private theorem coface_facePolynomialSpecIso :
    ((cosimplicialSmoothSite k).δ i).left ≫ (facePolynomialSpecIso k i).hom =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : CoordinateRing k n))) := by
  have hf : AlgebraicSimplex.pullback k (SimplexCategory.δ i).toOrderHom = face k i :=
    (face_eq_pullback k i).symm
  have hd : ((cosimplicialSmoothSite k).δ i).left = Spec.map (CommRingCat.ofHom (face k i)) := by
    unfold CosimplicialObject.δ
    rw [cosimplicialSmoothSite_map_left, hf]
  have he : (facePolynomialSpecIso k i).hom =
      Spec.map (CommRingCat.ofHom (facePolynomialEquiv k i).symm.toRingHom) := rfl
  have hr : CommRingCat.ofHom (facePolynomialEquiv k i).symm.toRingHom ≫
      CommRingCat.ofHom (face k i) =
        CommRingCat.ofHom (R := Polynomial (CoordinateRing k n)) (S := CoordinateRing k n)
          (Polynomial.evalRingHom (0 : CoordinateRing k n)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change face k i ((facePolynomialEquiv k i).symm r) = Polynomial.evalRingHom 0 r
    rw [face_eq_eval_zero_comp_facePolynomialEquiv]
    change Polynomial.evalRingHom 0
      (facePolynomialEquiv k i ((facePolynomialEquiv k i).symm r)) = _
    rw [AlgEquiv.apply_symm_apply]
  rw [hd, he, ← Spec.map_comp, hr]

private theorem polynomialZero_comp_projection {A : Type u} [CommRing A] :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))) ≫
      PolynomialLaurent.polynomialProjection (.of A) = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)) = 𝟙 (CommRingCat.of A) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact Polynomial.eval_C
  rw [h, Spec.map_id]

/-- Each original coface is the zero endpoint of a flat polynomial parameter. -/
theorem coface_cartesian_polynomial :
    ∃ q : (smoothSiteObj k (n + 1)).left ⟶ Spec (.of (Polynomial k)),
      Flat q ∧ IsPullback ((cosimplicialSmoothSite k).δ i).left
        (smoothSiteObj k n).hom q (AffineLineFiber.point (0 : k)) := by
  let b := structureMap k n
  let p := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
  let E : Spec (.of (Polynomial (CoordinateRing k n))) ≅ parameterSpace b :=
    ambientIso (constant k n)
  let e := facePolynomialSpecIso k i ≪≫ E
  let q := e.hom ≫ pullback.snd b p
  have he : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : CoordinateRing k n))) ≫
      E.hom = endpoint b 0 := by
    apply pullback.hom_ext
    · have hE : E.hom ≫ projection b = PolynomialLaurent.polynomialProjection
          (.of (CoordinateRing k n)) := ambientIso_fst (constant k n)
      change (_ ≫ E.hom) ≫ projection b = endpoint b 0 ≫ projection b
      rw [Category.assoc, hE, endpoint_projection]
      exact polynomialZero_comp_projection (A := CoordinateRing k n)
    · have hE : E.hom ≫ pullback.snd b p =
          Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (constant k n))) :=
        ambientIso_snd (constant k n)
      have hs : endpoint b 0 ≫ pullback.snd b p =
          b ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) :=
        endpoint_snd b 0
      rw [Category.assoc, hE, hs]
      exact polynomial_zero_scalar_naturality (constant k n)
  have hcoface : ((cosimplicialSmoothSite k).δ i).left ≫ e.hom = endpoint b 0 := by
    simp only [e, Iso.trans_hom, ← Category.assoc, coface_facePolynomialSpecIso, he]
  let : Flat b := inferInstanceAs (Flat (structureMap k n))
  have hq : Flat q := inferInstanceAs (Flat (e.hom ≫ pullback.snd b p))
  refine ⟨q, hq, ?_⟩
  apply (endpoint_affineLine_isPullback b (0 : k)).of_iso'
    (Iso.refl _) e (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.id_comp] using hcoface.symm
  · exact (Category.id_comp b).trans (Category.comp_id b).symm
  · exact (Category.comp_id q).symm
  · simp

/-- The original coface on a product with a smooth source is a Cartesian polynomial face. -/
theorem product_coface_cartesian_polynomial (U : SmoothSite (Spec (CommRingCat.of k))) :
    ∃ q : (product U (smoothSiteObj k (n + 1))).left ⟶ Spec (.of (Polynomial k)),
      Flat q ∧ IsPullback
        (SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite k).δ i)).left
        (product U (smoothSiteObj k n)).hom q (AffineLineFiber.point (0 : k)) := by
  obtain ⟨q, hq, H⟩ := coface_cartesian_polynomial k i
  let : Flat q := hq
  let P := smoothSiteObj k n
  let T := smoothSiteObj k (n + 1)
  let f : P ⟶ T := (cosimplicialSmoothSite k).δ i
  let p := (productSnd U T).left ≫ q
  have hp : Flat p := inferInstanceAs (Flat (pullback.snd U.hom T.hom ≫ q))
  refine ⟨p, hp, ?_⟩
  change IsPullback (SmoothSite.productMap (𝟙 U) f).left
    (pullback.fst U.hom P.hom ≫ U.hom) p (AffineLineFiber.point (0 : k))
  rw [pullback.condition]
  exact (productMap_right_isPullback U f).paste_vert H

end AlgebraicSimplex
