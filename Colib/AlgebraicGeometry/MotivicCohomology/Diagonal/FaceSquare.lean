/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointFiber
public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatFiber
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FiniteCyclePushforward
public import Colib.RingTheory.AlgebraicSimplex.Polynomial
public import Mathlib.Algebra.MvPolynomial.Equiv

import Mathlib.Tactic.FinCases

/-!
# The coefficient-change squares of the diagonal endpoint faces

The literal degree-zero cofaces commute with the native scalar maps of the
source and the simplex-times-torus ambient. The source square identifies the
full endpoint of an upstairs support with the polynomial endpoint of its
composite to the downstairs affine-line chart. The comparison retains the
projection to the original support and the scalar projection to the point.

Adapted from Motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/WeightTwo/CorestrictionBoundary.lean:38-142`,
`Motivic/Cohomology/WeightOne/BoundaryNorm.lean:56-186`, and
`Motivic/Cohomology/SuslinVoevodsky/ScalarExtensionSimplexEndpoint.lean:172-235`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open scoped Polynomial Simplicial

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalFiniteCyclePushforward

open _root_.AlgebraicGeometry.Scheme

/-- The original degree-zero coface of the base-times-simplex source. -/
def sourceFace (F : Type u) [Field F] (i : Fin 2) : source F 0 ⟶ source F 1 :=
  SmoothSite.productMap (𝟙 (SmoothSite.base (Spec (.of F))))
    ((AlgebraicSimplex.cosimplicialSmoothSite F).δ (n := 0) i)

/-- The second projection from the actual source to its simplex factor. -/
abbrev sourceSimplexProjection (F : Type u) [Field F] (r : ℕ) :
    (source F r).left ⟶ (AlgebraicSimplex.smoothSiteObj F r).left :=
  pullback.snd (SmoothSite.base (Spec (.of F))).hom (AlgebraicSimplex.structureMap F r)

instance sourceSimplexProjection_isIso (F : Type u) [Field F] (r : ℕ) :
    IsIso (sourceSimplexProjection F r) := by
  change IsIso (pullback.snd (𝟙 (Spec (.of F))) (AlgebraicSimplex.structureMap F r))
  infer_instance

/-- The coface leaves the base factor fixed. -/
@[reassoc] theorem sourceFace_fst (F : Type u) [Field F] (i : Fin 2) :
    (sourceFace F i).left ≫
      pullback.fst (SmoothSite.base (Spec (.of F))).hom (AlgebraicSimplex.structureMap F 1) =
    pullback.fst (SmoothSite.base (Spec (.of F))).hom (AlgebraicSimplex.structureMap F 0) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The second projection of the product coface is the original simplex coface. -/
@[reassoc] theorem sourceFace_snd (F : Type u) [Field F] (i : Fin 2) :
    (sourceFace F i).left ≫ sourceSimplexProjection F 1 =
      sourceSimplexProjection F 0 ≫
        ((AlgebraicSimplex.cosimplicialSmoothSite F).δ (n := 0) i).left :=
  pullback.lift_snd _ _ _

section ScalarChange

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

private theorem sourceMap_fst (r : ℕ) :
    sourceMap (k := k) (E := E) r ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (AlgebraicSimplex.structureMap k r) =
    pullback.fst (SmoothSite.base (Spec (.of E))).hom (AlgebraicSimplex.structureMap E r) ≫
      scalarMap :=
  pullback.lift_fst _ _ _

/-- Scalar change commutes with both original product cofaces. -/
theorem sourceMap_face (i : Fin 2) :
    (sourceFace E i).left ≫ sourceMap (k := k) (E := E) 1 =
      sourceMap (k := k) (E := E) 0 ≫ (sourceFace k i).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    change (sourceFace E i).left ≫ sourceMap (k := k) (E := E) 1 ≫
        pullback.fst (SmoothSite.base (Spec (.of k))).hom (AlgebraicSimplex.structureMap k 1) =
      sourceMap (k := k) (E := E) 0 ≫ (sourceFace k i).left ≫
        pullback.fst (SmoothSite.base (Spec (.of k))).hom (AlgebraicSimplex.structureMap k 1)
    rw [sourceMap_fst (k := k) (E := E) 1, sourceFace_fst_assoc E i, sourceFace_fst k i,
      sourceMap_fst (k := k) (E := E) 0]
  · have hn : ((AlgebraicSimplex.cosimplicialSmoothSite E).δ (n := 0) i).left ≫
        Spec.map (CommRingCat.ofHom (AlgebraicSimplex.mapCoefficients (algebraMap k E) 1)) =
      Spec.map (CommRingCat.ofHom (AlgebraicSimplex.mapCoefficients (algebraMap k E) 0)) ≫
        ((AlgebraicSimplex.cosimplicialSmoothSite k).δ (n := 0) i).left := by
      change (AlgebraicSimplex.cosimplicialScheme E).map (SimplexCategory.δ (n := 0) i) ≫
          (AlgebraicSimplex.cosimplicialSchemeMap (algebraMap k E)).app ⦋1⦌ =
        (AlgebraicSimplex.cosimplicialSchemeMap (algebraMap k E)).app ⦋0⦌ ≫
          (AlgebraicSimplex.cosimplicialScheme k).map (SimplexCategory.δ (n := 0) i)
      exact (AlgebraicSimplex.cosimplicialSchemeMap (algebraMap k E)).naturality
        (SimplexCategory.δ (n := 0) i)
    simp only [Category.assoc]
    change (sourceFace E i).left ≫ sourceMap (k := k) (E := E) 1 ≫ sourceSimplexProjection k 1 =
      sourceMap (k := k) (E := E) 0 ≫ (sourceFace k i).left ≫ sourceSimplexProjection k 1
    rw [sourceMap_snd (k := k) (E := E) 1, sourceFace_snd_assoc E i, hn, sourceFace_snd k i,
      sourceMap_snd_assoc (k := k) (E := E) 0]

/-- The actual product coface is Cartesian under scalar change. -/
theorem sourceMap_face_isPullback (i : Fin 2) :
    IsPullback (sourceFace E i).left (sourceMap (k := k) (E := E) 0)
      (sourceMap (k := k) (E := E) 1) (sourceFace k i).left := by
  apply IsPullback.of_right (h₁₂ := (source E 1).hom) (h₂₂ := (source k 1).hom)
    (v₁₃ := scalarMap (k := k) (E := E))
  · rw [MorphismProperty.Over.w (sourceFace E i), MorphismProperty.Over.w (sourceFace k i)]
    exact (sourceMap_isPullback (k := k) (E := E) 0).flip
  · exact sourceMap_face i
  · exact (sourceMap_isPullback (k := k) (E := E) 1).flip

end ScalarChange

/-- The ambient map of the actual graph fiber for an endpoint face. -/
abbrev ambientFace (F : Type u) [Field F] (q : ℕ) (i : Fin 2) :
    ambient F 0 q ⟶ ambient F 1 q :=
  correspondenceGraphFiberAmbientMap (source F 0).hom (source F 1).hom (target F q).hom
    (sourceFace F i).left (MorphismProperty.Over.w (sourceFace F i))

/-- The native graph-fiber ambient map is the original product map. -/
theorem ambientFace_eq_productMap (F : Type u) [Field F] (q : ℕ) (i : Fin 2) :
    ambientFace F q i = (SmoothSite.productMap (sourceFace F i) (𝟙 (target F q))).left :=
  rfl

/-- The first projection of the ambient face is its source face. -/
@[reassoc] theorem ambientFace_fst (F : Type u) [Field F] (q : ℕ) (i : Fin 2) :
    ambientFace F q i ≫ pullback.fst (source F 1).hom (target F q).hom =
      pullback.fst (source F 0).hom (target F q).hom ≫ (sourceFace F i).left :=
  pullback.lift_fst _ _ _

/-- The ambient face preserves the ordered torus factor. -/
@[reassoc] theorem ambientFace_snd (F : Type u) [Field F] (q : ℕ) (i : Fin 2) :
    ambientFace F q i ≫ pullback.snd (source F 1).hom (target F q).hom =
      pullback.snd (source F 0).hom (target F q).hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private theorem ambientFace_over (F : Type u) [Field F] (q : ℕ) (i : Fin 2) :
    ambientFace F q i ≫ (pullback.fst (source F 1).hom (target F q).hom ≫ (source F 1).hom) =
      pullback.fst (source F 0).hom (target F q).hom ≫ (source F 0).hom := by
  rw [ambientFace_fst_assoc, MorphismProperty.Over.w (sourceFace F i)]

section ScalarChange

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- The coefficient projection commutes with the literal ambient face. -/
theorem ambientMap_face (q : ℕ) (i : Fin 2) :
    ambientFace E q i ≫ ambientMap (k := k) (E := E) 1 q =
      ambientMap (k := k) (E := E) 0 q ≫ ambientFace k q i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, ambientMap_fst, ambientMap_fst_assoc,
      ambientFace_fst, ambientFace_fst_assoc, sourceMap_face]
  · simp only [Category.assoc, ambientMap_snd, ambientFace_snd, ambientFace_snd_assoc]

/-- The literal coefficient-change square of the ambient face is Cartesian. -/
theorem ambientMap_face_isPullback (q : ℕ) (i : Fin 2) :
    IsPullback (ambientFace E q i) (ambientMap (k := k) (E := E) 0 q)
      (ambientMap (k := k) (E := E) 1 q) (ambientFace k q i) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.fst (source E 1).hom (target E q).hom ≫ (source E 1).hom)
    (h₂₂ := pullback.fst (source k 1).hom (target k q).hom ≫ (source k 1).hom)
    (v₁₃ := scalarMap (k := k) (E := E))
  · rw [ambientFace_over E q i, ambientFace_over k q i]
    exact (ambientMap_isPullback (k := k) (E := E) 0 q).flip
  · exact ambientMap_face q i
  · exact (ambientMap_isPullback (k := k) (E := E) 1 q).flip

/-- The native support restriction retains the source projection after coefficient change. -/
theorem integralComponentMap_sourceProjection (q : ℕ) (z : ambient E 1 q) :
    integralComponentMap (ambientMap (k := k) (E := E) 1 q) z ≫
      ((integralComponentAt (ambientMap (k := k) (E := E) 1 q z)).subschemeι ≫
        pullback.fst (source k 1).hom (target k q).hom) =
      ((integralComponentAt z).subschemeι ≫
        pullback.fst (source E 1).hom (target E q).hom) ≫ sourceMap (k := k) (E := E) 1 := by
  rw [← Category.assoc, integralComponentMap_subschemeι, Category.assoc, ambientMap_fst,
    ← Category.assoc]

end ScalarChange

section Charts

variable (F : Type u) [Field F]

/-- The zero-simplex coordinate ring is the original field. -/
def zeroCoordinateEquiv : AlgebraicSimplex.CoordinateRing F 0 ≃ₐ[F] F :=
  (AlgebraicSimplex.polynomialEquiv F 0).trans (MvPolynomial.isEmptyAlgEquiv F (Fin 0))

/-- The one-simplex chart uses its first barycentric coordinate. -/
def oneCoordinateEquiv : AlgebraicSimplex.CoordinateRing F 1 ≃ₐ[F] F[X] :=
  (AlgebraicSimplex.polynomialEquiv F 1).trans (MvPolynomial.uniqueAlgEquiv F (Fin 1))

private theorem oneCoordinateEquiv_symm_X :
    (oneCoordinateEquiv F).symm Polynomial.X = AlgebraicSimplex.coordinate F 1 0 := by
  apply (oneCoordinateEquiv F).injective
  rw [AlgEquiv.apply_symm_apply]
  change Polynomial.X = MvPolynomial.uniqueAlgEquiv F (Fin 1)
    (AlgebraicSimplex.polynomialEquiv F 1
      (AlgebraicSimplex.coordinate F 1 (0 : Fin 1).castSucc))
  rw [AlgebraicSimplex.polynomialEquiv_coordinate_castSucc]
  simp [MvPolynomial.uniqueAlgEquiv]

private theorem zeroCoordinateEquiv_coordinate :
    zeroCoordinateEquiv F (AlgebraicSimplex.coordinate F 0 0) = 1 := by
  have h : AlgebraicSimplex.coordinate F 0 0 = 1 := by
    simpa using AlgebraicSimplex.sum_coordinate F 0
  rw [h, map_one]

private theorem face_ringHom (i : Fin 2) :
    (zeroCoordinateEquiv F).toRingHom.comp
        ((AlgebraicSimplex.face F (n := 0) i).comp (oneCoordinateEquiv F).symm.toRingHom) =
      Polynomial.evalRingHom (i.val : F) := by
  apply Polynomial.ringHom_ext
  · intro r
    change zeroCoordinateEquiv F (AlgebraicSimplex.face F (n := 0) i
      ((oneCoordinateEquiv F).symm (Polynomial.C r))) = Polynomial.eval (i.val : F) (Polynomial.C r)
    rw [show (oneCoordinateEquiv F).symm (Polynomial.C r) = AlgebraicSimplex.constant F 1 r
        from (oneCoordinateEquiv F).symm.commutes r,
      AlgebraicSimplex.face_eq_pullback, AlgebraicSimplex.pullback_constant, Polynomial.eval_C]
    exact (zeroCoordinateEquiv F).commutes r
  · change zeroCoordinateEquiv F (AlgebraicSimplex.face F (n := 0) i
      ((oneCoordinateEquiv F).symm Polynomial.X)) = Polynomial.eval (i.val : F) Polynomial.X
    rw [oneCoordinateEquiv_symm_X, Polynomial.eval_X]
    fin_cases i
    · change zeroCoordinateEquiv F (AlgebraicSimplex.face F (0 : Fin 2)
        (AlgebraicSimplex.coordinate F 1 0)) = ((0 : ℕ) : F)
      rw [AlgebraicSimplex.face_coordinate_self, map_zero, Nat.cast_zero]
    · have h : AlgebraicSimplex.face F (1 : Fin 2) (AlgebraicSimplex.coordinate F 1 0) =
          AlgebraicSimplex.coordinate F 0 0 :=
        AlgebraicSimplex.face_coordinate_succAbove F (1 : Fin 2) (0 : Fin 1)
      change zeroCoordinateEquiv F (AlgebraicSimplex.face F (1 : Fin 2)
        (AlgebraicSimplex.coordinate F 1 0)) = ((1 : ℕ) : F)
      rw [h, zeroCoordinateEquiv_coordinate, Nat.cast_one]

/-- The actual zero simplex in its field chart. -/
def simplexChart0 : (AlgebraicSimplex.smoothSiteObj F 0).left ≅ Spec (.of F) :=
  Scheme.Spec.mapIso (zeroCoordinateEquiv F).symm.toRingEquiv.toCommRingCatIso.op

/-- The actual one simplex in its polynomial chart. -/
def simplexChart1 : (AlgebraicSimplex.smoothSiteObj F 1).left ≅ Spec (.of F[X]) :=
  Scheme.Spec.mapIso (oneCoordinateEquiv F).symm.toRingEquiv.toCommRingCatIso.op

/-- The point chart of the original product source. -/
def sourceChart0 : (source F 0).left ≅ Spec (.of F) :=
  asIso (sourceSimplexProjection F 0) ≪≫ simplexChart0 F

/-- The polynomial chart of the original product source. -/
def sourceChart1 : (source F 1).left ≅ Spec (.of F[X]) :=
  asIso (sourceSimplexProjection F 1) ≪≫ simplexChart1 F

private theorem simplexFace_chart (i : Fin 2) :
    ((AlgebraicSimplex.cosimplicialSmoothSite F).δ (n := 0) i).left ≫ (simplexChart1 F).hom =
      (simplexChart0 F).hom ≫ PolynomialEndpointFiber.endpoint (i.val : F) := by
  change Spec.map (CommRingCat.ofHom (AlgebraicSimplex.face F (n := 0) i)) ≫
      Spec.map (CommRingCat.ofHom (oneCoordinateEquiv F).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (zeroCoordinateEquiv F).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (i.val : F)))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply (zeroCoordinateEquiv F).injective
  change zeroCoordinateEquiv F (AlgebraicSimplex.face F (n := 0) i
        ((oneCoordinateEquiv F).symm r)) =
      zeroCoordinateEquiv F ((zeroCoordinateEquiv F).symm (Polynomial.eval (i.val : F) r))
  rw [AlgEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (face_ringHom F i) r

/-- In the original source chart the two cofaces are evaluation at zero and one. -/
@[reassoc]
theorem sourceFace_chart (i : Fin 2) :
    (sourceFace F i).left ≫ (sourceChart1 F).hom =
      (sourceChart0 F).hom ≫ PolynomialEndpointFiber.endpoint (i.val : F) := by
  change (sourceFace F i).left ≫ sourceSimplexProjection F 1 ≫ (simplexChart1 F).hom =
    (sourceSimplexProjection F 0 ≫ (simplexChart0 F).hom) ≫
      PolynomialEndpointFiber.endpoint (i.val : F)
  rw [sourceFace_snd_assoc, simplexFace_chart, Category.assoc]

instance sourceFace_isClosedImmersion (i : Fin 2) : IsClosedImmersion (sourceFace F i).left := by
  have he : (sourceFace F i).left =
      (sourceChart0 F).hom ≫ PolynomialEndpointFiber.endpoint (i.val : F) ≫
        (sourceChart1 F).inv := by
    apply (cancel_mono (sourceChart1 F).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using sourceFace_chart F i
  rw [he]
  infer_instance

instance ambientFace_isClosedImmersion (q : ℕ) (i : Fin 2) :
    IsClosedImmersion (ambientFace F q i) := by
  have hp : IsPullback (ambientFace F q i) (pullback.fst (source F 0).hom (target F q).hom)
      (pullback.fst (source F 1).hom (target F q).hom) (sourceFace F i).left := by
    apply IsPullback.of_right (h₁₂ := pullback.snd (source F 1).hom (target F q).hom)
      (h₂₂ := (source F 1).hom) (v₁₃ := (target F q).hom)
    · rw [ambientFace_snd, MorphismProperty.Over.w (sourceFace F i)]
      exact (IsPullback.of_hasPullback (source F 0).hom (target F q).hom).flip
    · exact ambientFace_fst F q i
    · exact (IsPullback.of_hasPullback (source F 1).hom (target F q).hom).flip
  exact MorphismProperty.of_isPullback hp.flip
    (inferInstance : IsClosedImmersion (sourceFace F i).left)

private theorem facePullback_to_endpoint {H D : Scheme.{u}} {a : H ⟶ (source F 0).left}
    {b : H ⟶ D} {g : D ⟶ (source F 1).left} (i : Fin 2)
    (h : IsPullback a b (sourceFace F i).left g) :
    IsPullback (a ≫ (sourceChart0 F).hom) b (PolynomialEndpointFiber.endpoint (i.val : F))
      (g ≫ (sourceChart1 F).hom) :=
  h.of_iso (Iso.refl _) (sourceChart0 F) (Iso.refl _) (sourceChart1 F)
    (by simp) (by simp) (sourceFace_chart F i) (by simp)

/-- The actual coface pullback is Cartesian in the polynomial endpoint chart. -/
theorem faceEndpoint_isPullback {D : Scheme.{u}} (g : D ⟶ (source F 1).left) (i : Fin 2) :
    IsPullback (pullback.fst (sourceFace F i).left g ≫ (sourceChart0 F).hom)
      (pullback.snd (sourceFace F i).left g) (PolynomialEndpointFiber.endpoint (i.val : F))
      (g ≫ (sourceChart1 F).hom) :=
  facePullback_to_endpoint F i (IsPullback.of_hasPullback (sourceFace F i).left g)

/-- The full coface fiber is the literal endpoint fiber in the original parameter. -/
def faceEndpointIso {D : Scheme.{u}} (g : D ⟶ (source F 1).left) (i : Fin 2) :
    pullback (sourceFace F i).left g ≅
      PolynomialEndpointFiber.fiber (g ≫ (sourceChart1 F).hom) (i.val : F) :=
  (faceEndpoint_isPullback F g i).isoPullback

@[reassoc (attr := simp)] theorem faceEndpointIso_hom_inclusion {D : Scheme.{u}}
    (g : D ⟶ (source F 1).left) (i : Fin 2) :
    (faceEndpointIso F g i).hom ≫
      PolynomialEndpointFiber.fiberInclusion (g ≫ (sourceChart1 F).hom) (i.val : F) =
    pullback.snd (sourceFace F i).left g :=
  (faceEndpoint_isPullback F g i).isoPullback_hom_snd

@[reassoc (attr := simp)] theorem faceEndpointIso_hom_point {D : Scheme.{u}}
    (g : D ⟶ (source F 1).left) (i : Fin 2) :
    (faceEndpointIso F g i).hom ≫ pullback.fst
      (PolynomialEndpointFiber.endpoint (i.val : F)) (g ≫ (sourceChart1 F).hom) =
    pullback.fst (sourceFace F i).left g ≫ (sourceChart0 F).hom :=
  (faceEndpoint_isPullback F g i).isoPullback_hom_fst

/-- Sending the graph fiber into the degree-one ambient retains its support inclusion. -/
theorem graphFiberMap_ambientFace (q : ℕ) (z : ambient F 1 q) (i : Fin 2) :
    correspondenceGraphFiberMap (source F 0).hom (source F 1).hom (target F q).hom z
        (sourceFace F i).left (MorphismProperty.Over.w (sourceFace F i)) ≫ ambientFace F q i =
    pullback.snd (sourceFace F i).left
        ((integralComponentAt z).subschemeι ≫ pullback.fst (source F 1).hom (target F q).hom) ≫
      (integralComponentAt z).subschemeι :=
  (isPullback_correspondenceGraphFiberMap (source F 0).hom (source F 1).hom (target F q).hom z
    (sourceFace F i).left (MorphismProperty.Over.w (sourceFace F i))).w

end Charts

section ScalarEndpoint

variable {k E : Type u} [Field k] [Field E] [Algebra k E] {D : Scheme.{u}}
  (g : D ⟶ (source E 1).left) (i : Fin 2)

/-- The upstairs coface fiber is Cartesian over the downstairs polynomial endpoint. -/
theorem scalarFaceEndpoint_isPullback :
    IsPullback
      (pullback.fst (sourceFace E i).left g ≫ sourceMap (k := k) (E := E) 0 ≫ (sourceChart0 k).hom)
      (pullback.snd (sourceFace E i).left g) (PolynomialEndpointFiber.endpoint (i.val : k))
      ((g ≫ sourceMap (k := k) (E := E) 1) ≫ (sourceChart1 k).hom) := by
  have hp := (IsPullback.of_hasPullback (sourceFace E i).left g).paste_horiz
    (sourceMap_face_isPullback (k := k) (E := E) i).flip
  simpa only [Category.assoc] using facePullback_to_endpoint k i hp

/-- The whole upstairs endpoint fiber on the restricted polynomial parameter. -/
def scalarFaceEndpointIso : pullback (sourceFace E i).left g ≅
    PolynomialEndpointFiber.fiber
      ((g ≫ sourceMap (k := k) (E := E) 1) ≫ (sourceChart1 k).hom) (i.val : k) :=
  (scalarFaceEndpoint_isPullback (k := k) g i).isoPullback

@[reassoc (attr := simp)] theorem scalarFaceEndpointIso_hom_inclusion :
    (scalarFaceEndpointIso (k := k) g i).hom ≫ PolynomialEndpointFiber.fiberInclusion
        ((g ≫ sourceMap (k := k) (E := E) 1) ≫ (sourceChart1 k).hom) (i.val : k) =
      pullback.snd (sourceFace E i).left g :=
  (scalarFaceEndpoint_isPullback (k := k) g i).isoPullback_hom_snd

@[reassoc (attr := simp)] theorem scalarFaceEndpointIso_hom_point :
    (scalarFaceEndpointIso (k := k) g i).hom ≫ pullback.fst
        (PolynomialEndpointFiber.endpoint (i.val : k))
        ((g ≫ sourceMap (k := k) (E := E) 1) ≫ (sourceChart1 k).hom) =
      pullback.fst (sourceFace E i).left g ≫ sourceMap (k := k) (E := E) 0 ≫ (sourceChart0 k).hom :=
  (scalarFaceEndpoint_isPullback (k := k) g i).isoPullback_hom_fst

end ScalarEndpoint

end AlgebraicGeometry.MotivicCohomology.DiagonalFiniteCyclePushforward
