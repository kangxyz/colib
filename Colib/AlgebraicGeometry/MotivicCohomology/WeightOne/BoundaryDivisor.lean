/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.Norm
public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafificationMaps
public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.GeometricallyIntegral

/-!
# The actual all-degree boundary divisor chain map

The source is the accepted boundary-one sheaf complex. The target is the actual
canonical reduced-torus singular complex, sheafified only after taking chains.
Integral-affine components are the already proved genuine boundary divisors.
Every alternating face retains its integer sign and actual graph restriction.

Adapted from Motivic/Cohomology/WeightOne/Geometry/BoundaryOneSheafDivisor.lean
and BoundaryOneDivisorNorm.lean at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicSimplex
open scoped Simplicial

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- Literal relative simplex products of affine sources are affine. -/
instance isAffine_productSimplex (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] (n : ℕ) : IsAffine (product X (smoothSiteObj k n)).left := by
  change IsAffine (pullback X.hom (structureMap k n))
  have : IsAffineHom (structureMap k n) :=
    isAffineHom_of_isAffine (X := Spec (.of (CoordinateRing k n)))
      (Y := Spec (.of k)) (structureMap k n)
  exact IsAffine.of_isPullback (X := X.left)
    (IsPullback.of_hasPullback X.hom (structureMap k n))

/-- The actual geometrically integral simplex preserves integral sources. -/
instance isIntegral_productSimplex (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] (n : ℕ) : IsIntegral (product X (smoothSiteObj k n)).left := by
  change IsIntegral (pullback X.hom (structureMap k n))
  have : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (X := X.left) (Y := Spec (.of k)) X.hom
  exact AlgebraicSimplex.integral_product k (V := X.left) X.hom n

/-- The actual original boundary-one raw singular complex. -/
abbrev rawBoundarySingular := (singularChainsFunctor k).obj (largeBoundaryOnePresheaf k)

/-- The genuine divisor on the dense subsite in every original singular degree. -/
def integralAffineSingularDivisor (n : ℕ) :
    (integralAffineInclusion k).op ⋙ (rawBoundarySingular k).X n ⟶
      (integralAffineInclusion k).op ⋙ (rawReducedSingular k).X n where
  app X := by
    let : IsAffine X.unop.obj.left := X.unop.property.1
    let : IsIntegral X.unop.obj.left := X.unop.property.2
    exact affineReducedBoundaryDivisor (product X.unop.obj (smoothSiteObj k n))
  naturality {X Y} f := by
    let : IsAffine X.unop.obj.left := X.unop.property.1
    let : IsIntegral X.unop.obj.left := X.unop.property.2
    let : IsAffine Y.unop.obj.left := Y.unop.property.1
    let : IsIntegral Y.unop.obj.left := Y.unop.property.2
    exact affineReducedBoundaryDivisor_natural
      (X := product Y.unop.obj (smoothSiteObj k n))
      (Y := product X.unop.obj (smoothSiteObj k n))
      (SmoothSite.productMap f.unop.hom (𝟙 (smoothSiteObj k n)))

/-- The actual degreewise divisor between the original ordinary sheafified terms. -/
def singularSheafDivisor (n : ℕ) :
    (boundaryOneSheafComplex k).X n ⟶
      ((sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
        (rawReducedTorus k)).X n :=
  integralAffineSheafifyMap k (integralAffineSingularDivisor k n)

/-- The raw source maps to the actual target sheaf through its original unit. -/
def singularDivisorToSheaf (n : ℕ) :
    (rawBoundarySingular k).X n ⟶
      (((sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
        (rawReducedTorus k)).X n).obj :=
  toSheafify (nisnevichTopology (Spec (.of k))) ((rawBoundarySingular k).X n) ≫
    (singularSheafDivisor k n).hom

/-- The extension recovers the precise genuine affine divisor followed by the unit. -/
theorem singularDivisorToSheaf_app (n : ℕ) (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    (singularDivisorToSheaf k n).app (op X) =
      affineReducedBoundaryDivisor (product X (smoothSiteObj k n)) ≫
        (toSheafify (nisnevichTopology (Spec (.of k)))
          ((rawReducedSingular k).X n)).app (op X) :=
  congr_app (integralAffineSheafifyMap_restrict k (integralAffineSingularDivisor k n))
    (op ⟨X, inferInstance, inferInstance⟩)

/-- Each genuine divisor commutes with the original ordered alternating faces. -/
theorem affineReducedBoundaryDivisor_d (n : ℕ) (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    ((rawBoundarySingular k).d (n + 1) n).app (op X) ≫
        affineReducedBoundaryDivisor (product X (smoothSiteObj k n)) =
      affineReducedBoundaryDivisor (product X (smoothSiteObj k (n + 1))) ≫
        ((rawReducedSingular k).d (n + 1) n).app (op X) := by
  rw [singularChainsFunctor_obj_d_app, singularChainsFunctor_obj_d_app]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact affineReducedBoundaryDivisor_natural
    (X := product X (smoothSiteObj k n))
    (Y := product X (smoothSiteObj k (n + 1)))
    (SmoothSite.productMap (𝟙 X) ((cosimplicialSmoothSite k).δ i))

/-- The local maps commute with the differential as actual natural transformations. -/
theorem integralAffineSingularDivisor_d (n : ℕ) :
    (integralAffineInclusion k).op.whiskerLeft ((rawBoundarySingular k).d (n + 1) n) ≫
        integralAffineSingularDivisor k n =
      integralAffineSingularDivisor k (n + 1) ≫
        (integralAffineInclusion k).op.whiskerLeft ((rawReducedSingular k).d (n + 1) n) := by
  apply NatTrans.ext
  funext X
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  exact affineReducedBoundaryDivisor_d k n X.unop.obj

/-- Dense gluing and actual sheafification preserve the original differential. -/
theorem singularSheafDivisor_d (n : ℕ) :
    (boundaryOneSheafComplex k).d (n + 1) n ≫ singularSheafDivisor k n =
      singularSheafDivisor k (n + 1) ≫
        ((sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
          (rawReducedTorus k)).d (n + 1) n := by
  have h := congrArg (integralAffineSheafifyMap k) (integralAffineSingularDivisor_d k n)
  change (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map
      ((rawBoundarySingular k).d (n + 1) n) ≫
      integralAffineSheafifyMap k (integralAffineSingularDivisor k n) =
    integralAffineSheafifyMap k (integralAffineSingularDivisor k (n + 1)) ≫
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map
        ((rawReducedSingular k).d (n + 1) n)
  simpa only [integralAffineSheafifyMap_comp, integralAffineSheafifyMap_whisker] using h

/-- The genuine all-degree divisor chain map with the accepted boundary-one source. -/
def sheafDivisorChainMap : boundaryOneSheafComplex k ⟶
    (sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
      (rawReducedTorus k) where
  f := singularSheafDivisor k
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact (singularSheafDivisor_d k j).symm

/-- The original degreewise raw ordinary norm. -/
abbrev rawNorm (n : ℕ) := ((singularChainsFunctor k).map (reducedNorm k)).f n

/-- The actual local divisor lands in the kernel of the genuine raw norm. -/
theorem localDivisor_norm (n : ℕ) :
    integralAffineSingularDivisor k n ≫
      (integralAffineInclusion k).op.whiskerLeft (rawNorm k n) = 0 := by
  apply NatTrans.ext
  funext X
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  change affineReducedBoundaryDivisor (product X.unop.obj (smoothSiteObj k n)) ≫
    (reducedNorm k).app (op (product X.unop.obj (smoothSiteObj k n))) = 0
  rw [reducedNorm_app, affineReducedBoundaryDivisor_norm]

/-- The actual sheafified divisor followed by the actual norm is zero in every degree. -/
theorem singularSheafDivisor_norm (n : ℕ) :
    singularSheafDivisor k n ≫ (reducedNormSheafMap k).f n = 0 := by
  have h := congrArg (integralAffineSheafifyMap k) (localDivisor_norm k n)
  change integralAffineSheafifyMap k (integralAffineSingularDivisor k n) ≫
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map
      (rawNorm k n) = 0
  simpa only [integralAffineSheafifyMap_comp, integralAffineSheafifyMap_whisker,
    integralAffineSheafifyMap_zero] using h

/-- The actual divisor and norm form a genuine short complex, not an assumed one. -/
@[reassoc (attr := simp)] theorem sheafDivisorChainMap_norm :
    sheafDivisorChainMap k ≫ reducedNormSheafMap k = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact singularSheafDivisor_norm k n

end AlgebraicGeometry.MotivicCohomology.WeightOne
