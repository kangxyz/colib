/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.QuasiIso

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicSimplex
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers AlgebraicGeometry.NativeTorusPolynomial
open AlgebraicGeometry.MotivicCohomology.WeightOne

universe u

noncomputable section

variable (k : Type u) [Field k]

example : rawReducedTorus k ⟶ largeUnitsPresheaf (Spec (.of k)) := reducedNorm k

example : (integralAffineInclusion k).op.whiskerLeft (reducedNorm k) =
    integralAffineNorm k := reducedNorm_restrict k

example (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    (reducedNorm k).app (op X) = affineReducedNorm X := reducedNorm_app k X

attribute [local instance] AffineSectionCoordinates.sections_isIntegrallyClosed
  AffineSectionCoordinates.sections_isNoetherianRing

example (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (z : Cor.mk X ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    (reducedNorm k).app (op X)
        ((toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z)) =
      (affineSectionIso X (largeUnitsPresheaf (Spec (.of k)))).inv
        ((specUnitsIso (AffineSectionCoordinates.structureMap X)).inv
          (ULift.up (powerOneNorm (AffineSectionCoordinates.structureMap X)
            ((Cor.graphFunctor k).map (AffineSectionCoordinates.iso X).hom ≫ z)))) :=
  reducedNorm_affine_toReduced k X z

example (η : rawReducedTorus k ⟶ largeUnitsPresheaf (Spec (.of k)))
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      η.app (op X) = affineReducedNorm X) : η = reducedNorm k := reducedNorm_unique k η h

example : toSheafify (nisnevichTopology (Spec (.of k))) (rawReducedTorus k) ≫
    (reducedNormSheaf k).hom = reducedNorm k := toSheafify_reducedNormSheaf k

example (n : ℕ) : (reducedNormSheafMap k).f n =
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map
      (rawNorm k n) := reducedNormSheafMap_f k n

example {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y) :
    (rawReducedTorus k).map f.op ≫ affineReducedNorm X =
      affineReducedNorm Y ≫ (largeUnitsPresheaf (Spec (.of k))).map f.op :=
  affineReducedNorm_natural f

example {X Y : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine Y.left]
    [IsIntegral X.left] [IsIntegral Y.left] (f : X ⟶ Y) :
    (largeBoundaryOnePresheaf k).map f.op ≫ affineReducedBoundaryDivisor X =
      affineReducedBoundaryDivisor Y ≫ (rawReducedTorus k).map f.op :=
  affineReducedBoundaryDivisor_natural f

example (X : SmoothSite (Spec (.of k))) [IsAffine X.left] (n : ℕ) :
    IsAffine (product X (smoothSiteObj k n)).left := inferInstance

example (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] (n : ℕ) :
    IsIntegral (product X (smoothSiteObj k n)).left := inferInstance

example (n : ℕ) : (boundaryOneSheafComplex k).X n ⟶
    ((sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
      (rawReducedTorus k)).X n := singularSheafDivisor k n

example (n : ℕ) (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left] :
    (singularDivisorToSheaf k n).app (op X) =
      affineReducedBoundaryDivisor (product X (smoothSiteObj k n)) ≫
        (toSheafify (nisnevichTopology (Spec (.of k)))
          ((rawReducedSingular k).X n)).app (op X) := singularDivisorToSheaf_app k n X

example (n : ℕ) :
    integralAffineSingularDivisor k n ≫
      (integralAffineInclusion k).op.whiskerLeft (rawNorm k n) = 0 := localDivisor_norm k n

example (n : ℕ) : singularSheafDivisor k n ≫ (reducedNormSheafMap k).f n = 0 :=
  singularSheafDivisor_norm k n

example : sheafDivisorChainMap k ≫ reducedNormSheafMap k = 0 :=
  sheafDivisorChainMap_norm k

example (n : ℕ) (X : (integralAffineProperty k).FullSubcategoryᵒᵖ) :
    Function.Injective ((integralAffineSingularDivisor k n).app X) :=
  localDivisor_injective k n X

example (n : ℕ) (X : (integralAffineProperty k).FullSubcategoryᵒᵖ)
    (z : ((rawReducedSingular k).X n).obj (op X.unop.obj))
    (hz : (rawNorm k n).app (op X.unop.obj) z = 0) :
    ∃ m, (integralAffineSingularDivisor k n).app X m = z := localDivisor_exact k n X z hz

example (n : ℕ) :
    (integralAffineInclusion k).op ⋙ (rawBoundarySingular k).X n ≅
      (integralAffineInclusion k).op ⋙ kernel (rawNorm k n) := localKernelIso k n

example (n : ℕ) :
    IsLimit (KernelFork.ofι ((sheafDivisorChainMap k).f n)
      (show (sheafDivisorChainMap k).f n ≫ (reducedNormSheafMap k).f n = 0 from
        singularSheafDivisor_norm k n)) := divisorIsKernel k n

example (n : ℕ) : Epi ((reducedNormSheafMap k).f n) := norm_epi k n

example : (shortComplex k).ShortExact := shortExact k

example : (shortComplex k).Exact := (shortExact k).exact

example : Mono (sheafDivisorChainMap k) := (shortExact k).mono_f

example : Epi (reducedNormSheafMap k) := (shortExact k).epi_g

example (n : ℕ) : IsZero ((boundaryOneSheafComplex k).homology n) :=
  isZero_homology_boundaryOneSheafComplex k n

example : QuasiIso (reducedNormSheafMap k) := inferInstance

example : QuasiIsoAt (reducedNormSheafMap k) 0 :=
  (reducedNormSheafMap_quasiIso k).quasiIsoAt 0

example (n : ℕ) : QuasiIsoAt (reducedNormSheafMap k) (n + 1) :=
  (reducedNormSheafMap_quasiIso k).quasiIsoAt (n + 1)

example (n : ℕ) : IsIso (HomologicalComplex.homologyMap (reducedNormSheafMap k) n) :=
  (quasiIsoAt_iff_isIso_homologyMap (reducedNormSheafMap k) n).mp
    ((reducedNormSheafMap_quasiIso k).quasiIsoAt n)
