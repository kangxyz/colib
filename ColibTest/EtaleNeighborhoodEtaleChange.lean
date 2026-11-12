/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtaleChange
import Colib.AlgebraicGeometry.Sites.Smooth.Etale.AffineSpaceInduction
import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite

noncomputable section

universe u

section General

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {X Y : Scheme.SmoothSite S} [IsAffine X.left] [IsAffine Y.left]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {ξ : Spec (.of Ω) ⟶ X.left} {η : Spec (.of Ω) ⟶ Y.left}
  (F : (Scheme.SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
  (f : X ⟶ Y) [Etale f.left] (h : ξ ≫ f.left = η)

example : (etaleNeighborhoodValueEtaleIso f h F).hom =
    etaleNeighborhoodValuePullback f h F := rfl

example : (etaleNeighborhoodValueEtaleIso f h F).inv =
    etaleNeighborhoodValueComp f h F := rfl

example (A : EtaleNeighborhood X ξ) :
    ((etaleNeighborhoodToSmooth Y η).obj (etaleNeighborhoodComp f h A)).left =
      ((etaleNeighborhoodToSmooth X ξ).obj A).left := rfl

example (A : EtaleNeighborhood X ξ) :
    etaleNeighborhoodMark Y η (etaleNeighborhoodComp f h A) =
      etaleNeighborhoodMark X ξ A := rfl

example (B : EtaleNeighborhood Y η)
    (b : F.obj (op ((etaleNeighborhoodToSmooth Y η).obj B))) :
    (etaleNeighborhoodValueEtaleIso f h F).hom (toEtaleNeighborhoodValue Y η B F b) =
      toEtaleNeighborhoodValue X ξ (etaleNeighborhoodPullback f h B) F
        (F.map (etaleNeighborhoodPullbackHom f h B).op b) :=
  ConcreteCategory.congr_hom (toEtaleNeighborhoodValue_pullback f h F B) b

example (A : EtaleNeighborhood X ξ)
    (a : F.obj (op ((etaleNeighborhoodToSmooth X ξ).obj A))) :
    (etaleNeighborhoodValueEtaleIso f h F).inv (toEtaleNeighborhoodValue X ξ A F a) =
      toEtaleNeighborhoodValue Y η (etaleNeighborhoodComp f h A) F
        (F.map (etaleNeighborhoodCompIso f h A).inv.op a) :=
  ConcreteCategory.congr_hom (toEtaleNeighborhoodValue_comp f h F A) a

example (a : etaleNeighborhoodValue X ξ F) :
    etaleNeighborhoodValuePullback f h F (etaleNeighborhoodValueComp f h F a) = a :=
  ConcreteCategory.congr_hom (etaleNeighborhoodValueComp_pullback f h F) a

example (b : etaleNeighborhoodValue Y η F) :
    etaleNeighborhoodValueComp f h F (etaleNeighborhoodValuePullback f h F b) = b :=
  ConcreteCategory.congr_hom (etaleNeighborhoodValuePullback_valueComp f h F) b

example : etaleNeighborhoodBaseValueMap Y η F ≫
    (etaleNeighborhoodValueEtaleIso f h F).hom = etaleNeighborhoodBaseValueMap X ξ F :=
  etaleNeighborhoodBaseValueMap_etaleIso_hom f h F

example : etaleNeighborhoodBaseValueMap X ξ F ≫
    (etaleNeighborhoodValueEtaleIso f h F).inv = etaleNeighborhoodBaseValueMap Y η F :=
  etaleNeighborhoodBaseValueMap_etaleIso_inv f h F

end General

section OriginalBaseValue

variable (k : Type u) [Field k] (d : ℕ)
  (P : PresheafWithTransfers.{u + 1} k)

example :
    etaleNeighborhoodBaseValueMap (affineSpaceObject k d)
        (affineSpaceOriginGeometricPoint k d).hom ((PresheafWithTransfers.toPresheaf k).obj P) ≫
      affineSpaceOriginProjectionPullback k d ((PresheafWithTransfers.toPresheaf k).obj P) =
        etaleNeighborhoodBaseValueMap (affineSpaceObject k (d + 1))
          (affineSpaceOriginGeometricPoint k (d + 1)).hom
          ((PresheafWithTransfers.toPresheaf k).obj P) :=
  etaleNeighborhoodBaseValueMap_pullback (affineSpaceCoordinateProjection k d)
    (affineSpaceOriginGeometricPoint_projection k d) _

example {X : Scheme.SmoothSite (Spec (.of k))} [IsAffine X.left]
    {ξ : Spec (.of (AlgebraicClosure k)) ⟶ X.left}
    (f : X ⟶ affineSpaceObject k d) [Etale f.left]
    (h : ξ ≫ f.left = (affineSpaceOriginGeometricPoint k d).hom) :
    etaleNeighborhoodBaseValueMap (affineSpaceObject k d)
        (affineSpaceOriginGeometricPoint k d).hom ((PresheafWithTransfers.toPresheaf k).obj P) ≫
      (etaleNeighborhoodValueEtaleIso f h ((PresheafWithTransfers.toPresheaf k).obj P)).hom =
        etaleNeighborhoodBaseValueMap X ξ ((PresheafWithTransfers.toPresheaf k).obj P) :=
  etaleNeighborhoodBaseValueMap_etaleIso_hom f h _

example {X : Scheme.SmoothSite (Spec (.of k))} [IsAffine X.left]
    (ξ : Spec (.of (AlgebraicClosure k)) ⟶ X.left) (A : EtaleNeighborhood X ξ) :
    etaleNeighborhoodBaseValueMap X ξ ((PresheafWithTransfers.toPresheaf k).obj P) =
      PresheafWithTransfers.transfer P ((Cor.graphFunctor k).map
        (homMk ((etaleNeighborhoodToSmooth X ξ).obj A).hom
          (by change _ ≫ 𝟙 (Spec (.of k)) = _; simp) :
            (etaleNeighborhoodToSmooth X ξ).obj A ⟶ base (Spec (.of k)))) ≫
        toEtaleNeighborhoodValue X ξ A ((PresheafWithTransfers.toPresheaf k).obj P) :=
  etaleNeighborhoodBaseValueMap_eq _ A

end OriginalBaseValue

#print axioms etaleNeighborhoodComp
#print axioms etaleNeighborhoodCompIso
#print axioms etaleNeighborhoodValueComp_pullback
#print axioms etaleNeighborhoodValuePullback_valueComp
#print axioms etaleNeighborhoodValueEtaleIso
#print axioms toEtaleNeighborhoodValueFromObject_pullback
#print axioms etaleNeighborhoodBaseValueMap_eq
#print axioms etaleNeighborhoodBaseValueMap_pullback
#print axioms etaleNeighborhoodBaseValueMap_etaleIso_hom
#print axioms etaleNeighborhoodBaseValueMap_etaleIso_inv

end
