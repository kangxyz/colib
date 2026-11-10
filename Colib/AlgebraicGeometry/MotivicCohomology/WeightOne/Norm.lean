/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.SectionNaturality
public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafification
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.Sheaf
public import Colib.AlgebraicGeometry.Simplex.SheafifiedChains

/-!
# The global ordinary norm on the canonical reduced torus

The actual integral-affine determinant norm is now a natural transformation.
The genuine dense integral-affine subsite extends it uniquely into the ordinary
global-units sheaf. The target carries no invented transfer action. Singular
chains are formed before ordinary sheafification, in coefficient universe u+1.

Adapted from Motivic/Cohomology/WeightOne/Geometry/ReducedTorusNorm.lean at
revision a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicSimplex

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- The original canonical large reduced torus, with only its transfers forgotten. -/
abbrev rawReducedTorus := (toPresheaf k).obj (reducedTorus k 1)

/-- The actual reduced norm, natural on the genuine integral-affine full subcategory. -/
def integralAffineNorm : (integralAffineInclusion k).op ⋙ rawReducedTorus k ⟶
    (integralAffineInclusion k).op ⋙ largeUnitsPresheaf (Spec (.of k)) where
  app X := by
    let : IsAffine X.unop.obj.left := X.unop.property.1
    let : IsIntegral X.unop.obj.left := X.unop.property.2
    exact affineReducedNorm X.unop.obj
  naturality {X Y} f := by
    let : IsAffine X.unop.obj.left := X.unop.property.1
    let : IsIntegral X.unop.obj.left := X.unop.property.2
    let : IsAffine Y.unop.obj.left := Y.unop.property.1
    let : IsIntegral Y.unop.obj.left := Y.unop.property.2
    exact affineReducedNorm_natural f.unop.hom

/-- The unique ordinary global extension of the actual local determinant norm. -/
def reducedNorm : rawReducedTorus k ⟶ largeUnitsPresheaf (Spec (.of k)) :=
  extendIntegralAffineHom k (G := largeUnitsSheaf (Spec (.of k))) (integralAffineNorm k)

/-- The global map restricts to the actual local natural transformation. -/
@[simp] theorem reducedNorm_restrict :
    (integralAffineInclusion k).op.whiskerLeft (reducedNorm k) = integralAffineNorm k :=
  extendIntegralAffineHom_restrict k (G := largeUnitsSheaf (Spec (.of k)))
    (integralAffineNorm k)

/-- Its original integral-affine component is the concrete determinant norm. -/
@[simp] theorem reducedNorm_app (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    (reducedNorm k).app (op X) = affineReducedNorm X :=
  extendIntegralAffineHom_app k (G := largeUnitsSheaf (Spec (.of k)))
    (integralAffineNorm k) ⟨X, inferInstance, inferInstance⟩

attribute [local instance] AffineSectionCoordinates.sections_isIntegrallyClosed
  AffineSectionCoordinates.sections_isNoetherianRing

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On every original signed cycle the global quotient norm is the actual support norm. -/
theorem reducedNorm_affine_toReduced (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left]
    (z : Cor.mk X ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    (reducedNorm k).app (op X)
        ((toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z)) =
      (affineSectionIso X (largeUnitsPresheaf (Spec (.of k)))).inv
        ((specUnitsIso (AffineSectionCoordinates.structureMap X)).inv
          (ULift.up (powerOneNorm (AffineSectionCoordinates.structureMap X)
            ((Cor.graphFunctor k).map (AffineSectionCoordinates.iso X).hom ≫ z)))) := by
  rw [reducedNorm_app]
  change (affineSectionIso X (largeUnitsPresheaf (Spec (.of k)))).inv
    ((specUnitsIso (AffineSectionCoordinates.structureMap X)).inv
      (reducedNormApp (AffineSectionCoordinates.structureMap X)
        (transfer (reducedTorus k 1)
          ((Cor.graphFunctor k).map (AffineSectionCoordinates.iso X).hom)
          ((toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z))))) = _
  exact congrArg
    (fun t => (affineSectionIso X (largeUnitsPresheaf (Spec (.of k)))).inv
      ((specUnitsIso (AffineSectionCoordinates.structureMap X)).inv t))
    ((congrArg (reducedNormApp (AffineSectionCoordinates.structureMap X))
      (reducedTorus_transfer_apply k 1
        (X := Cor.mk (AffineSectionCoordinates.obj X)) (Y := Cor.mk X)
        ((Cor.graphFunctor k).map (AffineSectionCoordinates.iso X).hom) z)).trans
      (reducedNormApp_toReduced (AffineSectionCoordinates.structureMap X)
        ((Cor.graphFunctor k).map (AffineSectionCoordinates.iso X).hom ≫ z)))

/-- These actual components determine the global norm uniquely. -/
theorem reducedNorm_unique (η : rawReducedTorus k ⟶ largeUnitsPresheaf (Spec (.of k)))
    (hη : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      η.app (op X) = affineReducedNorm X) : η = reducedNorm k := by
  apply extendIntegralAffineHom_unique k (G := largeUnitsSheaf (Spec (.of k)))
    (integralAffineNorm k)
  apply NatTrans.ext
  funext X
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  exact hη X.unop.obj

/-- The same actual norm after ordinary source sheafification. -/
def reducedNormSheaf :
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
      (rawReducedTorus k) ⟶ largeUnitsSheaf (Spec (.of k)) :=
  sheafifyIntegralAffineHom k (integralAffineNorm k)

/-- The actual sheafification unit recovers the global ordinary norm. -/
@[reassoc (attr := simp)] theorem toSheafify_reducedNormSheaf :
    toSheafify (nisnevichTopology (Spec (.of k))) (rawReducedTorus k) ≫
      (reducedNormSheaf k).hom = reducedNorm k :=
  toSheafify_sheafifyIntegralAffineHom k (F := rawReducedTorus k)
    (G := largeUnitsSheaf (Spec (.of k))) (integralAffineNorm k)

/-- The original raw reduced singular chains on literal relative products. -/
abbrev rawReducedSingular := (singularChainsFunctor k).obj (rawReducedTorus k)

/-- The genuine ordinary unit singular chains, sheafified after singular chains. -/
abbrev unitsSheafComplex :=
  (sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
    (largeUnitsPresheaf (Spec (.of k)))

/-- The actual reduced norm in the original ordinary sheafified singular complexes. -/
def reducedNormSheafMap :
    (sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).obj
      (rawReducedTorus k) ⟶ unitsSheafComplex k :=
  (sheafifiedSingularChainsFunctor k (nisnevichTopology (Spec (.of k)))).map (reducedNorm k)

/-- Every component is sheafification of the actual parameter-wise ordinary norm. -/
@[simp] theorem reducedNormSheafMap_f (n : ℕ) :
    (reducedNormSheafMap k).f n =
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map
        (((singularChainsFunctor k).map (reducedNorm k)).f n) := rfl

end AlgebraicGeometry.MotivicCohomology.WeightOne
