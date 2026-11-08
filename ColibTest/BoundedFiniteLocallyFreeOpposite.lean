module

import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeOpposite

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

noncomputable section

attribute [local instance] Abelian.hasFiniteBiproducts

variable (X : Scheme.{u})

example : Waldhausen.IsCompatibleDual (boundedFiniteLocallyFreeWaldhausen X)
    (boundedFiniteLocallyFreeOppositeWaldhausen X) :=
  boundedFiniteLocallyFreeOppositeWaldhausen_compatible X

example : Waldhausen.Fibration.RowFactorization.JointData
    (Waldhausen.Fibration.NestedWeakEquivalences.refl (boundedFiniteLocallyFreeWaldhausen X)) :=
  boundedFiniteLocallyFreeJointData X (Waldhausen.Fibration.NestedWeakEquivalences.refl _)

example : Waldhausen.Fibration.RowFactorization.SecondEndpointSection
    (Waldhausen.Fibration.NestedWeakEquivalences.refl (boundedFiniteLocallyFreeWaldhausen X))
    (boundedFiniteLocallyFreeJointData X
      (Waldhausen.Fibration.NestedWeakEquivalences.refl _)) :=
  boundedFiniteLocallyFreeJointData_secondEndpointSection X _

example : Waldhausen.Fibration.RowFactorization.JointData
    (Waldhausen.Fibration.NestedWeakEquivalences.refl
      (boundedFiniteLocallyFreeOppositeWaldhausen X)) :=
  boundedFiniteLocallyFreeOppositeJointData X

example {K L : (boundedFiniteLocallyFreeComplex X).FullSubcategoryᵒᵖ} (f : K ⟶ L) :
    (((boundedFiniteLocallyFreePerfectInclusion X).op.map f).unop).hom = f.unop.hom := rfl

example (f : Arrow (boundedFiniteLocallyFreeComplex X).FullSubcategoryᵒᵖ) :
    (RingedSpace.perfectComplexesOppositeJointData X.toRingedSpace).inl.app
        ((boundedFiniteLocallyFreePerfectInclusion X).op.mapArrow.obj f) ≫
      ((boundedFiniteLocallyFreePerfectOppositeJointIso X).inv.app f).hom.left =
    (boundedFiniteLocallyFreePerfectInclusion X).op.map
      ((boundedFiniteLocallyFreeOppositeJointData X).inl.app f) :=
  boundedFiniteLocallyFreePerfectOppositeJointIso_inv_inl X f

example (f : Arrow (boundedFiniteLocallyFreeComplex X).FullSubcategoryᵒᵖ) :
    (RingedSpace.perfectComplexesOppositeJointData X.toRingedSpace).inr.app
        ((boundedFiniteLocallyFreePerfectInclusion X).op.mapArrow.obj f) ≫
      ((boundedFiniteLocallyFreePerfectOppositeJointIso X).inv.app f).hom.left =
    (boundedFiniteLocallyFreePerfectInclusion X).op.map
      ((boundedFiniteLocallyFreeOppositeJointData X).inr.app f) :=
  boundedFiniteLocallyFreePerfectOppositeJointIso_inv_inr X f

example (f : Arrow (boundedFiniteLocallyFreeComplex X).FullSubcategoryᵒᵖ) :
    ((boundedFiniteLocallyFreePerfectOppositeJointIso X).inv.app f).hom.right ≫
      (boundedFiniteLocallyFreePerfectInclusion X).op.map
        ((boundedFiniteLocallyFreeOppositeJointData X).projection.app f) =
    (RingedSpace.perfectComplexesOppositeJointData X.toRingedSpace).projection.app
      ((boundedFiniteLocallyFreePerfectInclusion X).op.mapArrow.obj f) :=
  boundedFiniteLocallyFreePerfectOppositeJointIso_inv_projection X f
