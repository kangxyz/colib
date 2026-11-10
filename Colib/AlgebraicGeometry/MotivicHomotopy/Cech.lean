/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cech
public import Colib.CategoryTheory.Sites.Simplicial.MappingCofiber
public import Colib.CategoryTheory.Sites.Simplicial.Representable

/-!
# The pointed Čech augmentation and its reduced cofiber

Termwise Yoneda sends the relative Čech powers to a simplicial presheaf.
Freely adjoining a basepoint gives the pointed augmentation to the pointed
representable of the base scheme.
Its reduced mapping cofiber gives the pointed cone of this augmentation
from Voevodsky, *Motivic cohomology with Z/2-coefficients*, Appendix B.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- The presheaf of simplicial sets represented termwise by the Čech nerve. -/
def cechPresheaf (X : SmoothSite S) : (SmoothSite S)ᵒᵖ ⥤ SSet.{u} :=
  (SimplicialObject.termwiseYoneda (SmoothSite S)).obj (cechNerve X)

/-- The unpointed Čech augmentation to the discrete representable of the base. -/
def cechPresheafAugmentation (X : SmoothSite S) :
    cechPresheaf X ⟶ (PointedSimplicialPresheaf.simplicialYoneda (SmoothSite S)).obj (base S) :=
  (SimplicialObject.termwiseYoneda (SmoothSite S)).map (cechAugmentation X) ≫
    (SimplicialObject.constTermwiseYonedaIso (SmoothSite S)).hom.app (base S)

@[simp]
theorem cechPresheafAugmentation_app_app_apply (X : SmoothSite S) (U : (SmoothSite S)ᵒᵖ)
    (n : SimplexCategoryᵒᵖ) (g : U.unop ⟶ (cechNerve X).obj n) :
    ((cechPresheafAugmentation X).app U).app n g = g ≫ (cechAugmentation X).app n :=
  rfl

/-- The Čech presheaf with a freely adjoined basepoint. -/
def pointedCechNerve (X : SmoothSite S) : PointedSimplicialPresheaf.{u} (SmoothSite S) :=
  (PointedSimplicialPresheaf.free (SmoothSite S)).obj (cechPresheaf X)

/-- The pointed augmentation of the Čech presheaf. -/
def pointedCechAugmentation (X : SmoothSite S) :
    pointedCechNerve X ⟶ (PointedSimplicialPresheaf.yoneda (SmoothSite S)).obj (base S) :=
  (PointedSimplicialPresheaf.free (SmoothSite S)).map (cechPresheafAugmentation X)

@[simp]
theorem pointedCechAugmentation_right (X : SmoothSite S) :
    (pointedCechAugmentation X).right = coprod.map (cechPresheafAugmentation X) (𝟙 _) :=
  rfl

/-- The reduced mapping cofiber of the pointed Čech augmentation. -/
def reducedCechCofiber (X : SmoothSite S) : PointedSimplicialPresheaf.{u} (SmoothSite S) :=
  PointedSimplicialPresheaf.reducedMappingCofiber (pointedCechAugmentation X)

/-- The map from the pointed base representable to the reduced Čech cofiber. -/
def toReducedCechCofiber (X : SmoothSite S) :
    (PointedSimplicialPresheaf.yoneda (SmoothSite S)).obj (base S) ⟶ reducedCechCofiber X :=
  PointedSimplicialPresheaf.toReducedMappingCofiber (pointedCechAugmentation X)

end AlgebraicGeometry.Scheme.SmoothSite
