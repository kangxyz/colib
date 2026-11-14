/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Cech
public import Colib.CategoryTheory.Sites.Simplicial.MappingCofiber
public import Colib.Util.References

/-!
# Reduced Čech cofibers

Freely pointing the native Čech augmentation gives a pointed map. Its reduced
mapping cofiber is formed by the existing strict cone and pushout construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (S : Scheme.{u}) {X Y : SmoothSite S} (f : X ⟶ Y)

/-- The Čech augmentation after adjoining a disjoint basepoint. -/
def pointedCechAugmentation :
    (free (SmoothSite S)).obj (cechSimplicialPresheaf S f) ⟶
      (free (SmoothSite S)).obj (cechBasePresheaf S Y) :=
  (free (SmoothSite S)).map (cechAugmentation S f)

/-- The freely pointed represented base is the freely pointed terminal presheaf. -/
def pointedCechBaseIso :
    (free (SmoothSite S)).obj (cechBasePresheaf S (SmoothSite.base S)) ≅
      (free (SmoothSite S)).obj (⊤_ ((SmoothSite S)ᵒᵖ ⥤ SSet.{u + 1})) :=
  (free (SmoothSite S)).mapIso (cechBaseIsoPoint S)

/-- The reduced mapping cofiber of the freely pointed Čech augmentation. -/
def reducedCechCofiber : PointedSimplicialPresheaf.{u + 1} (SmoothSite S) :=
  reducedMappingCofiber (pointedCechAugmentation S f)

/-- The reduced Čech cofiber of a smooth scheme over the base, using its
actual structure map. -/
def reducedCechCofiberOverBase (X : SmoothSite S) :
    PointedSimplicialPresheaf.{u + 1} (SmoothSite S) :=
  reducedCechCofiber S (SmoothSite.Contraction.toBase X)

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-1231"]
  AlgebraicGeometry.MotivicHomotopy.cechSimplicialPresheaf
  AlgebraicGeometry.MotivicHomotopy.cechAugmentation
  AlgebraicGeometry.MotivicHomotopy.cechContraction
  AlgebraicGeometry.MotivicHomotopy.pointedCechBaseIso
  AlgebraicGeometry.MotivicHomotopy.reducedCechCofiberOverBase

attribute [colib_ref "Voevodsky2003ModTwo" "Section 9, opening construction, pp. 101–102"
  "adaptation" "The augmented Čech nerve and its pointed cofiber over the base"]
  AlgebraicGeometry.MotivicHomotopy.reducedCechCofiberOverBase
