module

import Colib.AlgebraicGeometry.Intersection.AffineChartStalkModules

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]

example (j : Y ⟶ X) (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S))
    (f : R →+* S) (hf : Function.Surjective f)
    (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f))
    (y : Y) (x : X) (hx : x = j y) :
    (ModuleCat.restrictScalars
      ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ j.stalkMap y).hom).obj
      (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)) ≅
    (ModuleCat.restrictScalars (Scheme.stalkIsoOfAffineChart eX x).hom.hom).obj
      ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))) :=
  Scheme.closedStalkModuleIsoOfAffineChartOfEq j eX eY f hf h y x hx

example (j : Y ⟶ X) (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S))
    (f : R →+* S) (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f))
    (y : Y) : eX.hom (j y) = (eY.hom y).comap f :=
  Scheme.affineChart_point_comap j eX eY f h y

example (j : Y ⟶ X) [IsClosedImmersion j]
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S))
    (f : R →+* S) (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f)) :
    Function.Surjective f :=
  Scheme.surjective_affineChartMap_of_isClosedImmersion j eX eY f h

example (j : Y ⟶ X) [IsClosedImmersion j]
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S))
    (f : R →+* S) (h : j ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f))
    (y : Y) (x : X) (hx : x = j y) :
    (ModuleCat.restrictScalars
      ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ j.stalkMap y).hom).obj
      (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)) ≅
    (ModuleCat.restrictScalars (Scheme.stalkIsoOfAffineChart eX x).hom.hom).obj
      ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))) :=
  Scheme.closedImmersionStalkModuleIsoOfAffineChartOfEq j eX eY f h y x hx
