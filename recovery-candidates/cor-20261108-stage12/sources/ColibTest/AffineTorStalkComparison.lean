module

import Colib.AlgebraicGeometry.Intersection.AffineTorStalkComparison

/-!
Fresh recovery regression tests for the restored generic actual-stalk comparison.
The original historical test file was not retained. These are new source-only
candidates, not a reconstruction of that original file and not yet compiled.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}} {R S T : Type u}
  [CommRing R] [CommRing S] [CommRing T]

local instance affineTorRecoveryTestAtPrimeRing
    (p : Ideal R) [p.IsPrime] : Ring (Localization.AtPrime p) :=
  (inferInstance : CommRing (Localization.AtPrime p)).toRing

example
    (i : Y ⟶ X) (j : Z ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (eX : X ≅ Spec (.of R))
    (eY : Y ≅ Spec (.of S)) (eZ : Z ≅ Spec (.of T))
    (f : R →+* S) (g : R →+* T)
    (hi : i ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f))
    (hj : j ≫ eX.hom = eZ.hom ≫ Spec.map (CommRingCat.ofHom g))
    (x : X) (y : Y) (z : Z) (hy : x = i y) (hz : x = j z) (n : ℕ) :
    (((Tor (ModuleCat (X.presheaf.stalk x)) n).obj
      ((ModuleCat.restrictScalars
        ((X.presheaf.stalkCongr (.of_eq hy)).hom ≫ i.stalkMap y).hom).obj
        (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)))).obj
      ((ModuleCat.restrictScalars
        ((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ j.stalkMap z).hom).obj
        (ModuleCat.of (Z.presheaf.stalk z) (Z.presheaf.stalk z)))) ≅
    (ModuleCat.restrictScalars (stalkIsoOfAffineChart eX x).hom.hom).obj
      (((Tor (ModuleCat (Localization.AtPrime (eX.hom x).asIdeal)) n).obj
        ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))).obj
        ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
          ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T)))) := by
  exact torClosedStalksIsoOfAffineCharts i j eX eY eZ f g hi hj x y z hy hz n

example
    (i : Y ⟶ X) (j : Z ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (eX : X ≅ Spec (.of R))
    (eY : Y ≅ Spec (.of S)) (eZ : Z ≅ Spec (.of T))
    (f : R →+* S) (g : R →+* T)
    (hi : i ≫ eX.hom = eY.hom ≫ Spec.map (CommRingCat.ofHom f))
    (hj : j ≫ eX.hom = eZ.hom ≫ Spec.map (CommRingCat.ofHom g))
    (x : X) (y : Y) (z : Z) (hy : x = i y) (hz : x = j z) (n : ℕ) :
    Module.length (X.presheaf.stalk x)
      (((Tor (ModuleCat (X.presheaf.stalk x)) n).obj
        ((ModuleCat.restrictScalars
          ((X.presheaf.stalkCongr (.of_eq hy)).hom ≫ i.stalkMap y).hom).obj
          (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)))).obj
        ((ModuleCat.restrictScalars
          ((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ j.stalkMap z).hom).obj
          (ModuleCat.of (Z.presheaf.stalk z) (Z.presheaf.stalk z)))) =
    Module.length (Localization.AtPrime (eX.hom x).asIdeal)
      (((Tor (ModuleCat (Localization.AtPrime (eX.hom x).asIdeal)) n).obj
        ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))).obj
        ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
          ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T)))) := by
  exact length_torClosedStalks_eq_of_affineCharts i j eX eY eZ f g hi hj x y z hy hz n

end AlgebraicGeometry.Scheme
