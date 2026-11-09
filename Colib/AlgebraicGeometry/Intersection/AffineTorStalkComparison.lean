/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineChartStalkModules
public import Mathlib.RingTheory.Length
public import StacksFrontier.Homology.Tor.Independence

/-!
# Tor of actual closed-source stalks in affine coordinates

The input squares are literal scheme-coordinate squares, not assumed module or
Tor comparisons. The actual stalk maps and transport between equal ambient
points determine the two source modules. Native stalk comparisons identify them
with localized coordinate quotient modules. Native `Tor` functoriality and
`RingTheory.TorIndependence.torRestrictIso` then transport Tor over the actual
ambient stalk to the actual coordinate localization.

Both sources are actual closed immersions. Surjectivity of their coordinate
maps is derived by the preceding native affine-chart module interface.
No reduced-support replacement, support flatness or finite length is assumed.
The first and second source arguments remain in their specified order.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/Aglib/AlgebraicGeometry/Intersection/AffineClosedSupportTor.lean`.
This supplies coordinate transport; it is not the global Tor-cycle formula.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}} {R S T : Type u}
  [CommRing R] [CommRing S] [CommRing T]

/-- The ring structure on a prime localization, projected from its commutative ring. -/
local instance affineTorStalkAtPrimeRing (p : Ideal R) [p.IsPrime] :
    Ring (Localization.AtPrime p) :=
  (inferInstance : CommRing (Localization.AtPrime p)).toRing

/-- Tor of the two actual stalk modules is coordinate Tor with its actual ambient action. -/
def torClosedStalksIsoOfAffineCharts
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
  let a := closedImmersionStalkModuleIsoOfAffineChartOfEq i eX eY f hi y x hy
  let b := closedImmersionStalkModuleIsoOfAffineChartOfEq j eX eZ g hj z x hz
  exact (((Tor (ModuleCat (X.presheaf.stalk x)) n).mapIso a).app _) ≪≫
    ((Tor (ModuleCat (X.presheaf.stalk x)) n).obj _).mapIso b ≪≫
    RingTheory.TorIndependence.torRestrictIso
      (stalkIsoOfAffineChart eX x).commRingCatIsoToRingEquiv _ _ n

/-- The actual stalk Tor length equals the coordinate Tor length, including infinite length. -/
theorem length_torClosedStalks_eq_of_affineCharts
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
  have h₁ := (torClosedStalksIsoOfAffineCharts i j eX eY eZ f g hi hj
    x y z hy hz n).toLinearEquiv.length_eq
  let M := ((Tor (ModuleCat (Localization.AtPrime (eX.hom x).asIdeal)) n).obj
    ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))).obj
    ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (eX.hom x).asIdeal))).obj
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T)))
  let a := (stalkIsoOfAffineChart eX x).hom.hom
  let := a.toAlgebra
  let : IsScalarTower (X.presheaf.stalk x) (Localization.AtPrime (eX.hom x).asIdeal)
      ((ModuleCat.restrictScalars a).obj M) := ⟨fun r s m ↦ by
    change (a r * s) • m = a r • (s • m)
    exact mul_smul (a r) s m⟩
  have h₂ := Module.length_eq_of_surjective
    (R := Localization.AtPrime (eX.hom x).asIdeal)
    (M := (ModuleCat.restrictScalars a).obj M)
    (stalkIsoOfAffineChart eX x).commRingCatIsoToRingEquiv.surjective
  exact h₁.trans h₂

end AlgebraicGeometry.Scheme
