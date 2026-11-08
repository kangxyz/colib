/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineChartStalkModules
public import Colib.Algebra.Category.ModuleCat.TensorProductChangeOfRings

/-!
# Actual closed-source stalks with tensor-product coordinate rings

For a closed immersion whose actual affine coordinate square is the tensor-ring
left inclusion, the actual source stalk module is the original algebra module
extended along the composite map to the ambient coordinate localization. This
composes the actual chart-stalk comparison with native scalar-extension
associativity. No module comparison, flatness or reduced structure is assumed.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/Aglib/AlgebraicGeometry/Intersection/AffineMiddleTor.lean` and
`Motivic/Aglib/Algebra/Category/ModuleCat/Tor/SupportModulesAlgebra.lean`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {R S T : Type u}
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

local instance affineTensorStalkAtPrimeRing
    (p : Ideal S) [p.IsPrime] : Ring (Localization.AtPrime p) :=
  (inferInstance : CommRing (Localization.AtPrime p)).toRing

/-- The actual closed-source stalk with tensor coordinates is the composed scalar extension. -/
def closedImmersionTensorStalkModuleIsoOfAffineChartOfEq
    (j : Y ⟶ X) [IsClosedImmersion j]
    (eX : X ≅ Spec (.of S)) (eY : Y ≅ Spec (.of (S ⊗[R] T)))
    (h : j ≫ eX.hom = eY.hom ≫ Spec.map
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T)))
    (y : Y) (x : X) (hx : x = j y) :
    (ModuleCat.restrictScalars
      ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ j.stalkMap y).hom).obj
      (ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y)) ≅
    (ModuleCat.restrictScalars (R := X.presheaf.stalk x)
      (S := Localization.AtPrime (eX.hom x).asIdeal)
      (stalkIsoOfAffineChart eX x).hom.hom).obj
      ((ModuleCat.extendScalars (R := R) (S := Localization.AtPrime (eX.hom x).asIdeal)
        ((algebraMap S (Localization.AtPrime (eX.hom x).asIdeal)).comp (algebraMap R S))).obj
        (ModuleCat.of R T)) :=
  closedImmersionStalkModuleIsoOfAffineChartOfEq j eX eY
    Algebra.TensorProduct.includeLeftRingHom h y x hx ≪≫
    (ModuleCat.restrictScalars (R := X.presheaf.stalk x)
      (S := Localization.AtPrime (eX.hom x).asIdeal)
      (stalkIsoOfAffineChart eX x).hom.hom).mapIso
      (ModuleCat.extendScalarsTensorProductCompIso (R := R) (S := S) (T := T)
        (V := Localization.AtPrime (eX.hom x).asIdeal)
        (algebraMap S (Localization.AtPrime (eX.hom x).asIdeal)))

end AlgebraicGeometry.Scheme
