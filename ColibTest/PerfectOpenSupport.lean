/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport

/-! Regression clients: literal maps/classes and existing canonical K-map. -/
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Waldhausen Fibration
noncomputable section
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
example {K L : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))} (f : K ⟶ L) :
    (perfectOpenWeakWaldhausen j).cof f ↔ Mono f.hom := Iff.rfl
example {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (perfectSupportedWaldhausen j).cof f ↔ Mono f.hom := Iff.rfl
example {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (perfectSupportedWaldhausen j).weq f ↔ QuasiIso f.hom := Iff.rfl
example {K L : AcyclicCategory (perfectOpenNested j)} (f : K ⟶ L) :
    ((perfectAcyclicToSupported j).map f).hom = f.hom.hom := rfl
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
example : perfectAcyclicToSupported j ⋙ perfectSupportedInclusion j =
    acyclicInclusion (perfectOpenNested j) := rfl
example : perfectSupportedToAcyclic j ⋙ acyclicInclusion (perfectOpenNested j) =
    perfectSupportedInclusion j := rfl
example (n : ℕ) :
    (perfectOpenKRestrict j n).comp (perfectOpenKMap j n) =
      KMap (perfectComplexesRestrictOpenImmersion_isExact j) n :=
  perfectOpenKRestrict_comp_perfectOpenKMap j n
example (n : ℕ) :
    (perfectSupportedKMap j n).comp (perfectAcyclicSupportedKEquiv j n).toMonoidHom =
      KMap (acyclicInclusion_exact (perfectOpenNested j)) n :=
  perfectAcyclicSupportedKEquiv_inclusion j n

example (X : Scheme.{u}) (U : X.Opens) :
    perfectComplexesRestrictOpenImmersion U.ι = perfectComplexesRestrictFunctor X U :=
  perfectComplexesRestrictOpenImmersion_opens X U
example (X : Scheme.{u}) (U : X.Opens) (n : ℕ) :
    (perfectOpenKRestrict U.ι n).comp (perfectOpenKMap U.ι n) =
      perfectComplexesRestrictKMap X U n :=
  perfectOpenKRestrict_comp_perfectOpenKMap_opens X U n
