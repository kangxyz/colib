/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenWeak
public import Colib.CategoryTheory.Waldhausen.Fibration.CofibrationClosedExtension
public import Colib.CategoryTheory.Waldhausen.Fibration.ComplexExtension

/-!
# The native perfect open-weak extension axiom

The proof descends from actual quasi-isomorphism extension on complexes, first through
the native full inclusion and then through actual open restriction. No extension axiom
is assumed for the scheme application.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace

universe u

/-- The original fine perfect-complex structure satisfies extension. -/
theorem perfectComplexes_extensionAxiom (X : RingedSpace.{u, u}) :
    Waldhausen.Fibration.ExtensionAxiom (perfectComplexesWaldhausen X) :=
  Waldhausen.CofibrationClosedSubcategory.extensionAxiom _ _
    (perfectComplexes_cofibrationClosed X) Waldhausen.Fibration.complexes_extensionAxiom

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Open-detected weak equivalences satisfy the actual structural extension axiom. -/
theorem perfectOpenWeak_extensionAxiom {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    Waldhausen.Fibration.ExtensionAxiom (perfectOpenWeakWaldhausen j) :=
  Waldhausen.Structure.withInverseImageWeak_extensionAxiom
    (perfectComplexesRestrictOpenImmersion_isExact j)
    (RingedSpace.perfectComplexes_extensionAxiom Y.toRingedSpace)

end AlgebraicGeometry.Scheme.Modules
