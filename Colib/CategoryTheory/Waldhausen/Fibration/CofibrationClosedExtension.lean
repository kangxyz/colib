/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeak

/-!
# Extension in a native cofibration-closed full subcategory

The weak class is already the inverse image under the actual full inclusion.
The inverse-image extension theorem applies without changing the native structure
or requiring strict preservation of a chosen zero.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Waldhausen.CofibrationClosedSubcategory

universe u v

variable {C : Type u} [Category.{v} C] (W : Structure C) (P : ObjectProperty C)
  (H : Closed W P)

/-- An actual cofibration-closed full subcategory inherits the structural extension axiom. -/
theorem extensionAxiom (hW : Fibration.ExtensionAxiom W) :
    Fibration.ExtensionAxiom (waldhausenStructure W P H) :=
  Structure.withInverseImageWeak_extensionAxiom (inclusion_exact W P H) hW

end CategoryTheory.Waldhausen.CofibrationClosedSubcategory
