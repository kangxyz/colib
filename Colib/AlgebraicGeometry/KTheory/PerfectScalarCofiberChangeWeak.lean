/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberPrism
public import Colib.KTheory.Waldhausen.Fibration.CofiberObjectChangeWeak

/-!
# The original fine scalar-cofiber triangle and its localization image

The actual fine quotient triangle gives a specified track from the source-plus-cofiber object
loop to the original middle object loop. Its image under the unchanged localization map is
exactly the cofiber-prism face already used in the boundary calculation, with both parameters
retained. No scalar invertibility on the original scheme is required.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberChangeWeak.lean:35-80`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native perfect complexes retain
ambient monomorphism cofibrations, quasi-isomorphisms, and the actual signed cone.
The original maps, path coordinates, basepoints, and signs are unchanged. -/

@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology HomotopyGroup
open CategoryTheory.Waldhausen.Fibration
open scoped Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original scalar factor has its genuine quotient square in the fine structure. -/
theorem perfectScalarCofiber_fine_isPushout (X : Scheme.{u}) (r : Γ(X, ⊤)) (K :
  ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    IsPushout (perfectScalarInclusion X r K) (0 : K ⟶ (RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace).zero)
      ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
        (perfectScalarExtension X r K))
      (0 : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).zero ⟶
        (ExtensionCategory.cofiber (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
          (perfectScalarExtension X r K)) := by
  have h := ExtensionCategory.cofiber_isPushout (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace)
    (perfectScalarExtension X r K)
  convert h using 1 <;> first
    | rfl
    | exact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).isZero.eq_of_tgt _ _
    | exact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).isZero.eq_of_src _ _

/-- The specified fine triangle track uses the original categorical cofiber and middle objects. -/
def perfectScalarCofiberObjectTrack (X : Scheme.{u}) (r : Γ(X, ⊤)) (K :
  ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    Path.Homotopy (((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop
      K).trans
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop
        ((ExtensionCategory.cofiber (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
          (perfectScalarExtension X r K))))
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop
        ((ExtensionCategory.middle (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
          (perfectScalarExtension X r K))) :=
  (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cofiberObjectLoopTrack
    (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
      (perfectScalarExtension X r K))
    (ExtensionCategory.inclusion_cof (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
      (perfectScalarExtension X r K))
    (perfectScalarCofiber_fine_isPushout X r K)

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))

/-- The original localization map preserves the entire actual fine cofiber track. -/
theorem perfectScalarCofiberObjectTrack_changeWeak (a t : unitInterval) :
    changeWeakMap (perfectOpenNested j) (perfectScalarCofiberObjectTrack X r K (a, t)) =
      (perfectOpenNested j).coarse.cofiberObjectLoopTrack (perfectScalarInclusion X r K)
        ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
          (perfectScalarExtension X r K))
        (perfectScalarInclusion_openCof r j K) (perfectScalarCofiber_isPushout r j K) (a, t) :=
  cofiberObjectLoopTrack_changeWeak (perfectOpenNested j) (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
      (perfectScalarExtension X r K))
    (ExtensionCategory.inclusion_cof (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
      (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof r j K) (perfectScalarCofiber_fine_isPushout X r K)
    (perfectScalarCofiber_isPushout r j K) a t

/-- The exact nerve-one face of the original scalar prism is this same fine-track image. -/
theorem perfectScalarCofiberObjectTrack_prism_face (a t : unitInterval) :
    changeWeakMap (perfectOpenNested j) (perfectScalarCofiberObjectTrack X r K (a, t)) =
      perfectOpenScalarCofiberCompositionCube j r q hq K (a, 1, t) := by
  rw [perfectScalarCofiberObjectTrack_changeWeak]
  unfold perfectOpenScalarCofiberCompositionCube
  rw [Structure.cofiberPrismCompositionCube_nerve_one]

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberChangeWeak.lean:35-80" "adaptation"
  "The genuine fine scalar triangle and its full unchanged image in the coarse cofiber prism"]
  perfectScalarCofiberObjectTrack_prism_face

end AlgebraicGeometry.Scheme.Modules
