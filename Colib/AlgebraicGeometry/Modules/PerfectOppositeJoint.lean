/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectExactFunctor
public import Colib.AlgebraicGeometry.Modules.PerfectKernel
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJoint

/-! # Actual opposite joint data on native perfect complexes

The literal opposite of the native perfect-complex category has admissible
epimorphism cofibrations. Kernel perfectness follows from the native distinguished
triangle of the actual short exact sequence. Hence these admissible maps are
exactly ambient epimorphisms, without an assumption about resolutions or the space.

The common opposite complex cylinder supplies actual joint data. Compatibility
refers to the original ambient-monomorphism Waldhausen structure, not an alternate
model of perfect objects.

Implementation provenance: the perfect-complex part of
`Quillen/AlgebraicGeometry/PerfectComplexes/OppositeJointData.lean:45-74` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Stacks
perfectness on the unchanged cochain complexes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry StrictlyPerfect
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.RingedSpace
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
variable (X : RingedSpace.{u, u})

local instance : HasFiniteBiproducts (CochainComplex (OXMod.{u, u, u} X) ℤ) :=
  Abelian.hasFiniteBiproducts (C := CochainComplex (OXMod.{u, u, u} X) ℤ)

local instance : HasFiniteBiproducts
    (ObjectProperty.FullSubcategory (IsPerfectComplex (X := X))) := by
  let := isPerfectComplex_closedUnderFiniteProducts X
  exact ExactSubcategory.subcategoryHasFiniteBiproducts (IsPerfectComplex (X := X))

/-- An ambient epimorphism between perfect complexes has a perfect actual kernel. -/
theorem perfectComplexes_deflation_iff
    {K L : ObjectProperty.FullSubcategory (IsPerfectComplex (X := X))} (f : K ⟶ L) :
    (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex (OXMod.{u, u, u} X) ℤ))
      (IsPerfectComplex (X := X))).deflation f ↔ Epi f.hom := by
  constructor
  · rintro ⟨Q, i, w, hS⟩
    exact hS.epi_g
  · intro hf
    let : Epi f.hom := hf
    let S := ShortComplex.mk (kernel.ι f.hom) f.hom (kernel.condition f.hom)
    have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact f.hom }
    exact ⟨⟨kernel f.hom, isPerfectComplex_X₁_of_shortExact X hS K.property L.property⟩,
      ObjectProperty.homMk (kernel.ι f.hom),
      ObjectProperty.hom_ext _ (kernel.condition f.hom), hS⟩

/-- The Waldhausen structure on the literal opposite of the actual perfect category. -/
def perfectComplexesOppositeWaldhausen :
    Waldhausen.Structure (ObjectProperty.FullSubcategory (IsPerfectComplex (X := X)))ᵒᵖ :=
  Waldhausen.oppositeComplexSubcategory (IsPerfectComplex (X := X))

/-- Opposite cofibrations are exactly epimorphisms of the underlying actual complexes. -/
theorem perfectComplexesOppositeWaldhausen_cof_iff
    {K L : (ObjectProperty.FullSubcategory (IsPerfectComplex (X := X)))ᵒᵖ} (f : K ⟶ L) :
    (perfectComplexesOppositeWaldhausen X).cof f ↔ Epi f.unop.hom :=
  perfectComplexes_deflation_iff X f.unop

/-- Compatibility retains the original perfect structure and its ambient monomorphisms. -/
theorem perfectComplexesOppositeWaldhausen_compatible :
    Waldhausen.IsCompatibleDual (perfectComplexesWaldhausen X)
      (perfectComplexesOppositeWaldhausen X) := by
  apply Waldhausen.exactDualStructure_compatible
    (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex (OXMod.{u, u, u} X) ℤ))
      (IsPerfectComplex (X := X)))
    (perfectComplexesWaldhausen X)
    (Waldhausen.complexSubcategoryPullbackGluing (IsPerfectComplex (X := X)))
  funext K L f
  exact propext (perfectComplexes_inflation_iff X f).symm

/-- Actual opposite joint data obtained from the unchanged ambient complex cylinder. -/
def perfectComplexesOppositeJointData : Waldhausen.Fibration.RowFactorization.JointData
    (Waldhausen.Fibration.NestedWeakEquivalences.refl (perfectComplexesOppositeWaldhausen X)) :=
  Waldhausen.oppositeComplexJointData (IsPerfectComplex (X := X))
    (fun _ h => isPerfectComplex_shift X h (-1))

end AlgebraicGeometry.RingedSpace

attribute [colib_tag "COL-0311",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/OppositeJointData.lean:45-74"
    "adaptation" "Literal native perfect-complex opposite structure and actual joint data; \
    no strict-to-perfect instance is claimed"]
  AlgebraicGeometry.RingedSpace.perfectComplexesOppositeWaldhausen
  AlgebraicGeometry.RingedSpace.perfectComplexesOppositeWaldhausen_compatible
  AlgebraicGeometry.RingedSpace.perfectComplexesOppositeJointData
