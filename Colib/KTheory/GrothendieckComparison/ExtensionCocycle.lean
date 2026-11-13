/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.KTheory.GrothendieckGroup.QCocycle
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionFunctor

/-!
# The original Q-cocycle on total extensions

An extension morphism shrinks the kernel and enlarges the middle object. The
Grothendieck weight of its unchanged Q-projection is the source kernel class
minus the target kernel class. This sign is forced by the original quotient
span and the original definition of the Q-cocycle.
-/

open CategoryTheory

/-! Implementation source: `Quillen/KTheory/GrothendieckComparison/ExtensionCocycle.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
open CategoryTheory
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The actual kernel object's class, before taking the extension quotient. -/
def extensionKernelClass (x : E.ExtensionTotal) : E.GrothendieckGroup :=
  E.grothendieckClass x.fiber.unop.left.obj

/-- The original Q-projection has source-minus-target kernel weight. -/
theorem qGrothendieckWeight_extensionProjection {x y : E.ExtensionTotal} (f : x ⟶ y) :
    E.qGrothendieckWeight (E.extensionProjectionQMap f) =
      E.extensionKernelClass x - E.extensionKernelClass y := by
  let q := E.extensionProjectionCokernel f
  have hj : E.inflation ((Subdivision.domainMap f).hom ≫ x.fiber.unop.hom.hom) :=
    E.inflation.comp_mem _ _ (Subdivision.domainMap f).property x.fiber.unop.hom.property
  have ha := E.grothendieckClass_additive
    (E.conflation_of_inflation_of_isCokernel
      (S := ShortComplex.mk _ q.π q.zero) hj q.isColimit)
  have hx := E.grothendieckClass_additive (E.extensionQuotientData x).conflation
  change E.grothendieckClass x.base.obj =
    E.grothendieckClass y.fiber.unop.left.obj +
      E.grothendieckClass (E.extensionProjectionSpan f).apex at ha
  change E.grothendieckClass x.base.obj =
    E.grothendieckClass x.fiber.unop.left.obj +
      E.grothendieckClass (E.extensionProjectionObject x) at hx
  change E.grothendieckClass (E.extensionProjectionSpan f).apex -
    E.grothendieckClass (E.extensionProjectionObject x) = _
  dsimp only [extensionKernelClass]
  apply sub_eq_sub_iff_add_eq_add.mpr
  calc
    _ = E.grothendieckClass x.base.obj := by simpa [add_comm] using ha.symm
    _ = _ := hx

end CategoryTheory.ExactCategory.ExactStructure
