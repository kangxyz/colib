/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.GrothendieckComparison.ExtensionCocycle
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveZeroFiberEntry

/-!
# The original Q-cocycle on localized projective extensions

The potential is the kernel class minus the actual projective denominator.
The unchanged projection to Q has weight equal to source potential minus
target potential. On identity-extension entries this potential is exactly the
existing numerator-minus-denominator completion grade, without any rank or
invariant-basis-number assumption.
-/

open CategoryTheory

/-! Implementation source: `Quillen/KTheory/Plus/ProjectiveExtensionCocycle.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
  extensionDirectSumAction

/-- Kernel minus denominator is the potential for the unchanged quotient projection. -/
def localizedExtensionPotential (x : LocalizedExtensionCategory R) :
    (exactStructure R).GrothendieckGroup :=
  (exactStructure R).extensionKernelClass x.obj.2 - coreClass R x.obj.1

/-- The original identity-extension entry has exactly the preexisting completion grade. -/
@[simp] theorem localizedExtensionPotential_completionIdentityEntry
    (U : GroupCompletionCategory R) :
    localizedExtensionPotential R ((completionIdentityEntry R).obj U) = completionGrade R U := rfl

/-- The original Q-projection has source-minus-target potential on every actual quotient arrow. -/
theorem qGrothendieckWeight_localizedExtensionProjection
    {x y : LocalizedExtensionCategory R} (f : x ⟶ y) :
    (exactStructure R).qGrothendieckWeight ((localizedExtensionProjection R).map f) =
      localizedExtensionPotential R x - localizedExtensionPotential R y := by
  obtain ⟨h, rfl⟩ := GroupCompletion.ActionLocalization.mkHom_surjective x.obj y.obj f
  change (exactStructure R).qGrothendieckWeight
    ((localizedExtensionProjection R).map
      (GroupCompletion.Localization.mkHom h.denom h.map.1 h.map.2)) = _
  rw [localizedExtensionProjection_map_mkHom,
    CategoryTheory.ExactCategory.ExactStructure.qGrothendieckWeight_comp]
  have hi : (exactStructure R).qGrothendieckWeight
      ((exactStructure R).qIsoOfIso
        (directSumExtensionQuotientIso R h.denom x.obj.2)).inv = 0 := by
    change (exactStructure R).grothendieckClass _ -
      (exactStructure R).grothendieckClass _ = 0
    exact sub_self _
  rw [hi, zero_add,
    CategoryTheory.ExactCategory.ExactStructure.qGrothendieckWeight_extensionProjection]
  have hd := (exactStructure R).grothendieckClass_iso h.map.1.iso
  change coreClass R (h.denom ⊗ x.obj.1) = coreClass R y.obj.1 at hd
  rw [coreClass_tensor] at hd
  have hk : (exactStructure R).extensionKernelClass (directSumExtensionObject R h.denom x.obj.2) =
      coreClass R h.denom + (exactStructure R).extensionKernelClass x.obj.2 :=
    coreClass_tensor R h.denom ⟨x.obj.2.fiber.unop.left.obj⟩
  rw [hk]
  dsimp only [localizedExtensionPotential]
  rw [← hd]
  abel

end ModuleCat.FiniteProjective
