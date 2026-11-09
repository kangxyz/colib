/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Extension by zero of modules along an open immersion

For an arbitrary open immersion of schemes, extension by zero is the left adjoint to
Mathlib's actual `Scheme.Modules.restrictFunctor`. Its construction is the module-sheaf
pullback along the image functor on open sets, with scalars transported by the inverse
of the open immersion's section isomorphisms. In particular, it does not require replacing
the source scheme by a chosen open subscheme.

The adjoint triple with restriction and direct image proves full faithfulness. This is
the scheme specialization of the construction in Stacks Project, Tag 00AB.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

set_option backward.defeqAttrib.useBackward true in
/-- The inverse section isomorphisms, viewed as a morphism of sheaves of rings on `U`. -/
noncomputable def extensionByZeroRingHom :
    U.ringCatSheaf ⟶
      (j.opensFunctor.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology U)
        (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  let α : U.presheaf ⟶ j.opensFunctor.op ⋙ X.presheaf :=
    { app V := (j.appIso V.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/-- The underlying presheaf restriction admits a left adjoint. -/
instance extensionByZeroPresheafPushforward_isRightAdjoint :
    (PresheafOfModules.pushforward.{u} (F := j.opensFunctor)
      (extensionByZeroRingHom j).hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward (extensionByZeroRingHom j).hom

/-- The module-sheaf restriction admits a left adjoint. -/
instance extensionByZeroSheafPushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (F := j.opensFunctor)
      (extensionByZeroRingHom j)).IsRightAdjoint :=
  SheafOfModules.instIsRightAdjointPushforward (extensionByZeroRingHom j)

/-- Restriction along an open immersion admits the extension-by-zero left adjoint. -/
instance restrictFunctor_isRightAdjoint : (restrictFunctor j).IsRightAdjoint :=
  extensionByZeroSheafPushforward_isRightAdjoint j

/-- Extension by zero of module sheaves along an arbitrary open immersion. -/
noncomputable def extensionByZero : U.Modules ⥤ X.Modules :=
  SheafOfModules.pullback (F := j.opensFunctor) (extensionByZeroRingHom j)

/-- Extension by zero is left adjoint to the actual open-restriction functor. -/
noncomputable def extensionByZeroRestrictAdjunction :
    extensionByZero j ⊣ restrictFunctor j :=
  SheafOfModules.pullbackPushforwardAdjunction (F := j.opensFunctor) (extensionByZeroRingHom j)

instance : (extensionByZero j).IsLeftAdjoint :=
  (extensionByZeroRestrictAdjunction j).isLeftAdjoint

/-- The adjoint triple of extension by zero, restriction, and direct image. -/
noncomputable def extensionByZeroAdjointTriple :
    Adjunction.Triple (extensionByZero j) (restrictFunctor j) (pushforward j) :=
  ⟨extensionByZeroRestrictAdjunction j, restrictAdjunction j⟩

instance extensionByZeroRestrictAdjunction_unit_isIso :
    IsIso (extensionByZeroRestrictAdjunction j).unit := by
  rw [show extensionByZeroRestrictAdjunction j =
    (extensionByZeroAdjointTriple j).adj₁ from rfl,
    (extensionByZeroAdjointTriple j).isIso_unit_iff_isIso_counit]
  exact inferInstanceAs (IsIso (restrictAdjunction j).counit)

/-- Restricting extension by zero recovers the original module sheaf. -/
noncomputable def extensionByZeroRestrictIso :
    extensionByZero j ⋙ restrictFunctor j ≅ 𝟭 U.Modules :=
  (asIso (extensionByZeroRestrictAdjunction j).unit).symm

/-- Extension by zero is fully faithful. -/
noncomputable def extensionByZeroFullyFaithful : (extensionByZero j).FullyFaithful :=
  (extensionByZeroRestrictAdjunction j).fullyFaithfulLOfIsIsoUnit

instance : (extensionByZero j).Full := (extensionByZeroFullyFaithful j).full
instance : (extensionByZero j).Faithful := (extensionByZeroFullyFaithful j).faithful

instance : PreservesColimitsOfSize.{v, w} (extensionByZero j) :=
  (extensionByZeroRestrictAdjunction j).leftAdjoint_preservesColimits

instance : (extensionByZero j).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (extensionByZero j)
  exact Functor.additive_of_preservesBinaryBiproducts _

instance restrict_extensionByZero_counit_isIso (M : X.Modules) :
    IsIso ((restrictFunctor j).map ((extensionByZeroRestrictAdjunction j).counit.app M)) :=
  isIso_of_hom_comp_eq_id _
    ((extensionByZeroRestrictAdjunction j).right_triangle_components M)

end AlgebraicGeometry.Scheme.Modules
