/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.ExtensionByZeroStalk
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Exactness of genuine scheme extension by zero

Monomorphisms are detected stalkwise. On the open image the actual adjunction unit identifies
extension followed by restriction with the identity; off the image the source stalk is zero.
Together with preservation of colimits this proves exactness without geometric finiteness.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

instance extensionByZero_preservesMonomorphisms :
    (extensionByZero j).PreservesMonomorphisms where
  preserves {M N} f hf := by
    let F := _root_.SheafOfModules.toSheaf X.ringCatSheaf
    apply F.mono_of_mono_map
    apply (TopCat.Presheaf.mono_iff_stalk_mono _).2
    intro x
    by_cases hx : x ∈ Set.range j
    · obtain ⟨y, rfl⟩ := hx
      let S := toPresheaf U ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
      have : S.PreservesMonomorphisms := by
        change (_root_.SheafOfModules.toSheaf.{u} U.ringCatSheaf ⋙
          (TopCat.Sheaf.forget AddCommGrpCat.{u} U ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y)).PreservesMonomorphisms
        have : (_root_.SheafOfModules.toSheaf.{u} U.ringCatSheaf).PreservesMonomorphisms :=
          inferInstance
        have : (TopCat.Sheaf.forget AddCommGrpCat.{u} U ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).PreservesMonomorphisms :=
          inferInstance
        infer_instance
      have : (extensionByZero j ⋙ restrictFunctor j).PreservesMonomorphisms :=
        Functor.PreservesMonomorphisms.of_iso (extensionByZeroRestrictIso j).symm
      have : ((extensionByZero j ⋙ restrictFunctor j) ⋙ S).PreservesMonomorphisms :=
        inferInstance
      have : (extensionByZero j ⋙ restrictFunctor j ⋙ S).PreservesMonomorphisms :=
        inferInstanceAs (((extensionByZero j ⋙ restrictFunctor j) ⋙ S).PreservesMonomorphisms)
      have : (extensionByZero j ⋙ (toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j y))).PreservesMonomorphisms :=
        Functor.PreservesMonomorphisms.of_iso
          (Functor.isoWhiskerLeft (extensionByZero j) (restrictStalkNatIso j y))
      exact Functor.map_mono (extensionByZero j ⋙ (toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j y))) f
    · exact mono_of_source_iso_zero _ (isZero_stalk_extensionByZero j M x hx).isoZero

instance extensionByZero_preservesHomology : (extensionByZero j).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance extensionByZero_preservesFiniteLimits : PreservesFiniteLimits (extensionByZero j) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

end AlgebraicGeometry.Scheme.Modules
