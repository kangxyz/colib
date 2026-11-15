/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-! # Cartesian monoidal structure on the smooth site -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- The original base object is terminal, with the original structure maps. -/
def baseIsTerminal (S : Scheme.{u}) : IsTerminal (base S) :=
  IsTerminal.ofUniqueHom Contraction.toBase (fun _ f =>
    MorphismProperty.Over.Hom.ext
      ((Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f)))

/-- The cartesian tensor is the literal relative scheme product. -/
instance (S : Scheme.{u}) : CartesianMonoidalCategory (SmoothSite S) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    ⟨_, baseIsTerminal S⟩ (fun X Y => ⟨_, productIsLimit X Y⟩)

/-- The tensor on scheme maps is the literal product map. -/
theorem tensorHom_eq_productMap {X X' Y Y' : SmoothSite S} (f : X ⟶ X') (g : Y ⟶ Y') :
    f ⊗ₘ g = productMap f g := by
  apply product_hom_ext
  · rw [productMap_fst]
    change (f ⊗ₘ g) ≫ SemiCartesianMonoidalCategory.fst X' Y' =
      SemiCartesianMonoidalCategory.fst X Y ≫ f
    exact CartesianMonoidalCategory.tensorHom_fst f g
  · rw [productMap_snd]
    change (f ⊗ₘ g) ≫ SemiCartesianMonoidalCategory.snd X' Y' =
      SemiCartesianMonoidalCategory.snd X Y ≫ g
    exact CartesianMonoidalCategory.tensorHom_snd f g

end AlgebraicGeometry.Scheme.SmoothSite
