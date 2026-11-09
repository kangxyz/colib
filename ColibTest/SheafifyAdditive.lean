/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Sites.SheafifyAdditive

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (J : GrothendieckTopology C)
  (hJ : ∀ (X : C) (S : Sieve X), S ∈ J X →
    ∃ (Y : C) (q : Y ⟶ X), S q ∧ Sieve.generate (Presieve.singleton q) ∈ J X)

example {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [F.Additive] (η : F ⟶ G)
    [Presheaf.IsLocallySurjective J η] (hG : Presheaf.IsSeparated J G) : G.Additive :=
  Presheaf.additive_of_isLocallySurjective_of_isSeparated J hJ η hG

example [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
    [J.PreservesSheafification (forget AddCommGrpCat.{max u v})]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) [F.Additive] :
    (sheafify J F).Additive :=
  sheafify_additive_of_principal_covering_basis J hJ F

example {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} [F.Additive] (η : F ⟶ G)
    [Presheaf.IsLocallySurjective J η] (hG : Presheaf.IsSeparated J G)
    {X Y : Cᵒᵖ} (f g : X ⟶ Y) : G.map (f + g) = G.map f + G.map g := by
  have : G.Additive :=
    Presheaf.additive_of_isLocallySurjective_of_isSeparated J hJ η hG
  exact G.map_add
