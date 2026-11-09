/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.Sites.SheafifyLocallyBijective

open CategoryTheory

universe u v w u' v'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [HasWeakSheafify J A] [J.WEqualsLocallyBijective A]
  {P Q : Cᵒᵖ ⥤ A} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
  [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]

example : IsIso (sheafifyLift J η hQ) :=
  isIso_sheafifyLift_of_isLocallyBijective J η hQ

example : toSheafify J P ≫ sheafifyLift J η hQ = η :=
  toSheafify_sheafifyLift J η hQ
