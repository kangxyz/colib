/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSectionUnit

/-! Consumers retain arbitrary schemes, the same chosen zero and actual scalar pullback. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules CategoryTheory.Functor.IdentityAutomorphism
universe u

example (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionEvaluation X).IsEquivalence := inferInstance

example (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionEvaluation X).obj
      (boundedAboveFlatGlobalSectionWaldhausen X).zero =
        boundedAboveFlatGlobalFiberZero X := rfl

example {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (boundedAboveFlatGlobalSectionsMap f).obj (boundedAboveFlatGlobalSectionZero X) =
      boundedAboveFlatGlobalSectionZero Y := boundedAboveFlatGlobalSectionsMap_zero f

example {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedAboveFlatGlobalSectionWaldhausen X).cof
      (boundedAboveFlatGlobalSectionWaldhausen X).weq
      (boundedAboveFlatGlobalSectionWaldhausen Y).cof
      (boundedAboveFlatGlobalSectionWaldhausen Y).weq (boundedAboveFlatGlobalSectionsMap f) :=
  boundedAboveFlatGlobalSectionsMap_exact f

example {X Y Z : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g) =
      boundedAboveFlatGlobalSectionModelFunctor.map f ≫
        boundedAboveFlatGlobalSectionModelFunctor.map g :=
  boundedAboveFlatGlobalSectionModelFunctor.map_comp f g

example {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (r : (Γ(X.unop, ⊤))ˣ)
    (S : BoundedAboveFlatGlobalSections X) :
    (boundedAboveFlatGlobalSectionsMap f).map ((boundedAboveFlatGlobalSectionUnit X r).hom.app S) =
      (boundedAboveFlatGlobalSectionUnit Y (Units.map f.unop.appTop.hom.toMonoidHom r)).hom.app
        ((boundedAboveFlatGlobalSectionsMap f).obj S) :=
  boundedAboveFlatGlobalSectionUnit_reindex f r S

example {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (r : (Γ(X.unop, ⊤))ˣ)
    (s : (Γ(Y.unop, ⊤))ˣ) (h : Units.map f.unop.appTop.hom.toMonoidHom r = s) :
    Preserves (boundedAboveFlatGlobalSectionsMap f)
      (boundedAboveFlatGlobalSectionUnit X r) (boundedAboveFlatGlobalSectionUnit Y s) :=
  boundedAboveFlatGlobalSectionUnit_reindex_of_eq f r s h
