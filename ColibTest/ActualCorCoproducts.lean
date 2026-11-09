/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Coproducts.Finite

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

noncomputable section

variable (k : Type u) [Field k]

example (X Y T : Cor k) : Function.Bijective
    (fun α : Cor.coproduct k X Y ⟶ T =>
      (Cor.coproductInl k X Y ≫ α, Cor.coproductInr k X Y ≫ α)) :=
  Cor.coproduct_restriction_bijective k X Y T

example (X Y : Cor k) :
    IsColimit (BinaryCofan.mk (Cor.coproductInl k X Y) (Cor.coproductInr k X Y)) :=
  Cor.coproductIsColimit k X Y

example : HasFiniteBiproducts (Cor k) := inferInstance

example : HasFiniteCoproducts (Cor k) := inferInstance

example {n : ℕ} {T : Cor k} {Y : Fin n → SmoothSite (Spec (.of k))}
    (f : ∀ i, Cor.mk (Y i) ⟶ T) (i : Fin n) :
    (Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i) ≫
      Cor.finiteCoproductDesc k f = f i :=
  Cor.finiteCoproductι_desc k f i

example {n : ℕ} {T T' : Cor k} {Y : Fin n → SmoothSite (Spec (.of k))}
    (f : ∀ i, Cor.mk (Y i) ⟶ T) (g : T ⟶ T') :
    Cor.finiteCoproductDesc k f ≫ g = Cor.finiteCoproductDesc k (fun i => f i ≫ g) :=
  Cor.finiteCoproductDesc_comp k f g

example {n : ℕ} {X : SmoothSite (Spec (.of k))} {Y : Fin n → SmoothSite (Spec (.of k))}
    (f : ∀ i, Y i ⟶ X) :
    Cor.finiteCoproductDesc k (fun i => (Cor.graphFunctor k).map (f i)) =
      (Cor.graphFunctor k).map (SmoothSite.finiteCoproductDesc f) :=
  Cor.finiteCoproductDesc_graph k f

example {n : ℕ} (Y : Fin n → SmoothSite (Spec (.of k))) :
    IsColimit (Cofan.mk (Cor.mk (SmoothSite.finiteCoproduct Y))
      (fun i => (Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i))) :=
  Cor.finiteCoproductIsColimit k Y

example (Y : Fin 0 → SmoothSite (Spec (.of k))) (T : Cor k)
    (α : Cor.mk (SmoothSite.finiteCoproduct Y) ⟶ T) : α = 0 := by
  have : IsEmpty (Cor.mk (SmoothSite.finiteCoproduct Y)).toSmoothSite.left :=
    inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
  exact Cor.hom_eq_zero_of_isEmpty_source k α
