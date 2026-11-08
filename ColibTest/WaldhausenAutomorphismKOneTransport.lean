/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.AutomorphismKOne
import Colib.KTheory.Waldhausen.Fibration.CofiberObjectChangeWeak
import Colib.KTheory.Waldhausen.Fibration.BisimplexChangeWeak
import Colib.KTheory.Waldhausen.Fibration.IdentityCofiberComponent

/-! Abstract regressions for original K-one classes and complete change-weak transport.
These statements retain independent object/hom universes, arbitrary exact functors,
both cofiber certificates, every homotopy degree and independent path coordinates.
No ring or scheme application is imported. Source-only; not compiled in this task.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration CategoryTheory.Waldhausen.QuotientRows
open Topology Convexity Opposite SSet
open scoped Simplicial Topology
universe u v

section Classes
variable {C : Type u} [Category.{v} C] (W : Structure C)

example {A : C} (f : A ⟶ A) (hf : W.weq f) :
    W.weakEndomorphismKOneClass f hf =
      Topology.loopKOneNormalization (W.kZeroObjectLoop A)
        (FundamentalGroup.fromPath ⟦W.weakObjectSquareLoopPath f hf⟧) := rfl

example {A : C} {f g : A ⟶ A} (h : f = g) (hf : W.weq f) (hg : W.weq g) :
    W.weakEndomorphismKOneClass f hf = W.weakEndomorphismKOneClass g hg :=
  W.weakEndomorphismKOneClass_congr h hf hg

example {A : C} (e : A ≅ A) :
    W.automorphismKOneClass e =
      W.weakEndomorphismKOneClass e.hom (W.weq_iso e.hom inferInstance) := rfl

example (A : C) : W.automorphismKOneClass (Iso.refl A) = 1 :=
  W.automorphismKOneClass_refl A

example {A : C} (f g : A ⟶ A) (hf : W.weq f) (hg : W.weq g) :
    W.weakEndomorphismKOneClass (f ≫ g) (W.weq.comp_mem _ _ hf hg) =
      W.weakEndomorphismKOneClass g hg * W.weakEndomorphismKOneClass f hf :=
  W.weakEndomorphismKOneClass_comp f g hf hg

example (A : C) : Aut A →* W.K 1 := W.automorphismKOneHom A

example {A : C} (e : Aut A) :
    W.automorphismKOneHom A e = W.automorphismKOneClass e.asIso := rfl

example {A : C} (e f : Aut A) :
    W.automorphismKOneHom A (e * f) =
      W.automorphismKOneClass e.asIso * W.automorphismKOneClass f.asIso :=
  (W.automorphismKOneHom A).map_mul e f

example {A B : C} (e : A ≅ B) (f : A ⟶ A) (g : B ⟶ B)
    (hf : W.weq f) (hg : W.weq g) (h : f ≫ e.hom = e.hom ≫ g) :
    W.weakEndomorphismKOneClass f hf = W.weakEndomorphismKOneClass g hg :=
  W.weakEndomorphismKOneClass_iso e f g hf hg h

example {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g) :
    ((W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg)).Homotopy
      (W.weakObjectSquareLoopPath (f ≫ g) (W.weq.comp_mem _ _ hf hg)) :=
  W.weakObjectSquareCompositionTrack f g hf hg

example {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)
    (r s t : unitInterval) :
    W.weakObjectSquareCompositionTrack f g hf hg (r, s) t =
      W.weakObjectCompositionCube f g hf hg (r, s, t) :=
  W.weakObjectSquareCompositionTrack_apply f g hf hg r s t

end Classes

section ExactFunctor
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

-- Only the two strict intermediary tests have a chosen-zero equality assumption.
example (h0 : F.obj V.zero = W.zero) {A : C} (f : A ⟶ A) (hf : V.weq f) :
    ((V.weakObjectSquareLoopPath f hf).map
      (basedLoopMap (deloopingMap hF).hom
        (deloopingMap_basepoint_of_zeroEq hF h0)).continuous).cast
        (objectLoopMapEq hF h0 A).symm (objectLoopMapEq hF h0 A).symm =
      W.weakObjectSquareLoopPath (F.map f) (hF.weak f hf) :=
  weakObjectSquareLoopPath_postcompose hF h0 f hf

example (h0 : F.obj V.zero = W.zero) {A : C} (f : A ⟶ A) (hf : V.weq f) :
    KMap hF 1 (V.weakEndomorphismKOneClass f hf) =
      W.weakEndomorphismKOneClass (F.map f) (hF.weak f hf) :=
  KMap_weakEndomorphismKOneClass_of_zeroEq hF h0 f hf

example {A : C} (f : A ⟶ A) (hf : V.weq f) :
    KMap hF 1 (V.weakEndomorphismKOneClass f hf) =
      W.weakEndomorphismKOneClass (F.map f) (hF.weak f hf) :=
  KMap_weakEndomorphismKOneClass hF f hf

example {A : C} (e : A ≅ A) :
    KMap hF 1 (V.automorphismKOneClass e) = W.automorphismKOneClass (F.mapIso e) :=
  KMap_automorphismKOneClass hF e

end ExactFunctor

section WholeBisimplex
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

example {n m : ℕ} (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C)
    (hF : IsSimplex₂ V.cof V.weq F) (hG : IsSimplex₂ N.coarse.cof N.coarse.weq F)
    (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    changeWeakMap N (bisimplexRealization V F hF (z, t)) =
      bisimplexRealization N.coarse F hG (z, t) :=
  bisimplexRealization_changeWeak N F hF hG z t

example (F : Grid₂ ⦋2⦌ ⦋1⦌ ⥤ C)
    (hF : IsSimplex₂ V.cof V.weq F) (hG : IsSimplex₂ N.coarse.cof N.coarse.weq F)
    (z : StdSimplex ℝ (Fin 3)) (t : StdSimplex ℝ (Fin 2)) :
    changeWeakMap N (bisimplexRealization V F hF (z, t)) =
      bisimplexRealization N.coarse F hG (z, t) :=
  bisimplexRealization_changeWeak N F hF hG z t

example {A B : C} (f : A ⟶ B) (hf : V.weq f) (t z : StdSimplex ℝ (Fin 2)) :
    changeWeakMap N (bisimplexRealization V (V.weakObjectSimplex f hf).val
      ((isSimplex₂_diagonal_iff _ _ _).mpr (V.weakObjectSimplex f hf).property) (t, z)) =
      bisimplexRealization N.coarse (N.coarse.weakObjectSimplex f (N.le_weq _ hf)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          (N.coarse.weakObjectSimplex f (N.le_weq _ hf)).property) (t, z) :=
  weakObjectSquare_changeWeak N f hf t z

-- This derived regression compares every point of the actual fine/coarse weak-square paths.
example {A B : C} (f : A ⟶ B) (hf : V.weq f) (s t : unitInterval) :
    changeWeakMap N (V.weakObjectSquareLoopPath f hf s t) =
      N.coarse.weakObjectSquareLoopPath f (N.le_weq _ hf) s t := by
  exact weakObjectSquare_changeWeak N f hf
    (StdSimplex.homeomorphI.symm t) (StdSimplex.homeomorphI.symm s)

end WholeBisimplex

section WholeCofiber
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {V : Structure C} (N : NestedWeakEquivalences V)
  {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : V.cof i) (hi' : N.coarse.cof i)
  (hQ : IsPushout i (0 : A ⟶ V.zero) q (0 : V.zero ⟶ Q))
  (hQ' : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q))

example (r t : unitInterval) :
    changeWeakMap N (V.cofiberObjectLoopTrack i q hi hQ (r, t)) =
      N.coarse.cofiberObjectLoopTrack i q hi' hQ' (r, t) :=
  cofiberObjectLoopTrack_changeWeak N i q hi hi' hQ hQ' r t

end WholeCofiber

section IdentityComponent
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {V : Structure C} (N : NestedWeakEquivalences V) (A : C)

example (n : ℕ) :
    HomotopyGroup.Pi n (Path V.kBasepoint V.kBasepoint) (Path.refl V.kBasepoint) ≃
      HomotopyGroup.Pi n (Path V.kBasepoint V.kBasepoint) (V.kZeroObjectLoop A) :=
  V.identityCofiberComponentEquiv A n

example (s t : unitInterval) :
    changeWeakMap N (V.identityCofiberSuffixPath A s t) =
      N.coarse.identityCofiberSuffixPath A s t :=
  identityCofiberSuffixPath_changeWeak N A s t

-- Equality of the entire suffix path, including the two actual endpoint casts.
example :
    ((V.identityCofiberSuffixPath A).map
      (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)).continuous).cast
      (by
        have hA : basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N)
            (V.kZeroObjectLoop A) = N.coarse.kZeroObjectLoop A :=
          deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A
        rw [basedLoopMap_trans, basedLoopMap_refl, hA])
      (deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A).symm =
        N.coarse.identityCofiberSuffixPath A := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  exact identityCofiberSuffixPath_changeWeak N A s t

example (n : ℕ)
    (a : HomotopyGroup.Pi n (Path V.kBasepoint V.kBasepoint) (Path.refl V.kBasepoint)) :
    N.coarse.identityCofiberComponentEquiv A n
        (HomotopyGroup.map (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
          (basedLoopMap_refl _ _) a) =
      HomotopyGroup.map (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A)
        (V.identityCofiberComponentEquiv A n a) :=
  identityCofiberComponentEquiv_naturality N A n a

example (a : HomotopyGroup.Pi 0
    (Path V.kBasepoint V.kBasepoint) (Path.refl V.kBasepoint)) :
    N.coarse.identityCofiberComponentEquiv A 0
        (HomotopyGroup.map (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
          (basedLoopMap_refl _ _) a) =
      HomotopyGroup.map (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
        (deloopingMap_kZeroObjectLoop (changeWeak_exact N) N.zero_eq.symm A)
        (V.identityCofiberComponentEquiv A 0 a) :=
  identityCofiberComponentEquiv_naturality N A 0 a

end IdentityComponent
