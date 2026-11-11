/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarLocalZero

/-! Uncompiled consumers of the real scalar maps, with independent coefficient universe. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe v u

section GeneralDegree

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  (f : X ⟶ Y) [IsFinite f] [Flat f]

example (x : X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) =
      Module.length (Y.presheaf.stalk (f x)) (Y.presheaf.stalk (f x)) *
        Module.length (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) :=
  length_stalk_eq_mul_localFiberLength f x

example (y : Y) :
    finiteCyclePushforward f (AlgebraicCycle.fundamentalCycle X) y =
      (f.finrank y : ℤ) * AlgebraicCycle.fundamentalCycle Y y :=
  finiteCyclePushforward_fundamentalCycle_apply f y

example (d : ℕ) (hd : ∀ y, f.finrank y = d) :
    finiteCyclePushforward f (AlgebraicCycle.fundamentalCycle X) =
      (d : ℤ) • AlgebraicCycle.fundamentalCycle Y :=
  finiteCyclePushforward_fundamentalCycle_of_constant_finrank f d hd

end GeneralDegree

section InseparableAllowed

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
  {X : Scheme.{u}} [IsNoetherian X] (q : X ⟶ Spec (.of k))

-- No separability, reducedness or finite-type assumption on q is present.
example (x : X) :
    (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k E)))).finrank x =
      Module.finrank k E := finrank_scalarProjection q x

end InseparableAllowed

section NativeTransfer

variable {k E L : Type u} [Field k] [Field E] [Field L]
  [Algebra k E] [Module.Finite k E] [Algebra.IsSeparable k E]
  [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L]
  (P : PresheafWithTransfers.{v} k)

example (X : SmoothSite (Spec (.of k))) :
    Cor.ofFiniteFlatSpan (𝟙 X.left) (𝟙 X.left) (by simp) = 𝟙 (Cor.mk X) :=
  Cor.ofFiniteFlatSpan_id X

example (X : SmoothSite (Spec (.of k))) :
    Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X) ≫
        (Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) X) =
      (Module.finrank k E : ℤ) • 𝟙 (Cor.mk X) := Cor.finiteScalarTrace_comp_graph X

example (X : SmoothSite (Spec (.of k))) :
    transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) X)) ≫
      transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X)) =
      (Module.finrank k E : ℤ) • 𝟙 (sections P (Cor.mk X)) :=
  finiteScalar_restriction_trace P X

example (X : SmoothSite (Spec (.of k))) (s : sections P (Cor.mk X))
    (hs : transfer P ((Cor.graphFunctor k).map
      (SmoothSite.finiteScalarProjection (E := E) X)) s = 0) :
    (Module.finrank k E : ℤ) • s = 0 :=
  finrank_smul_eq_zero_of_scalar_restriction_eq_zero P X s hs

example (X : Cor L) : sections (finiteSeparableExtension L P) X =
    sections P ((Cor.finiteSeparableForgetBase k L).obj X) := rfl

example {X Y : Cor L} (a : X ⟶ Y) :
    transfer (finiteSeparableExtension L P) a =
      transfer P ((Cor.finiteSeparableForgetBase k L).map a) := rfl

example {X Y : SmoothSite (Spec (.of L))} (a : X ⟶ Y) :
    ((toPresheaf L).obj (finiteSeparableExtension L P)).map a.op =
      ((toPresheaf k).obj P).map ((SmoothSite.finiteSeparableForgetBase k L).map a).op :=
  finiteSeparableExtension_graph L P a

example (X : SmoothSite (Spec (.of k))) :
    sections (finiteSeparableExtension L P)
        (Cor.mk ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X)) ≅
      sections P (Cor.mk (SmoothSite.finiteScalarExtension (E := L) X)) :=
  finiteScalarSectionIso P X

example (X : SmoothSite (Spec (.of k))) :
    transfer P ((Cor.graphFunctor k).map
      (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) ≫
      (finiteScalarSectionIso P X).hom =
    transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := L) X)) :=
  finiteScalarSectionIso_projection P X

example {U X : SmoothSite (Spec (.of k))} (a : U ⟶ X) :
    transfer P ((Cor.graphFunctor k).map a) ≫
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) U)) =
    transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) X)) ≫
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) a)) :=
  finiteScalarRestriction_naturality P a

example {U X : SmoothSite (Spec (.of k))} (a : U ⟶ X) (s : sections P (Cor.mk X))
    (hs : transfer P ((Cor.graphFunctor k).map a) s = 0) :
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map a))
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s) = 0 :=
  native_scalar_restriction_eq_zero_of_restriction_eq_zero P a s hs

example {U X : SmoothSite (Spec (.of k))} (a : U ⟶ X) (s : sections P (Cor.mk X))
    (hs : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
      ((SmoothSite.fieldBaseChange (algebraMap k L)).map a))
      (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s) = 0) :
    (Module.finrank k L : ℤ) • transfer P ((Cor.graphFunctor k).map a) s = 0 :=
  finrank_smul_restriction_eq_zero_of_native_scalar_zero P a s hs

example
    {U X : SmoothSite (Spec (.of k))} (a : U ⟶ X) (s : sections P (Cor.mk X))
    (hE : transfer (finiteSeparableExtension E P) ((Cor.graphFunctor E).map
        ((SmoothSite.fieldBaseChange (algebraMap k E)).map a))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := E) X)) s) = 0)
    (hL : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        ((SmoothSite.fieldBaseChange (algebraMap k L)).map a))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s) = 0)
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    transfer P ((Cor.graphFunctor k).map a) s = 0 :=
  restriction_eq_zero_of_coprime_native_scalar_zeros P a s hE hL hdegree

example
    (X : SmoothSite (Spec (.of k))) (s : sections P (Cor.mk X)) (x : X.left)
    (V : ((SmoothSite.fieldBaseChange (algebraMap k E)).obj X).left.Opens)
    (W : ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X).left.Opens)
    (hV : (SmoothSite.finiteScalarProjection (E := E) X).left ⁻¹' {x} ⊆
      (V : Set ((SmoothSite.fieldBaseChange (algebraMap k E)).obj X).left))
    (hW : (SmoothSite.finiteScalarProjection (E := L) X).left ⁻¹' {x} ⊆
      (W : Set ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X).left))
    (zV : transfer (finiteSeparableExtension E P) ((Cor.graphFunctor E).map
        (SmoothSite.homMk (X := SmoothSite.mk (V.ι ≫
          ((SmoothSite.fieldBaseChange (algebraMap k E)).obj X).hom))
          (Y := (SmoothSite.fieldBaseChange (algebraMap k E)).obj X) V.ι rfl))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := E) X)) s) = 0)
    (zW : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (SmoothSite.homMk (X := SmoothSite.mk (W.ι ≫
          ((SmoothSite.fieldBaseChange (algebraMap k L)).obj X).hom))
          (Y := (SmoothSite.fieldBaseChange (algebraMap k L)).obj X) W.ι rfl))
        (transfer P ((Cor.graphFunctor k).map
          (SmoothSite.fieldBaseChangeForgetProjection (L := L) X)) s) = 0)
    (hdegree : (Module.finrank k E).Coprime (Module.finrank k L)) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ x ∈ U ∧
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (U.ι ≫ X.hom)) (Y := X) U.ι rfl)) s = 0 :=
  exists_affine_zero_open_of_coprime_scalar_zero_opens P X s x V W hV hW zV zW hdegree

end NativeTransfer
