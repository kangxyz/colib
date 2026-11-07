/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberNaturality
public import Colib.KTheory.Waldhausen.Fibration.LongExactSequence

/-!
# Naturality of the original change-of-weak connecting maps

Any functor exact for both nested structures preserves the actual connecting
homomorphisms when both original canonical comparisons are weak equivalences.
The original canonical rebasing removes strict preservation of chosen zero.
No connecting-square or arbitrary replacement boundary is supplied as input.

Implementation provenance: adapted from
`Quillen/Waldhausen/Fibration/ConnectingNaturality.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zeros, whole path coordinates and shared universe pair are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Topology
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

/-- The original connecting maps commute for a strictly chosen-zero-preserving functor. -/
lemma changeWeakConnectingHom_natural_of_zeroEq (h0 : F.obj V.zero = W.zero)
    (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M)) (n : ℕ) :
    (KMap (acyclicFunctor_exact N M hF hFc) n).comp (changeWeakConnectingHom N hN n) =
    (changeWeakConnectingHom M hM n).comp (KMap hFc (n + 1)) := by
  ext x
  apply (canonicalFiberKMap_bijective_of_weak M hM n).injective
  have H := DFunLike.congr_fun (canonicalFiberKMap_natural N M hF hFc h0 n)
    (changeWeakConnectingHom N hN n x)
  simp only [MonoidHom.comp_apply] at H ⊢
  rw [← H, canonicalFiberKMap_connecting, canonicalFiberKMap_connecting,
    KMap_eq_piMap_of_zeroEq hFc (coarse_zero_eq N M h0)]
  exact DFunLike.congr_fun (HomotopyFiber.connectingHom_mapAt_natural
    (deloopingMap hF).hom (deloopingMap hFc).hom (changeWeakMap_natural N M hF hFc)
    V.kBasepoint N.coarse.kBasepoint W.kBasepoint M.coarse.kBasepoint
    (changeWeakMap_basepoint N) (changeWeakMap_basepoint M)
    (deloopingMap_basepoint_of_zeroEq hF h0)
    (deloopingMap_basepoint_of_zeroEq hFc (coarse_zero_eq N M h0)) n) x

/-- Every fine-and-coarse exact functor preserves the original connecting maps,
including the K₁-to-K₀ boundary, without a strict chosen-zero hypothesis. -/
lemma changeWeakConnectingHom_natural
    (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M)) (n : ℕ) :
    (KMap (acyclicFunctor_exact N M hF hFc) n).comp (changeWeakConnectingHom N hN n) =
    (changeWeakConnectingHom M hM n).comp (KMap hFc (n + 1)) := by
  let e := CategoryTheory.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)
  have hFc' := hFc.of_iso e
  have H := changeWeakConnectingHom_natural_of_zeroEq N M hF.rebase hFc'
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) hN hM n
  rw [← KMap_eq_of_iso (acyclicFunctor_exact N M hF hFc)
      (acyclicFunctor_exact N M hF.rebase hFc') (acyclicFunctorIso N M hFc hFc' e) n,
    ← KMap_eq_of_iso hFc hFc' e (n + 1)] at H
  exact H

attribute [colib_tag "COL-0291",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4 and proof, pp. 350-352"
    "background" "The original canonical acyclic-to-fiber comparison; its full-path naturality
      and the induced original connecting-map square are proved here",
  colib_ref "ThomasonTrobaugh1990" "Sections 1.8.1-1.8.2, p. 263"
    "background" "The classical K-theory fiber sequence and chosen zero-to-object nullhomotopy;
      the present naturality preserves its actual path-space boundary, including K-one to K-zero"]
  changeWeakConnectingHom_natural

attribute [colib_ref "ThomasonTrobaugh1990" "Section 1.5.4, pp. 260-261"
  "ingredient" "Exact-functor spectrum maps and homotopies from weak natural transformations;
    the complete rebased path-level connecting square is proved in this implementation"]
  changeWeakConnectingHom_natural

end CategoryTheory.Waldhausen.Fibration
