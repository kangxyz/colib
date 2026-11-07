/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.Fibration.ConnectingNaturality

/-!
# Regression source for the original fibration and LES naturality

These checks use the actual restricted functor, cylinder, reversed null track,
mapAt coordinates and canonical K-maps. The arbitrary-functor checks deliberately
have no chosen-zero equality. The last checks retain the K₁-to-K₀ boundary.

Implementation correspondence: the three original naturality modules in
`Quillen/Waldhausen/Fibration` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Topology
open scoped Simplicial Topology
universe u v

namespace CategoryTheory.Waldhausen.Fibration

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {V : Structure C} {W : Structure D} {T : Structure E}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  (L : NestedWeakEquivalences T) {F G : C ⥤ D} {J : D ⥤ E}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)

-- The full-subcategory restriction is the original lift, on actual objects and arrows.
example : acyclicFunctor N M hFc =
    (acyclicObjects M).lift (acyclicInclusion N ⋙ F)
      (fun X => map_acyclic N M hFc X.property) := rfl

example (X : AcyclicCategory N) : ((acyclicFunctor N M hFc).obj X).obj = F.obj X.obj := rfl

example {X Y : AcyclicCategory N} (f : X ⟶ Y) :
    ((acyclicFunctor N M hFc).map f).hom = F.map f.hom := rfl

example : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
    (acyclicStructure M).cof (acyclicStructure M).weq (acyclicFunctor N M hFc) :=
  acyclicFunctor_exact N M hF hFc

example : acyclicFunctor N N (IsExact.id N.coarse.cof N.coarse.weq) =
    𝟭 (AcyclicCategory N) := acyclicFunctor_id N

example (hJc : IsExact M.coarse.cof M.coarse.weq L.coarse.cof L.coarse.weq J) :
    acyclicFunctor N L (hFc.comp hJc) =
      acyclicFunctor N M hFc ⋙ acyclicFunctor M L hJc :=
  acyclicFunctor_comp N M hFc L hJc

example : acyclicFunctor N M hFc ⋙ acyclicInclusion M = acyclicInclusion N ⋙ F :=
  acyclicFunctor_inclusion N M hFc

example (hGc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq G)
    (e : F ≅ G) (X : AcyclicCategory N) :
    ((acyclicFunctorIso N M hFc hGc e).hom.app X).hom = e.hom.app X.obj := rfl

-- Both original realization squares and both canonical K-map squares are retained.
example : (deloopingMap hFc).hom.comp (changeWeakMap N) =
    (changeWeakMap M).comp (deloopingMap hF).hom :=
  changeWeakMap_natural N M hF hFc

example : (deloopingMap hF).hom.comp (acyclicInclusionMap N) =
    (acyclicInclusionMap M).comp (deloopingMap (acyclicFunctor_exact N M hF hFc)).hom :=
  acyclicInclusionMap_natural N M hF hFc

example (n : ℕ) : (KMap hFc n).comp (KMap (changeWeak_exact N) n) =
    (KMap (changeWeak_exact M) n).comp (KMap hF n) :=
  changeWeakKMap_natural N M hF hFc n

example (n : ℕ) : (KMap hF n).comp (KMap (acyclicInclusion_exact N) n) =
    (KMap (acyclicInclusion_exact M) n).comp (KMap (acyclicFunctor_exact N M hF hFc) n) :=
  acyclicInclusionKMap_natural N M hF hFc n

section StrictZero
variable (h0 : F.obj V.zero = W.zero)

example : (acyclicFunctor N M hFc).obj (acyclicStructure N).zero =
    (acyclicStructure M).zero := acyclicFunctor_zero N M hFc h0

example : F.obj N.coarse.zero = M.coarse.zero := coarse_zero_eq N M h0

-- This tests the whole simplicial cylinder, not just its endpoint maps.
example :
    weakNaturalTransformationCylinder (acyclicStructure N) N.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) ≫ sSetMap hFc =
    sSetMap (acyclicFunctor_exact N M hF hFc) ▷ Δ[1] ≫
      weakNaturalTransformationCylinder (acyclicStructure M) M.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact M)
        (zeroToAcyclicInclusion M) (zeroToAcyclicInclusion_weak M) :=
  acyclicCylinder_natural N M hF hFc h0

-- There is no endpoint restriction on the time parameter.
example (t : unitInterval) (x : (acyclicStructure N).Delooping) :
    deloopingMap hFc (acyclicNullhomotopy N (t, x)) =
      acyclicNullhomotopy M (t, deloopingMap (acyclicFunctor_exact N M hF hFc) x) :=
  acyclicNullhomotopy_natural N M hF hFc h0 t x

example : fiberFunctorMap N M hF hFc h0 =
    HomotopyFiber.mapAt (deloopingMap hF).hom (deloopingMap hFc).hom
      (changeWeakMap_natural N M hF hFc) N.coarse.kBasepoint M.coarse.kBasepoint
      (deloopingMap_basepoint_of_zeroEq hFc (coarse_zero_eq N M h0)) := rfl

-- The mapAt source coordinate and every point of the full postcomposed path.
example (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :
    (fiberFunctorMap N M hF hFc h0 z).1.1 = deloopingMap hF z.1.1 := rfl

example (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :
    (fiberFunctorMap N M hF hFc h0 z).1.2 = (deloopingMap hFc).hom.comp z.1.2 := rfl

example (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) (t : unitInterval) :
    (fiberFunctorMap N M hF hFc h0 z).1.2 t = deloopingMap hFc (z.1.2 t) := rfl

example : fiberFunctorMap N M hF hFc h0
      (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint
        V.kBasepoint (changeWeakMap_basepoint N)) =
    HomotopyFiber.basepoint (changeWeakMap M) M.coarse.kBasepoint
      W.kBasepoint (changeWeakMap_basepoint M) :=
  fiberFunctorMap_basepoint N M hF hFc h0

example : (fiberFunctorMap N M hF hFc h0).comp (canonicalFiberMap N) =
    (canonicalFiberMap M).comp (deloopingMap (acyclicFunctor_exact N M hF hFc)).hom :=
  canonicalFiberMap_natural N M hF hFc h0

example (x : (acyclicStructure N).Delooping) (t : unitInterval) :
    (fiberFunctorMap N M hF hFc h0 (canonicalFiberMap N x)).1.2 t =
      (canonicalFiberMap M (deloopingMap (acyclicFunctor_exact N M hF hFc) x)).1.2 t :=
  congrArg (fun z => z.1.2 t)
    (ContinuousMap.congr_fun (canonicalFiberMap_natural N M hF hFc h0) x)

example (n : ℕ) :
    (HomotopyGroup.piMap n (fiberFunctorMap N M hF hFc h0)
      (fiberFunctorMap_basepoint N M hF hFc h0)).comp (canonicalFiberKMap N n) =
    (canonicalFiberKMap M n).comp (KMap (acyclicFunctor_exact N M hF hFc) n) :=
  canonicalFiberKMap_natural N M hF hFc h0 n

end StrictZero

-- Canonical rebasing removes strict chosen-zero preservation for this same F.
example (n : ℕ) :
    let e := CategoryTheory.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)
    KMap (acyclicFunctor_exact N M hF hFc) n =
      KMap (acyclicFunctor_exact N M hF.rebase (hFc.of_iso e)) n := by
  dsimp only
  exact KMap_eq_of_iso _ _
    (acyclicFunctorIso N M hFc _
      (CategoryTheory.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero))) n

variable (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
  (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M))

example (n : ℕ) :
    (KMap (acyclicFunctor_exact N M hF hFc) n).comp (changeWeakConnectingHom N hN n) =
      (changeWeakConnectingHom M hM n).comp (KMap hFc (n + 1)) :=
  changeWeakConnectingHom_natural N M hF hFc hN hM n

-- The bottom connecting map is K₁ of the coarse category to K₀ of its acyclic category.
example :
    (KMap (acyclicFunctor_exact N M hF hFc) 0).comp (changeWeakConnectingHom N hN 0) =
      (changeWeakConnectingHom M hM 0).comp (KMap hFc 1) :=
  changeWeakConnectingHom_natural N M hF hFc hN hM 0

example (x : N.coarse.K 1) :
    KMap (acyclicFunctor_exact N M hF hFc) 0 (changeWeakConnectingHom N hN 0 x) =
      changeWeakConnectingHom M hM 0 (KMap hFc 1 x) :=
  DFunLike.congr_fun (changeWeakConnectingHom_natural N M hF hFc hN hM 0) x

end CategoryTheory.Waldhausen.Fibration
