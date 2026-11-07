/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.KTheory.Waldhausen.AsSmall.Connecting

/-!
# Regression source for actual AsSmall connecting transport

The first checks retain independent object and hom universes and the actual
fiber homeomorphism, including its complete path and specified basepoint.
Evaluation retains the precise `u + 1`/`u` hom universes and the given acyclic
functor square. Its degree-zero instance tests the original K₁-to-K₀ boundary.
No test assumes strict preservation of the chosen zero by the evaluated functor.

Implementation correspondence: `Quillen/Waldhausen/SmallModel/Connecting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Topology
open scoped Topology
universe u v

namespace CategoryTheory.Waldhausen.Fibration

section IndependentUniverses
variable {C : Type u} [Category.{v} C] {W : Structure C}
  (N : NestedWeakEquivalences W)

-- This is the actual induced map, rather than an arbitrary K-group isomorphism.
example (n : ℕ) : (acyclicSmallKEquiv N n).toMonoidHom =
    HomotopyGroup.piMap n (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv.toFun
      (acyclicSmallDeloopingHomeomorph_basepoint N) := rfl

example (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :
    (asSmallChangeWeakFiberHomeomorph N z).val.1 = W.asSmallDeloopingHomeomorph z.val.1 := rfl

example (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :
    (asSmallChangeWeakFiberHomeomorph N z).val.2 =
      N.coarse.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun.comp z.val.2 := rfl

example : asSmallChangeWeakFiberHomeomorph N
      (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint
        W.kBasepoint (changeWeakMap_basepoint N)) =
    HomotopyFiber.basepoint (changeWeakMap N.asSmall) N.asSmall.coarse.kBasepoint
      W.asSmall.kBasepoint (changeWeakMap_basepoint N.asSmall) :=
  asSmallChangeWeakFiberHomeomorph_basepoint N

example (t : unitInterval) (x : (acyclicStructure N).Delooping) :
    N.coarse.asSmallDeloopingHomeomorph (acyclicNullhomotopy N (t, x)) =
      acyclicNullhomotopy N.asSmall (t, acyclicSmallDeloopingHomeomorph N x) :=
  acyclicSmallNullhomotopy N t x

-- Equality of complete continuous maps retains both the source and the whole fiber path.
example :
    (asSmallChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun.comp (canonicalFiberMap N) =
      (canonicalFiberMap N.asSmall).comp
        (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv.toFun :=
  asSmall_canonicalFiberMap_square N

variable (h : IsWeakHomotopyEquivalence (canonicalFiberMap N))

example : IsWeakHomotopyEquivalence (canonicalFiberMap N.asSmall) :=
  canonicalFiberMap_isWeakHomotopyEquivalence_asSmall N h

example (n : ℕ) (x : N.coarse.K (n + 1)) :
    acyclicSmallKEquiv N n (changeWeakConnectingHom N h n x) =
      changeWeakConnectingHom N.asSmall
        (canonicalFiberMap_isWeakHomotopyEquivalence_asSmall N h) n
        (N.coarse.asSmallKEquiv (n + 1) x) :=
  acyclicSmallKEquiv_connecting N h n x

example (x : N.coarse.K 1) :
    acyclicSmallKEquiv N 0 (changeWeakConnectingHom N h 0 x) =
      changeWeakConnectingHom N.asSmall
        (canonicalFiberMap_isWeakHomotopyEquivalence_asSmall N h) 0
        (N.coarse.asSmallKEquiv 1 x) :=
  acyclicSmallKEquiv_connecting N h 0 x

end IndependentUniverses

section Lowering
variable {D : Type (u + 1)} [Category.{u} D] {W : Structure D}
  (M : NestedWeakEquivalences W)

example (n : ℕ) (x : (acyclicStructure M).K n) :
    KMap ((acyclicSmallDown_exact M).comp (acyclicStructure M).asSmall_up_exact) n
      (acyclicSmallKEquiv M n x) = (acyclicStructure M).asSmallKEquiv n x :=
  acyclicSmallDown_KMap_acyclicSmallKEquiv M n x

end Lowering

section Evaluation
variable {C : Type (u + 1)} [Category.{u + 1} C]
  {D : Type (u + 1)} [Category.{u} D]
  {V : Structure C} {W : Structure D}
  (N : NestedWeakEquivalences V) (M : NestedWeakEquivalences W)
  {F : C ⥤ D} (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFc : IsExact N.coarse.cof N.coarse.weq M.coarse.cof M.coarse.weq F)
  {A : AcyclicCategory N ⥤ AcyclicCategory M}
  (hA : IsExact (acyclicStructure N).cof (acyclicStructure N).weq
    (acyclicStructure M).cof (acyclicStructure M).weq A)
  (hAinc : A ⋙ acyclicInclusion M = acyclicInclusion N ⋙ F)
  (hN : IsWeakHomotopyEquivalence (canonicalFiberMap N))
  (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M))

-- The small-model equivalence and its inverse are part of the actual equation.
example (n : ℕ) (x : N.coarse.K (n + 1)) :
    KMap (hA.comp (acyclicStructure M).asSmall_up_exact) n
      (changeWeakConnectingHom N hN n x) =
    (acyclicStructure M).asSmallKEquiv n
      (changeWeakConnectingHom M hM n
        ((M.coarse.asSmallKEquiv (n + 1)).symm
          (KMap (hFc.comp M.coarse.asSmall_up_exact) (n + 1) x))) :=
  changeWeakConnectingHom_evaluation N M hF hFc hA hAinc hN hM n x

example (x : N.coarse.K 1) :
    KMap (hA.comp (acyclicStructure M).asSmall_up_exact) 0
      (changeWeakConnectingHom N hN 0 x) =
    (acyclicStructure M).asSmallKEquiv 0
      (changeWeakConnectingHom M hM 0
        ((M.coarse.asSmallKEquiv 1).symm
          (KMap (hFc.comp M.coarse.asSmall_up_exact) 1 x))) :=
  changeWeakConnectingHom_evaluation N M hF hFc hA hAinc hN hM 0 x

end Evaluation
end CategoryTheory.Waldhausen.Fibration
