/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.AsSmall.Fiber
public import Colib.KTheory.Waldhausen.Fibration.ConnectingNaturality

/-!
# Original connecting maps under Mathlib AsSmall

The actual AsSmall homeomorphisms preserve the original full canonical
fiber map, its based point and connecting homomorphism. Exact evaluation from
a common-universe category into a category with smaller homs uses precisely
these homeomorphisms and the original canonically rebased K-maps.

Implementation provenance: adapted from
`Quillen/Waldhausen/SmallModel/Connecting.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. All six original declarations,
the actual based homeomorphisms and complete fiber paths are retained.
The evaluation theorem has precisely object universe `u + 1`, source hom
universe `u + 1`, and target hom universe `u`. No strict chosen-zero
preservation or replacement connecting homomorphism is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Topology
open scoped Topology
universe u
namespace CategoryTheory.Waldhausen.Fibration

private theorem piMap_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (h : f = g) : HomotopyGroup.piMap n f hf = HomotopyGroup.piMap n g hg := by
  subst g
  rfl

/-- Weakness of the original canonical comparison transports to its actual small model. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence_asSmall
    {C : Type*} [Category* C] {W : Structure C}
    (N : NestedWeakEquivalences W)
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N.asSmall) := by
  have hh := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (asSmallChangeWeakFiberHomeomorph N).toHomotopyEquiv).comp h
  rw [asSmall_canonicalFiberMap_square] at hh
  exact hh.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv
    (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv)

/-- The actual acyclic small-model homeomorphism induces this K-equivalence. -/
def acyclicSmallKEquiv {C : Type*} [Category* C] {W : Structure C}
    (N : NestedWeakEquivalences W) (n : ℕ) :
    (acyclicStructure N).K n ≃* (acyclicStructure N.asSmall).K n :=
  homotopyEquivPiEquiv (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv
    (acyclicSmallDeloopingHomeomorph_basepoint N) n

/-- The complete small-model fiber homeomorphism retains the original based point. -/
theorem asSmallChangeWeakFiberHomeomorph_basepoint {C : Type*} [Category* C] {W : Structure C}
    (N : NestedWeakEquivalences W) :
    asSmallChangeWeakFiberHomeomorph N
      (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint
        W.kBasepoint (changeWeakMap_basepoint N)) =
      HomotopyFiber.basepoint (changeWeakMap N.asSmall) N.asSmall.coarse.kBasepoint
        W.asSmall.kBasepoint (changeWeakMap_basepoint N.asSmall) := by
  apply Subtype.ext
  apply Prod.ext
  · exact W.asSmallDeloopingHomeomorph_basepoint
  · exact ContinuousMap.ext (fun _ ↦ N.coarse.asSmallDeloopingHomeomorph_basepoint)

/-- The original connecting map is preserved by the actual small-model homeomorphisms. -/
theorem acyclicSmallKEquiv_connecting {C : Type*} [Category* C] {W : Structure C}
    (N : NestedWeakEquivalences W)
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (x : N.coarse.K (n + 1)) :
    acyclicSmallKEquiv N n (changeWeakConnectingHom N h n x) =
      changeWeakConnectingHom N.asSmall
        (canonicalFiberMap_isWeakHomotopyEquivalence_asSmall N h) n
        (N.coarse.asSmallKEquiv (n + 1) x) := by
  apply (canonicalFiberKMap_bijective_of_weak N.asSmall
    (canonicalFiberMap_isWeakHomotopyEquivalence_asSmall N h) n).injective
  have hs :
      (HomotopyGroup.piMap n (asSmallChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun
        (asSmallChangeWeakFiberHomeomorph_basepoint N)).comp (canonicalFiberKMap N n) =
      (canonicalFiberKMap N.asSmall n).comp (acyclicSmallKEquiv N n).toMonoidHom := by
    change (HomotopyGroup.piMap n _ _).comp (HomotopyGroup.piMap n _ _) =
      (HomotopyGroup.piMap n _ _).comp (HomotopyGroup.piMap n _ _)
    rw [← HomotopyGroup.mapHom_comp, ← HomotopyGroup.mapHom_comp]
    congr 1
    exact asSmall_canonicalFiberMap_square N
  have hc := HomotopyFiber.connectingHom_mapAt_natural
    (f := changeWeakMap N) (g := changeWeakMap N.asSmall)
    W.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
    N.coarse.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
    (asSmall_changeWeak_square N)
    W.kBasepoint N.coarse.kBasepoint W.asSmall.kBasepoint N.asSmall.coarse.kBasepoint
    (changeWeakMap_basepoint N) (changeWeakMap_basepoint N.asSmall)
    W.asSmallDeloopingHomeomorph_basepoint
    N.coarse.asSmallDeloopingHomeomorph_basepoint n
  have hm : (asSmallChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun =
      HomotopyFiber.mapAt W.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
        N.coarse.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
        (asSmall_changeWeak_square N) N.coarse.kBasepoint N.asSmall.coarse.kBasepoint
        N.coarse.asSmallDeloopingHomeomorph_basepoint := by
    ext z
    apply Subtype.ext
    rfl
  have hx : HomotopyGroup.piMap n (asSmallChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun
      (asSmallChangeWeakFiberHomeomorph_basepoint N)
      (canonicalFiberKMap N n (changeWeakConnectingHom N h n x)) =
      canonicalFiberKMap N.asSmall n
        (acyclicSmallKEquiv N n (changeWeakConnectingHom N h n x)) :=
    DFunLike.congr_fun hs (changeWeakConnectingHom N h n x)
  have hc' : HomotopyGroup.piMap n (asSmallChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun
      (asSmallChangeWeakFiberHomeomorph_basepoint N)
      (HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
        W.kBasepoint (changeWeakMap_basepoint N) n x) =
      HomotopyFiber.connectingHom (changeWeakMap N.asSmall) N.asSmall.coarse.kBasepoint
        W.asSmall.kBasepoint (changeWeakMap_basepoint N.asSmall) n
        (N.coarse.asSmallKEquiv (n + 1) x) := by
    exact (DFunLike.congr_fun (piMap_congr n _ _ _ _ hm) _).trans
      (DFunLike.congr_fun hc x)
  exact hx.symm.trans ((congrArg
    (HomotopyGroup.piMap n (asSmallChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun
      (asSmallChangeWeakFiberHomeomorph_basepoint N))
    (canonicalFiberKMap_connecting N h n x)).trans
      (hc'.trans (canonicalFiberKMap_connecting N.asSmall
        (canonicalFiberMap_isWeakHomotopyEquivalence_asSmall N h) n
        (N.coarse.asSmallKEquiv (n + 1) x)).symm))

/-- Lowering the actual lifted acyclic model gives its original small-model K-coordinate. -/
theorem acyclicSmallDown_KMap_acyclicSmallKEquiv {C : Type (u + 1)} [Category.{u} C]
    {W : Structure C} (N : NestedWeakEquivalences W) (n : ℕ)
    (x : (acyclicStructure N).K n) :
    KMap ((acyclicSmallDown_exact N).comp (acyclicStructure N).asSmall_up_exact) n
      (acyclicSmallKEquiv N n x) = (acyclicStructure N).asSmallKEquiv n x := by
  have hs : (acyclicSmallSSetIso N).hom ≫
      sSetMap ((acyclicSmallDown_exact N).comp (acyclicStructure N).asSmall_up_exact) =
      (acyclicStructure N).asSmallSSetIso.hom := by
    ext m A : 4
    apply Subtype.ext
    rfl
  have hh := congrArg (fun f ↦ (SSet.toTop.map f).hom) hs
  rw [SSet.toTop.map_comp] at hh
  have hk : (KMap ((acyclicSmallDown_exact N).comp
      (acyclicStructure N).asSmall_up_exact) n).comp
        (acyclicSmallKEquiv N n).toMonoidHom =
      ((acyclicStructure N).asSmallKEquiv n).toMonoidHom := by
    rw [KMap_eq_piMap_of_zeroEq _ rfl n]
    change (HomotopyGroup.piMap n _ _).comp (HomotopyGroup.piMap n _ _) = HomotopyGroup.piMap n _ _
    rw [← HomotopyGroup.mapHom_comp]
    exact piMap_congr n _ _ _ _ hh
  exact DFunLike.congr_fun hk x

/-- Actual fine/coarse exact evaluation preserves the original connecting maps
across the hom universes after the specified acyclic functor square. -/
theorem changeWeakConnectingHom_evaluation
    {C : Type (u + 1)} [Category.{u + 1} C]
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
    (hM : IsWeakHomotopyEquivalence (canonicalFiberMap M)) (n : ℕ)
    (x : N.coarse.K (n + 1)) :
    KMap (hA.comp (acyclicStructure M).asSmall_up_exact) n
      (changeWeakConnectingHom N hN n x) =
    (acyclicStructure M).asSmallKEquiv n
      (changeWeakConnectingHom M hM n
        ((M.coarse.asSmallKEquiv (n + 1)).symm
          (KMap (hFc.comp M.coarse.asSmall_up_exact) (n + 1) x))) := by
  let hf := hF.comp W.asSmall_up_exact
  let hc := hFc.comp M.coarse.asSmall_up_exact
  let ha := acyclicFunctor_exact N M.asSmall hf hc
  let hl := (acyclicSmallDown_exact M).comp (acyclicStructure M).asSmall_up_exact
  have hn : KMap ha n (changeWeakConnectingHom N hN n x) =
      changeWeakConnectingHom M.asSmall
        (canonicalFiberMap_isWeakHomotopyEquivalence_asSmall M hM) n
        (KMap hc (n + 1) x) :=
    DFunLike.congr_fun (changeWeakConnectingHom_natural N M.asSmall hf hc hN
      (canonicalFiberMap_isWeakHomotopyEquivalence_asSmall M hM) n) x
  have hb : (acyclicFunctor N M.asSmall hc ⋙ acyclicSmallDown M) ⋙
      acyclicInclusion M = acyclicInclusion N ⋙ F := rfl
  let : (acyclicInclusion M).Full := inferInstanceAs ((acyclicObjects M).ι).Full
  let : (acyclicInclusion M).Faithful := inferInstanceAs ((acyclicObjects M).ι).Faithful
  have hAi := Functor.fullyFaithfulCancelRight (acyclicInclusion M)
    (eqToIso (hb.trans hAinc.symm))
  have hk := KMap_eq_of_iso (ha.comp hl)
    (hA.comp (acyclicStructure M).asSmall_up_exact)
    (Functor.isoWhiskerRight hAi AsSmall.up) n
  calc
    _ = KMap hl n (KMap ha n (changeWeakConnectingHom N hN n x)) :=
      (DFunLike.congr_fun hk (changeWeakConnectingHom N hN n x)).symm.trans
        (DFunLike.congr_fun (KMap_comp_KMap ha hl n).symm
          (changeWeakConnectingHom N hN n x))
    _ = KMap hl n (changeWeakConnectingHom M.asSmall
        (canonicalFiberMap_isWeakHomotopyEquivalence_asSmall M hM) n
        (KMap hc (n + 1) x)) := congrArg (KMap hl n) hn
    _ = _ := by
      have hs := acyclicSmallKEquiv_connecting M hM n
        ((M.coarse.asSmallKEquiv (n + 1)).symm (KMap hc (n + 1) x))
      rw [MulEquiv.apply_symm_apply] at hs
      exact (congrArg (KMap hl n) hs.symm).trans
        (acyclicSmallDown_KMap_acyclicSmallKEquiv M n _)

attribute [colib_tag "COL-0294"] acyclicSmallKEquiv_connecting
  changeWeakConnectingHom_evaluation

attribute [colib_ref "Waldhausen1985"
  "Section 1.6, Theorem 1.6.4 and proof, pp. 350-352" "background"
  "The classical acyclic-to-fiber comparison is background for this actual AsSmall boundary
    transport; unequal hom universes and explicit comparison-weakness premises are retained",
  colib_ref "ThomasonTrobaugh1990" "Sections 1.8.1-1.8.2, p. 263" "background"
    "The classical fiber sequence specifies a zero-to-acyclic nullhomotopy; the actual whole
      path and original boundary, including K-one to K-zero, are transported here"]
  acyclicSmallKEquiv_connecting changeWeakConnectingHom_evaluation

end CategoryTheory.Waldhausen.Fibration
