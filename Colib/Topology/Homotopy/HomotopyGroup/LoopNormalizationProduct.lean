/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.PeriodicLoopFamilies

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.KOneNormalization
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.Reversal
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup
public import Colib.Topology.HomotopyFiber.LoopPrefixHomotopy
public import Colib.Topology.Homotopy.HomotopyGroup.Product

/-!
# Products of original normalized loop self-tracks

The original inverse-prefix normalization respects pointwise products of loop
self-tracks when the actual fundamental-group action on Pi two is trivial.
Free-path evaluation identifies the left/right normalization difference with
that action. Genuine associator and cancellation homotopies handle fixed
prefixes and suffixes; the product fundamental group then separates the two axes.

All spaces, paths, caps and degree shifts are the original topological objects.
The pointwise product is the existing `IdentityTrack.loopProduct` from
`PeriodicLoopFamilies`; it is not redeclared here. No K-theory module, abstract
action law, or global loop-commutation homotopy is used in these proofs.
-/
/-! Implementation provenance: `Quillen/Topology/HomotopyGroups/LoopNormalizationProduct.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining actual paths and normalization. -/
@[expose] public section

noncomputable section
open CategoryTheory
open HomotopyGroup
open scoped Topology unitInterval
universe u v
namespace Topology.IdentityTrack
open HomotopyFiber
variable {X : Type u} [TopologicalSpace X] {x : X}
variable {Z : Type v} [TopologicalSpace Z]

private theorem loopPiOneComm (p : Path x x)
    (a b : HomotopyGroup.Pi 1 (Path x x) p) : a * b = b * a := by
  let e := HomotopyGroup.pi1MulEquivFundamentalGroup.trans (loopKOneNormalization p)
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

/-- Convert an actual loop-valued map using its displayed correction path. -/
def correctedClass (f : C(Z, Path x x)) (z : Z)
    (γ : Path (f z) (Path.refl x)) (a : HomotopyGroup.Pi 1 Z z) :=
  (loopShiftMulEquiv 0).symm (pathTransportMulEquiv γ 0 (piMap 0 f rfl a))

/-- Normalize the family by the inverse of its original base loop on the left. -/
def leftMap (f : C(Z, Path x x)) (z : Z) : C(Z, Path x x) :=
  (pathPrefix (f z).symm).comp f

/-- The original inverse-prefix cancellation corrects the normalized base loop. -/
def leftCap (f : C(Z, Path x x)) (z : Z) : Path (leftMap f z z) (Path.refl x) :=
  loopInversePrefixCancellation (f z)

/-- The original left normalization, correction and loop-degree shift. -/
def leftClass (f : C(Z, Path x x)) (z : Z) (a : HomotopyGroup.Pi 1 Z z) :=
  correctedClass (leftMap f z) z (leftCap f z) a

/-- Normalize the family by the inverse of its original base loop on the right. -/
def rightMap (f : C(Z, Path x x)) (z : Z) : C(Z, Path x x) :=
  ⟨fun w => (f w).trans (f z).symm,
    Path.continuous_trans.comp (f.continuous.prodMk continuous_const)⟩

/-- The corresponding genuine right cancellation, obtained by reversing the base loop. -/
def rightCap (f : C(Z, Path x x)) (z : Z) : Path (rightMap f z z) (Path.refl x) :=
  (loopInversePrefixCancellation (f z).symm).cast
    (by change (f z).trans (f z).symm = _; rw [Path.symm_symm]) rfl

/-- Right normalization with its displayed cancellation and loop-degree shift. -/
def rightClass (f : C(Z, Path x x)) (z : Z) (a : HomotopyGroup.Pi 1 Z z) :=
  correctedClass (rightMap f z) z (rightCap f z) a

private theorem correctedClass_homotopy {f g : C(Z, Path x x)} (H : f.Homotopy g)
    (z : Z) (γ : Path (f z) (Path.refl x)) (δ : Path (g z) (Path.refl x))
    (a : HomotopyGroup.Pi 1 Z z) : correctedClass f z γ a = correctedClass g z δ a :=
  congrArg (loopShiftMulEquiv 0).symm
    (DFunLike.congr_fun (piOne_homotopy_corrected H γ δ (loopPiOneComm (Path.refl x))) a)

private theorem leftEquiv_eq_prefix (p : Path x x) :
    (loopLeftTranslationEquiv p).toFun = pathPrefix p := by
  apply ContinuousMap.ext
  intro q
  exact loopLeftTranslationEquiv_apply p q

/-- Removing a fixed prefix commutes with the actual left normalization,
through the genuine associator and the translation inverse homotopy. -/
private def leftMap_prefix_homotopy (p : Path x x) (f : C(Z, Path x x)) (z : Z) :
    (leftMap ((pathPrefix p).comp f) z).Homotopy (leftMap f z) := by
  let e := loopLeftTranslationEquiv p
  have hi : e.invFun = pathPrefix p.symm :=
    (loopLeftTranslationEquiv_invFun p).trans (leftEquiv_eq_prefix p.symm)
  have he : e.toFun = pathPrefix p := leftEquiv_eq_prefix p
  let K : ((pathPrefix p.symm).comp (pathPrefix p)).Homotopy (ContinuousMap.id _) :=
    e.left_inv.some.cast (by rw [hi, he]) rfl
  let H := (pathPrefixAssociator (f z).symm p.symm).compContinuousMap
    ((pathPrefix p).comp f)
  let L := ((ContinuousMap.Homotopy.refl (pathPrefix (f z).symm)).comp K).compContinuousMap f
  exact (H.trans L).cast (by
    apply ContinuousMap.ext
    intro w
    change ((f z).symm.trans p.symm).trans (p.trans (f w)) =
      (p.trans (f z)).symm.trans (p.trans (f w))
    rw [Path.trans_symm]) rfl

/-- Fixed prefixes preserve normalized classes without an action-triviality assumption. -/
theorem leftClass_prefix (p : Path x x) (f : C(Z, Path x x)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    leftClass ((pathPrefix p).comp f) z a = leftClass f z a := by
  have h := DFunLike.congr_fun (piOne_homotopy_corrected (leftMap_prefix_homotopy p f z)
    (leftCap ((pathPrefix p).comp f) z) (leftCap f z)
    (loopPiOneComm (Path.refl x))) a
  exact congrArg (loopShiftMulEquiv 0).symm h

/-- Actual reversal exchanges left and right normalization and inverts the
one-higher class. The cancellation-path comparison is made inside the loop space. -/
theorem leftClass_reverse (f : C(Z, Path x x)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    leftClass (loopReversal.comp f) z a = (rightClass f z a)⁻¹ := by
  have he : leftMap (loopReversal.comp f) z = loopReversal.comp (rightMap f z) := by
    apply ContinuousMap.ext
    intro w
    change (f z).symm.symm.trans (f w).symm = ((f w).trans (f z).symm).symm
    rw [Path.trans_symm, Path.symm_symm]
  let H : (leftMap (loopReversal.comp f) z).Homotopy
      (loopReversal.comp (rightMap f z)) := (ContinuousMap.Homotopy.refl _).cast rfl he
  have hh := correctedClass_homotopy H z (leftCap (loopReversal.comp f) z)
    (loopReversalPath (rightCap f z)) a
  have ht : pathTransport (loopReversalPath (rightCap f z)) 1
      (HomotopyGroup.map (loopReversal.comp (rightMap f z)) rfl a) =
      HomotopyGroup.map loopReversal loopReversal_refl
        (pathTransport (rightCap f z) 1 (HomotopyGroup.map (rightMap f z) rfl a)) :=
    (congrArg (pathTransport (loopReversalPath (rightCap f z)) 1)
      (HomotopyGroup.map_comp (rightMap f z) rfl loopReversal rfl a)).trans
        (pathTransport_naturality_of_track loopReversal (rightCap f z)
          (loopReversalPath (rightCap f z)) rfl loopReversal_refl (fun _ => rfl) 1 _)
  exact hh.trans ((congrArg (loopShiftMulEquiv 0).symm ht).trans
    (loopShiftEquiv_symm_loopReversal 1 _))

private theorem reverse_reverse (f : C(Z, Path x x)) :
    loopReversal.comp (loopReversal.comp f) = f := by
  apply ContinuousMap.ext
  intro w
  exact Path.symm_symm (f w)

/-- Append one fixed original loop continuously. -/
def pathSuffix (p : Path x x) : C(Path x x, Path x x) :=
  ⟨fun q => q.trans p, Path.continuous_trans.comp (continuous_id.prodMk continuous_const)⟩

/-- Fixed suffixes preserve right-normalized classes by actual reversal of
fixed-prefix homotopies. -/
theorem rightClass_suffix (p : Path x x) (f : C(Z, Path x x)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    rightClass ((pathSuffix p).comp f) z a = rightClass f z a := by
  apply inv_injective
  rw [← leftClass_reverse, ← leftClass_reverse]
  have he : loopReversal.comp ((pathSuffix p).comp f) =
      (pathPrefix p.symm).comp (loopReversal.comp f) := by
    apply ContinuousMap.ext
    intro w
    exact Path.trans_symm (f w) p
  rw [he]
  exact leftClass_prefix p.symm (loopReversal.comp f) z a

/-- The displayed inverse-prefix map and cap are exactly the original
K-one normalization, including the original fundamental-group comparison. -/
theorem leftClass_eq_normalization (f : C(Z, Path x x)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    leftClass f z a = loopKOneNormalization (f z)
      (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)) := by
  have hfg : HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)) =
        piMap 0 f rfl a := by
    apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
    rw [MulEquiv.apply_symm_apply]
    change FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a) =
      HomotopyGroup.pi1MulEquivFundamentalGroup (HomotopyGroup.map f rfl a)
    rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
    apply End.ext
    simp only [FundamentalGroup.map_apply_asHom, FundamentalGroup.mapOfEq_apply,
      Path.Homotopic.Quotient.cast_rfl_rfl]
  change (loopShiftMulEquiv 0).symm
    (pathTransport (loopInversePrefixCancellation (f z)) 1
      (piMap 0 (leftMap f z) rfl a)) =
    (loopShiftMulEquiv 0).symm
      (pathTransport (loopInversePrefixCancellation (f z)) 1
        (piMap 0 (loopLeftTranslationEquiv (f z).symm).toFun
          (loopLeftTranslationEquiv_apply _ _)
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
            (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)))))
  rw [hfg]
  apply congrArg (loopShiftMulEquiv 0).symm
  apply congrArg (pathTransport (loopInversePrefixCancellation (f z)) 1)
  exact (HomotopyGroup.map_comp f rfl (pathPrefix (f z).symm) rfl a).trans
    (congrFun (homotopyGroupMap_congr (leftEquiv_eq_prefix (f z).symm)
      (loopLeftTranslationEquiv_apply _ _) rfl) (piMap 0 f rfl a)).symm

private def leftMap_nullHomotopy (f : C(Z, Path x x)) (z : Z)
    (γ : Path (f z) (Path.refl x)) : (leftMap f z).Homotopy f := by
  let g : C(Z, Path x x) := ⟨fun w => (Path.refl x).trans (f w), by fun_prop⟩
  let H : (leftMap f z).Homotopy g := {
    toFun := fun a => (γ a.1).symm.trans (f a.2)
    continuous_toFun := Path.continuous_trans.comp
      ((Path.continuous_symm.comp (γ.continuous.comp continuous_fst)).prodMk
        (f.continuous.comp continuous_snd))
    map_zero_left := by intro w; change (γ 0).symm.trans (f w) = _; rw [γ.source]; rfl
    map_one_left := by intro w; change (γ 1).symm.trans (f w) = _; rw [γ.target]; rfl }
  let K : g.Homotopy f := {
    toFun := fun a => Path.delayReflLeft a.1 (f a.2)
    continuous_toFun := Path.continuous_delayReflLeft.comp
      (continuous_fst.prodMk (f.continuous.comp continuous_snd))
    map_zero_left := fun w => Path.delayReflLeft_zero (f w)
    map_one_left := fun w => Path.delayReflLeft_one (f w) }
  exact H.trans K

private theorem leftClass_eq_corrected_of_homotopy {f g : C(Z, Path x x)}
    (H : f.Homotopy g) (z : Z) (γ : Path (g z) (Path.refl x))
    (a : HomotopyGroup.Pi 1 Z z) : leftClass f z a = correctedClass g z γ a := by
  let δ := (H.evalAt z).trans γ
  exact (correctedClass_homotopy (leftMap_nullHomotopy f z δ) z (leftCap f z) δ a).trans
    (correctedClass_homotopy H z δ γ a)

private theorem leftClass_natural {Y : Type u} [TopologicalSpace Y] {y : Y}
    (g : C(X, Y)) (hg : g x = y) (f : C(Z, Path x x)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    HomotopyGroup.map g hg (leftClass f z a) =
      leftClass ((basedLoopMap g hg).comp f) z a := by
  have ht := loopKOneNormalization_naturality g hg (f z)
    (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a))
  have hcomp : FundamentalGroup.mapOfEq (basedLoopMap g hg) rfl
      (FundamentalGroup.map f z (HomotopyGroup.pi1MulEquivFundamentalGroup a)) =
      FundamentalGroup.map ((basedLoopMap g hg).comp f) z
        (HomotopyGroup.pi1MulEquivFundamentalGroup a) := by
    apply End.ext
    simp only [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply_asHom,
      Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  rw [hcomp] at ht
  exact (congrArg (HomotopyGroup.map g hg) (leftClass_eq_normalization f z a)).trans
    (ht.trans (leftClass_eq_normalization ((basedLoopMap g hg).comp f) z a).symm)

private def cutHead (p : Path x x) (t : unitInterval) : Path x (p t) where
  toFun s := p (t * s)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private def cutTail (p : Path x x) (t : unitInterval) : Path (p t) x where
  toFun s := p (unitInterval.symm (unitInterval.symm t * unitInterval.symm s))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

private def cutLoop (p q : Path x x) (t : unitInterval) : Path (p t) (p t) :=
  ((cutTail p t).trans q).trans (cutHead p t)

private theorem cutLoop_continuous (p : Path x x) :
    Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      cutLoop p z.1.2 z.1.1 z.2) := by
  have ht : Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      cutTail p z.1.1 z.2) := by
    change Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      p (unitInterval.symm (unitInterval.symm z.1.1 * unitInterval.symm z.2)))
    fun_prop
  have hq : Continuous (fun z : (unitInterval × Path x x) × unitInterval => z.1.2 z.2) := by
    fun_prop
  have hh : Continuous (fun z : (unitInterval × Path x x) × unitInterval =>
      cutHead p z.1.1 z.2) := by
    change Continuous (fun z : (unitInterval × Path x x) × unitInterval => p (z.1.1 * z.2))
    fun_prop
  exact Path.trans_continuous_family
    (fun z : unitInterval × Path x x => (cutTail p z.1).trans z.2)
    (Path.trans_continuous_family (fun z : unitInterval × Path x x => cutTail p z.1) ht
      (fun z : unitInterval × Path x x => z.2) hq)
    (fun z : unitInterval × Path x x => cutHead p z.1) hh

private def cutLoopMap (p : Path x x) : C((unitInterval × Path x x) × unitInterval, X) :=
  ⟨fun z => cutLoop p z.1.2 z.1.1 z.2, cutLoop_continuous p⟩

/-- Moving the cut through p gives loops in the actual free-path space,
whose basepoint is the whole displayed path p. -/
private def cutFamily (p : Path x x) :
    C(Path x x, Path p.toContinuousMap p.toContinuousMap) where
  toFun (q : Path x x) := {
    toFun (s : unitInterval) := (cutLoopMap p).comp
      ⟨fun t : unitInterval => ((t, q), s), by fun_prop⟩
    continuous_toFun := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun st : unitInterval × unitInterval => cutLoopMap p ((st.2, q), st.1))
      exact (cutLoopMap p).continuous.comp (by fun_prop)
    source' := by ext t; exact (cutLoop p q t).source
    target' := by ext t; exact (cutLoop p q t).target }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (Path x x × unitInterval) × unitInterval =>
      cutLoopMap p ((z.2, z.1.1), z.1.2))
    exact (cutLoopMap p).continuous.comp (by fun_prop)

private theorem cutFamily_zero (p q : Path x x) :
    basedLoopMap (freePathEvaluation X 0) p.source (cutFamily p q) =
      (p.trans q).trans (Path.refl x) := by
  ext s
  change cutLoop p q 0 s = _
  simp [cutLoop, cutHead, cutTail, Path.trans_apply]

private theorem cutFamily_one (p q : Path x x) :
    basedLoopMap (freePathEvaluation X 1) p.target (cutFamily p q) =
      ((Path.refl x).trans q).trans p := by
  ext s
  change cutLoop p q 1 s = _
  simp [cutLoop, cutHead, cutTail, Path.trans_apply]

private def cutCore (f : C(Z, Path x x)) (z : Z) :
    C(Z, Path (f z).symm.toContinuousMap (f z).symm.toContinuousMap) :=
  (cutFamily (f z).symm).comp f

private def cutZero (f : C(Z, Path x x)) (z : Z) : C(Z, Path x x) :=
  (basedLoopMap (freePathEvaluation X 0) (f z).symm.source).comp (cutCore f z)

private def cutOne (f : C(Z, Path x x)) (z : Z) : C(Z, Path x x) :=
  (basedLoopMap (freePathEvaluation X 1) (f z).symm.target).comp (cutCore f z)

private def cutZeroHomotopy (f : C(Z, Path x x)) (z : Z) :
    (cutZero f z).Homotopy (leftMap f z) where
  toFun a := Path.delayReflRight a.1 ((f z).symm.trans (f a.2))
  continuous_toFun := Path.continuous_delayReflRight.comp
    (continuous_fst.prodMk (Path.continuous_trans.comp
      (continuous_const.prodMk (f.continuous.comp continuous_snd))))
  map_zero_left w := by
    rw [Path.delayReflRight_zero]
    exact (cutFamily_zero (f z).symm (f w)).symm
  map_one_left w := Path.delayReflRight_one _

private def cutOneHomotopy (f : C(Z, Path x x)) (z : Z) :
    (cutOne f z).Homotopy (rightMap f z) where
  toFun a := (Path.delayReflLeft a.1 (f a.2)).trans (f z).symm
  continuous_toFun := Path.continuous_trans.comp
    ((Path.continuous_delayReflLeft.comp
      (continuous_fst.prodMk (f.continuous.comp continuous_snd))).prodMk continuous_const)
  map_zero_left w := by
    rw [Path.delayReflLeft_zero]
    exact (cutFamily_one (f z).symm (f w)).symm
  map_one_left w := by rw [Path.delayReflLeft_one]; rfl

/-- Free-path evaluation identifies the actual normalization-order difference
with transport around the reversed original base loop. -/
theorem rightClass_action (f : C(Z, Path x x)) (z : Z)
    (a : HomotopyGroup.Pi 1 Z z) :
    rightClass f z a = pathTransport (f z).symm 2 (leftClass f z a) := by
  let b := leftClass (cutCore f z) z a
  have ht := pathTransport_homotopyGroupMap_start (f z).symm 2 b
  have h0 : HomotopyGroup.map (freePathEvaluation X 0) (f z).symm.source b =
      leftClass f z a :=
    (leftClass_natural (freePathEvaluation X 0) (f z).symm.source (cutCore f z) z a).trans
      (leftClass_eq_corrected_of_homotopy (cutZeroHomotopy f z) z (leftCap f z) a)
  have h1 : HomotopyGroup.map (freePathEvaluation X 1) (f z).symm.target b =
      rightClass f z a :=
    (leftClass_natural (freePathEvaluation X 1) (f z).symm.target (cutCore f z) z a).trans
      (leftClass_eq_corrected_of_homotopy (cutOneHomotopy f z) z (rightCap f z) a)
  rw [h0, h1] at ht
  exact ht.symm

/-- Triviality is used for the actual object-loop action on Pi two. -/
theorem rightClass_eq_leftClass
    (hs : ∀ p : Path x x, ∀ a : HomotopyGroup.Pi 2 X x, pathTransport p 2 a = a)
    (f : C(Z, Path x x)) (z : Z) (a : HomotopyGroup.Pi 1 Z z) :
    rightClass f z a = leftClass f z a := (rightClass_action f z a).trans (hs _ _)

/-- Actual right-normalized classes are invariant under fixed prefixes in a simple space. -/
theorem rightClass_prefix
    (hs : ∀ p : Path x x, ∀ a : HomotopyGroup.Pi 2 X x, pathTransport p 2 a = a)
    (p : Path x x) (f : C(Z, Path x x)) (z : Z) (a : HomotopyGroup.Pi 1 Z z) :
    rightClass ((pathPrefix p).comp f) z a = rightClass f z a :=
  (rightClass_eq_leftClass hs _ z a).trans
    ((leftClass_prefix p f z a).trans (rightClass_eq_leftClass hs f z a).symm)

/-- Fixed-base normalized classes retain the original group law. -/
def rightClassHom (f : C(Z, Path x x)) (z : Z) :
    HomotopyGroup.Pi 1 Z z →* HomotopyGroup.Pi 2 X x :=
  (loopShiftMulEquiv 0).symm.toMonoidHom.comp
    ((pathTransportMulEquiv (rightCap f z) 0).toMonoidHom.comp (piMap 0 (rightMap f z) rfl))

/-- Precomposition retains the original induced fundamental-group map. -/
theorem rightClass_comp {A : Type*} [TopologicalSpace A]
    (f : C(Z, Path x x)) (g : C(A, Z)) (z : A) (a : HomotopyGroup.Pi 1 A z) :
    rightClass (f.comp g) z a = rightClass f (g z) (piMap 0 g rfl a) :=
  congrArg (loopShiftMulEquiv 0).symm
    (congrArg (pathTransport (rightCap f (g z)) 1)
      (HomotopyGroup.map_comp g rfl (rightMap f (g z)) rfl a))

private theorem piOne_pair_axes {A B D : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]
    (f : C(A, B)) (g : C(A, D)) (z : A) (a : HomotopyGroup.Pi 1 A z) :
    piMap 0 (f.prodMk g) (y := (f z, g z)) rfl a =
      piMap 0 (f.prodMk (ContinuousMap.const A (g z))) (y := (f z, g z)) rfl a *
        piMap 0 ((ContinuousMap.const A (f z)).prodMk g) (y := (f z, g z)) rfl a := by
  apply (piProdEquiv 0 (f z) (g z)).injective
  rw [map_mul]
  have h0f : piMap 0 ContinuousMap.fst (x := (f z, g z)) (y := f z) rfl
      (piMap 0 (f.prodMk g) (y := (f z, g z)) rfl a) = piMap 0 f rfl a :=
    (HomotopyGroup.map_comp (f.prodMk g) (y := (f z, g z)) rfl
      ContinuousMap.fst (z := f z) rfl a).symm
  have h1f : piMap 0 ContinuousMap.fst (x := (f z, g z)) (y := f z) rfl
      (piMap 0 (f.prodMk (ContinuousMap.const A (g z))) (y := (f z, g z)) rfl a) =
        piMap 0 f rfl a :=
    (HomotopyGroup.map_comp (f.prodMk (ContinuousMap.const A (g z)))
      (y := (f z, g z)) rfl ContinuousMap.fst (z := f z) rfl a).symm
  have h2f : piMap 0 ContinuousMap.fst (x := (f z, g z)) (y := f z) rfl
      (piMap 0 ((ContinuousMap.const A (f z)).prodMk g) (y := (f z, g z)) rfl a) = 1 :=
    (HomotopyGroup.map_comp ((ContinuousMap.const A (f z)).prodMk g)
      (y := (f z, g z)) rfl ContinuousMap.fst (z := f z) rfl a).symm.trans
        (DFunLike.congr_fun (piMap_const 0 (X := A) (y := f z)) a)
  have h0g : piMap 0 ContinuousMap.snd (x := (f z, g z)) (y := g z) rfl
      (piMap 0 (f.prodMk g) (y := (f z, g z)) rfl a) = piMap 0 g rfl a :=
    (HomotopyGroup.map_comp (f.prodMk g) (y := (f z, g z)) rfl
      ContinuousMap.snd (z := g z) rfl a).symm
  have h1g : piMap 0 ContinuousMap.snd (x := (f z, g z)) (y := g z) rfl
      (piMap 0 (f.prodMk (ContinuousMap.const A (g z))) (y := (f z, g z)) rfl a) = 1 :=
    (HomotopyGroup.map_comp (f.prodMk (ContinuousMap.const A (g z)))
      (y := (f z, g z)) rfl ContinuousMap.snd (z := g z) rfl a).symm.trans
        (DFunLike.congr_fun (piMap_const 0 (X := A) (y := g z)) a)
  have h2g : piMap 0 ContinuousMap.snd (x := (f z, g z)) (y := g z) rfl
      (piMap 0 ((ContinuousMap.const A (f z)).prodMk g) (y := (f z, g z)) rfl a) =
        piMap 0 g rfl a :=
    (HomotopyGroup.map_comp ((ContinuousMap.const A (f z)).prodMk g)
      (y := (f z, g z)) rfl ContinuousMap.snd (z := g z) rfl a).symm
  apply Prod.ext
  · exact h0f.trans ((mul_one _).symm.trans (congrArg₂ (· * ·) h1f.symm h2f.symm))
  · exact h0g.trans ((one_mul _).symm.trans (congrArg₂ (· * ·) h1g.symm h2g.symm))

/-- Split the actual product fundamental group into its two axes. Right-axis
invariance is geometric; left-axis invariance uses the original Pi-two action. -/
theorem rightClass_product
    (hs : ∀ p : Path x x, ∀ a : HomotopyGroup.Pi 2 X x, pathTransport p 2 a = a)
    (f g : C(Z, Path x x)) (z : Z) (a : HomotopyGroup.Pi 1 Z z) :
    rightClass (loopProduct f g) z a = rightClass f z a * rightClass g z a := by
  let M : C(Path x x × Path x x, Path x x) :=
    ⟨fun w => w.1.trans w.2, Path.continuous_trans⟩
  have h := congrArg (rightClassHom M (f z, g z)) (piOne_pair_axes f g z a)
  rw [map_mul] at h
  change rightClass M (f z, g z) (piMap 0 (f.prodMk g) (y := (f z, g z)) rfl a) =
    rightClass M (f z, g z)
        (piMap 0 (f.prodMk (ContinuousMap.const Z (g z))) (y := (f z, g z)) rfl a) *
      rightClass M (f z, g z)
        (piMap 0 ((ContinuousMap.const Z (f z)).prodMk g) (y := (f z, g z)) rfl a) at h
  have hc0 := rightClass_comp M (f.prodMk g) z a
  have hc1 := rightClass_comp M (f.prodMk (ContinuousMap.const Z (g z))) z a
  have hc2 := rightClass_comp M ((ContinuousMap.const Z (f z)).prodMk g) z a
  have hh := hc0.trans (h.trans (congrArg₂ (· * ·) hc1.symm hc2.symm))
  change rightClass (loopProduct f g) z a =
    rightClass ((pathSuffix (g z)).comp f) z a *
      rightClass ((pathPrefix (f z)).comp g) z a at hh
  exact hh.trans (congrArg₂ (· * ·) (rightClass_suffix (g z) f z a)
    (rightClass_prefix hs (f z) g z a))

/-- Source multiplication of the whole loop family is additive after the
original Pi-two action has been proved trivial. -/
theorem leftClass_product
    (hs : ∀ p : Path x x, ∀ a : HomotopyGroup.Pi 2 X x, pathTransport p 2 a = a)
    (f g : C(Z, Path x x)) (z : Z) (a : HomotopyGroup.Pi 1 Z z) :
    leftClass (loopProduct f g) z a = leftClass f z a * leftClass g z a :=
  (rightClass_eq_leftClass hs _ z a).symm.trans
    ((rightClass_product hs f g z a).trans
      (congrArg₂ (· * ·) (rightClass_eq_leftClass hs f z a)
        (rightClass_eq_leftClass hs g z a)))

/-- The actual normalized product of two loop self-tracks is the product
of their normalized classes, with no change of cap convention. -/
theorem normalization_product
    (hs : ∀ p : Path x x, ∀ a : HomotopyGroup.Pi 2 X x, pathTransport p 2 a = a)
    (p q : Path x x) (α : Path p p) (β : Path q q) :
    loopKOneNormalization (p.trans q)
      (FundamentalGroup.fromPath ⟦(α.prod β).map
        (loopProduct (ContinuousMap.fst : C(Path x x × Path x x, Path x x))
        ContinuousMap.snd).continuous⟧) =
      loopKOneNormalization p (FundamentalGroup.fromPath ⟦α⟧) *
        loopKOneNormalization q (FundamentalGroup.fromPath ⟦β⟧) := by
  let a : HomotopyGroup.Pi 1 (Path x x × Path x x) (p, q) :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm (FundamentalGroup.fromPath ⟦α.prod β⟧)
  have h := leftClass_product hs
    (ContinuousMap.fst : C(Path x x × Path x x, Path x x)) ContinuousMap.snd (p, q) a
  rw [leftClass_eq_normalization, leftClass_eq_normalization, leftClass_eq_normalization] at h
  change loopKOneNormalization (p.trans q)
      (FundamentalGroup.map (loopProduct ContinuousMap.fst ContinuousMap.snd) (p, q)
        (HomotopyGroup.pi1MulEquivFundamentalGroup
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
            (FundamentalGroup.fromPath ⟦α.prod β⟧)))) =
    loopKOneNormalization p (FundamentalGroup.map ContinuousMap.fst (p, q)
        (HomotopyGroup.pi1MulEquivFundamentalGroup
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
            (FundamentalGroup.fromPath ⟦α.prod β⟧)))) *
      loopKOneNormalization q (FundamentalGroup.map ContinuousMap.snd (p, q)
        (HomotopyGroup.pi1MulEquivFundamentalGroup
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
            (FundamentalGroup.fromPath ⟦α.prod β⟧)))) at h
  simp only [MulEquiv.apply_symm_apply] at h
  have hf : FundamentalGroup.map ContinuousMap.fst (p, q)
      (FundamentalGroup.fromPath ⟦α.prod β⟧) = FundamentalGroup.fromPath ⟦α⟧ := by
    apply End.ext
    rfl
  have hg : FundamentalGroup.map ContinuousMap.snd (p, q)
      (FundamentalGroup.fromPath ⟦α.prod β⟧) = FundamentalGroup.fromPath ⟦β⟧ := by
    apply End.ext
    rfl
  rw [hf, hg] at h
  exact h

end Topology.IdentityTrack

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyGroups/LoopNormalizationProduct.lean:48-498"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  Topology.IdentityTrack.correctedClass
  Topology.IdentityTrack.leftMap
  Topology.IdentityTrack.leftCap
  Topology.IdentityTrack.leftClass
  Topology.IdentityTrack.rightMap
  Topology.IdentityTrack.rightCap
  Topology.IdentityTrack.rightClass
  Topology.IdentityTrack.leftClass_prefix
  Topology.IdentityTrack.leftClass_reverse
  Topology.IdentityTrack.pathSuffix
  Topology.IdentityTrack.rightClass_suffix
  Topology.IdentityTrack.leftClass_eq_normalization
  Topology.IdentityTrack.rightClass_action
  Topology.IdentityTrack.rightClass_eq_leftClass
  Topology.IdentityTrack.rightClass_prefix
  Topology.IdentityTrack.rightClassHom
  Topology.IdentityTrack.rightClass_comp
  Topology.IdentityTrack.loopProduct
  Topology.IdentityTrack.rightClass_product
  Topology.IdentityTrack.leftClass_product
  Topology.IdentityTrack.normalization_product
