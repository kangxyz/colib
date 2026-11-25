/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Homotopy.OpenCover.TransParameters
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedRectangle

/-!
# Whole positive rails recovered from the original full rectangle

Factor extraction uses exact half-interval substitutions, including the shared midpoint.
Both sheets retain their own carrier points; their common native images do not identify tips.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace FundamentalGroupoid.OpenCover
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedRails
open CommonReferenceNerve InputIdentitySeedCarrier InputIdentitySeedRectangle
private theorem left_factor {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b c : A} {a' b' c' : B} (ev : A → B)
    (p : Path a b) (q : Path b c) (P : Path a' b') (Q : Path b' c')
    (h : ∀ t, ev ((p.trans q) t) = (P.trans Q) t) (s : I) :
    ev (p s) = P s := by
  have h' := h (leftHalf s)
  simpa only [trans_leftHalf] using h'

private theorem right_factor {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b c : A} {a' b' c' : B} (ev : A → B)
    (p : Path a b) (q : Path b c) (P : Path a' b') (Q : Path b' c')
    (h : ∀ t, ev ((p.trans q) t) = (P.trans Q) t) (s : I) :
    ev (q s) = Q s := by
  have h' := h (rightHalf s)
  simpa only [trans_rightHalf] using h'

private theorem unreverse {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b : A} {a' b' : B} (ev : A → B) (p : Path a b) (P : Path a' b')
    (h : ∀ t, ev (p.symm t) = P.symm t) (s : I) : ev (p s) = P s := by
  have h' := h (unitInterval.symm s)
  change ev (p (unitInterval.symm (unitInterval.symm s))) =
    P (unitInterval.symm (unitInterval.symm s)) at h'
  simpa only [unitInterval.symm_symm] using h'

private theorem carrier_path_apply {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) (s : I) : p.toContinuousMap s = p s := rfl

private theorem native_path_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : LoopPrespectrum.Homotopy f g) (n : ℕ) (x : E.space n) (s : I) :
    H.path n x s = H.level n (s, x) := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (e : Bool)

/-- The entire sheet source boundary word has its original native image. -/
theorem source_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (((positiveMovement g e).trans (polynomialMovement g e)) s) x =
      (((InputIdentityPositiveNull.positiveMovement g).path n x).trans
        ((InputIdentityPositiveNull.polynomialMovement g).path n x)) s := by
  have h := rectangle_native g e n 0 s x
  change CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g) n ((rectangle g e).toFun (0, s)) x = _ at h
  rw [(rectangle g e).map_zero_left s] at h
  have hb := ((InputIdentityPositiveNull.positivePasting g).level n).apply_zero
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- The entire sheet target boundary word has its original native image. -/
theorem target_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (((oldPositive g e).symm.trans ((laurentMovement g e).trans
    (newPositive g e))) s) x =
      (((InputIdentityPositiveNull.oldPositive g).path n x).symm.trans
        (((InputIdentityPositiveNull.laurentMovement g).path n x).trans
        ((InputIdentityPositiveNull.newPositive g).path n x))) s := by
  have h := rectangle_native g e n 1 s x
  change CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
    (ordinary g) (shifted g) n ((rectangle g e).toFun (1, s)) x = _ at h
  rw [(rectangle g e).map_one_left s] at h
  have hb := ((InputIdentityPositiveNull.positivePasting g).level n).apply_one
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- Every point of either positiveMovement rail has its original native value. -/
theorem positiveMovement_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (positiveMovement g e s) x =
      (InputIdentityPositiveNull.positiveMovement g).level n (s, x) := by
  let ev := fun z : Carrier g ↦
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n z x
  change ev ((positiveMovement g e) s) = ((InputIdentityPositiveNull.positiveMovement
    g).path n x) s
  exact left_factor ev (positiveMovement g e) (polynomialMovement g e)
    ((InputIdentityPositiveNull.positiveMovement g).path n x)
    ((InputIdentityPositiveNull.polynomialMovement g).path n x)
    (fun t ↦ source_native g e n t x) s

/-- Every point of either oldPositive rail has its original native value. -/
theorem oldPositive_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (oldPositive g e s) x =
      (InputIdentityPositiveNull.oldPositive g).level n (s, x) := by
  let ev := fun z : Carrier g ↦
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n z x
  change ev ((oldPositive g e) s) = ((InputIdentityPositiveNull.oldPositive g).path n x) s
  have h := left_factor ev
    (oldPositive g e).symm ((laurentMovement g e).trans (newPositive g e))
    ((InputIdentityPositiveNull.oldPositive g).path n x).symm
    (((InputIdentityPositiveNull.laurentMovement g).path n x).trans
      ((InputIdentityPositiveNull.newPositive g).path n x))
    (fun t ↦ target_native g e n t x)
  exact unreverse ev (oldPositive g e)
    ((InputIdentityPositiveNull.oldPositive g).path n x) h s

/-- Every point of either laurentMovement rail has its original native value. -/
theorem laurentMovement_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (laurentMovement g e s) x =
      (InputIdentityPositiveNull.laurentMovement g).level n (s, x) := by
  let ev := fun z : Carrier g ↦
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n z x
  change ev ((laurentMovement g e) s) = ((InputIdentityPositiveNull.laurentMovement g).path n x) s
  have h := right_factor ev
    (oldPositive g e).symm ((laurentMovement g e).trans (newPositive g e))
    ((InputIdentityPositiveNull.oldPositive g).path n x).symm
    (((InputIdentityPositiveNull.laurentMovement g).path n x).trans
      ((InputIdentityPositiveNull.newPositive g).path n x))
    (fun t ↦ target_native g e n t x)
  exact left_factor ev
    (laurentMovement g e) (newPositive g e)
    ((InputIdentityPositiveNull.laurentMovement g).path n x)
    ((InputIdentityPositiveNull.newPositive g).path n x) h s

/-- Every point of either newPositive rail has its original native value. -/
theorem newPositive_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (newPositive g e s) x =
      (InputIdentityPositiveNull.newPositive g).level n (s, x) := by
  let ev := fun z : Carrier g ↦
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n z x
  change ev ((newPositive g e) s) = ((InputIdentityPositiveNull.newPositive g).path n x) s
  have h := right_factor ev
    (oldPositive g e).symm ((laurentMovement g e).trans (newPositive g e))
    ((InputIdentityPositiveNull.oldPositive g).path n x).symm
    (((InputIdentityPositiveNull.laurentMovement g).path n x).trans
      ((InputIdentityPositiveNull.newPositive g).path n x))
    (fun t ↦ target_native g e n t x)
  exact right_factor ev
    (laurentMovement g e) (newPositive g e)
    ((InputIdentityPositiveNull.laurentMovement g).path n x)
    ((InputIdentityPositiveNull.newPositive g).path n x) h s

/-- The whole polynomial rail retains the original cone-square seam on either sheet. -/
theorem polynomialMovement_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (polynomialMovement g e s) x =
      (InputIdentityPositiveNull.polynomialMovement g).level n (s, x) := by
  rw [polynomial_seam]
  exact (InputIdentitySeedCone.cylinder_native g e n s 0 x).trans
    ((InputIdentitySeedCone.nativeSquare g n x).left s)

/-- Endpoint retyping preserves every old cone value and its own actual tip. -/
theorem oldCone_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (oldCone g e s) x =
      (InputIdentityPositiveNull.oldCone g).level n (s, x) :=
  (InputIdentitySeedCone.cylinder_native g e n 0 s x).trans
    ((InputIdentitySeedCone.nativeSquare g n x).at_zero s)

/-- Endpoint retyping preserves every new cone value and its separately retained tip. -/
theorem newCone_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
      (ordinary g) (shifted g) n (newCone g e s) x =
      (InputIdentityPositiveNull.newCone g).level n (s, x) :=
  (InputIdentitySeedCone.cylinder_native g e n 1 s x).trans
    ((InputIdentitySeedCone.nativeSquare g n x).at_one s)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedRails
