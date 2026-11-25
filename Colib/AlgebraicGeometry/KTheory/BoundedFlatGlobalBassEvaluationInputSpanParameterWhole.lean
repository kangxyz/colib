/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSpanParameterAssoc
public import Colib.Topology.Prespectrum.CarrierCorrectedBoundaryEvaluation
public import Colib.Topology.Prespectrum.CarrierSquareDescentEvaluation

/-!
# The exact compact family of the original input-span cylinder

The entire selected boundary correction and its original collapse descend in the fixed mixed
reference. The native image is the actual input-span homotopy followed by raw comparison,
with all scalar, cylinder, native, and level-zero loop coordinates independent.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterWhole
open GlobalSectionChangeIndex InputSpanParameterWord InputSpanParameterCells InputSpanParameterAssoc

private theorem trans_values {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b : A} {a' b' : B} {p q z : Path a b} {p' q' z' : Path a' b'}
    (f : A → C) (h : B → C) (J : p.Homotopy q) (K : q.Homotopy z)
    (J' : p'.Homotopy q') (K' : q'.Homotopy z')
    (hJ : ∀ r s, f (J (r, s)) = h (J' (r, s)))
    (hK : ∀ r s, f (K (r, s)) = h (K' (r, s))) (r s : unitInterval) :
    f (J.trans K (r, s)) = h (J'.trans K' (r, s)) := by
  rw [Path.Homotopy.trans_apply, Path.Homotopy.trans_apply]
  split
  · exact hJ _ s
  · exact hK _ s

private theorem hcomp_values {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b c : A} {a' b' c' : B} {p q : Path a b} {w z : Path b c}
    {p' q' : Path a' b'} {w' z' : Path b' c'}
    (f : A → C) (h : B → C) (J : p.Homotopy q) (K : w.Homotopy z)
    (J' : p'.Homotopy q') (K' : w'.Homotopy z')
    (hJ : ∀ r s, f (J (r, s)) = h (J' (r, s)))
    (hK : ∀ r s, f (K (r, s)) = h (K' (r, s))) (r s : unitInterval) :
    f (J.hcomp K (r, s)) = h (J'.hcomp K' (r, s)) := by
  rw [Path.Homotopy.hcomp_apply, Path.Homotopy.hcomp_apply]
  split
  · exact hJ r _
  · exact hK r _

private theorem corrected_values {A Z : Type*} [TopologicalSpace A]
    {a₀ b₀ a₁ b₁ : A} {p₀ : Path a₀ b₀} {p₁ p₂ : Path a₁ b₁}
    {l : Path a₀ a₁} {m : Path b₀ b₁}
    {E F : LoopPrespectrum.{u}} {f₀ g₀ f₁ g₁ : E ⟶ F}
    {H₀ : Homotopy f₀ g₀} {H₁ H₂ : Homotopy f₁ g₁}
    {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁}
    (Q : Topology.CarrierPathSquare.Square p₀ p₁ l m) (J : p₁.Homotopy p₂)
    (S : H₀.Square H₁ L M) (R : H₁.RelHomotopy H₂)
    (n : ℕ) (x : E.space n) (f : A → Z) (c : F.space n → Z)
    (hQ : ∀ r s, f (Q.parameter (r, s)) = c (S.level n (r, (s, x))))
    (hJ : ∀ r s, f (J (r, s)) = c (R.level n (r, (s, x)))) (r s : unitInterval) :
    f ((Q.toBoundary.trans
      (((Path.Homotopy.refl l).hcomp J).hcomp (Path.Homotopy.refl m.symm))) (r, s)) =
      c ((Topology.CarrierPathSquare.nativeCorrectedBoundary S R).level n (r, (s, x))) := by
  have hL (t : unitInterval) : f (l t) = c (L.level n (t, x)) :=
    (congrArg f (Q.left t)).symm.trans ((hQ t 0).trans (congrArg c (S.left n t x)))
  have hM (t : unitInterval) : f (m t) = c (M.level n (t, x)) :=
    (congrArg f (Q.right t)).symm.trans ((hQ t 1).trans (congrArg c (S.right n t x)))
  have hB (t v : unitInterval) : f (Q.toBoundary (t, v)) =
      c (S.toBoundary.level n (t, (v, x))) :=
    (hQ (Topology.ThreeSideSquare.collapse (t, v)).1
      (Topology.ThreeSideSquare.collapse (t, v)).2).trans
        (congrArg c (S.toBoundary_apply n t v x).symm)
  have hC (t v : unitInterval) : f (((Path.Homotopy.refl l).hcomp J) (t, v)) =
      c (((Homotopy.RelHomotopy.refl L).hcomp R).level n (t, (v, x))) := by
    rw [Homotopy.RelHomotopy.hcomp_apply_path]
    exact hcomp_values f c _ _ _ _ (fun _ v => hL v) hJ t v
  have hD (t v : unitInterval) : f
      ((((Path.Homotopy.refl l).hcomp J).hcomp (Path.Homotopy.refl m.symm)) (t, v)) =
      c ((((Homotopy.RelHomotopy.refl L).hcomp R).hcomp
        (Homotopy.RelHomotopy.refl M.symm)).level n (t, (v, x))) := by
    rw [Homotopy.RelHomotopy.hcomp_apply_path]
    exact hcomp_values f c _ _ _ _ hC (fun _ v => hM (unitInterval.symm v)) t v
  unfold Topology.CarrierPathSquare.nativeCorrectedBoundary
  rw [Homotopy.RelHomotopy.trans_apply_path]
  exact trans_values f c _ _ _ _ hB hD r s

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Every point of the selected relative boundary retains the actual native corrected word. -/
theorem boundary_native (n : ℕ)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n)
      (r s : unitInterval) :
    ev g n x (InputSpanParameterWord.boundary g (r, s)) =
      (GlobalRawBass.comparison X).map n ((InputSpan.cylinderBoundary g).level n (r, (s, x))) :=
  corrected_values (movingSquare g) (reassociation g).symm
    (movingNative g) (reassociationNative g).symm n x (ev g n x)
    ((GlobalRawBass.comparison X).map n) (moving_native g n x)
    (fun t v => reassociation_native g n x (unitInterval.symm t) v) r s

/-- Original quotient descent preserves both scalar coordinates on every native input. -/
theorem parameter_native (n : ℕ)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n)
      (r s : unitInterval) :
    ev g n x (parameter g (r, s)) =
      (GlobalRawBass.comparison X).map n ((InputSpan.cylinderSquare g).level n (r, (s, x))) := by
  obtain ⟨z, hz⟩ := Topology.ThreeSideSquare.collapse_surjective (r, s)
  have hc := congrArg (ev g n x) (parameter_collapse g z)
  rw [hz] at hc
  have hn := (InputSpan.cylinderBoundary g).toSquare_collapse n z x
  rw [hz] at hn
  exact hc.trans ((boundary_native g n x z.1 z.2).trans
    (congrArg ((GlobalRawBass.comparison X).map n) hn.symm))

/-- The full continuous family is actual input-span evaluation followed by raw comparison. -/
theorem native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g) n =
    ((GlobalRawBass.comparison X).map n).comp
      (((inputSpanHomotopy g).level n).comp
        ⟨fun z ↦ (z.1.1, HomotopyPushout.cylinder
          (sectionMap (projection.app Y)) (sectionMap (projection.app Y)) n (z.1.2, z.2)),
          by fun_prop⟩) := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  exact (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (InputMixedDesc.sourceMap g) (parameter g) n (r, s) x).symm.trans
      ((parameter_native g n x r s).trans
        (congrArg ((GlobalRawBass.comparison X).map n)
          (inputSpanHomotopy_cylinder g n r s x).symm))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSpanParameterWhole
