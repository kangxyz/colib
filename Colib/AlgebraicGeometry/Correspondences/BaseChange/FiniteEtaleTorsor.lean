/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.FiniteEtale
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Galois

/-! # Descent of invariant cycles along a finite étale torsor

The two projections of the Čech fibre product evaluate an upstairs cycle at
the original point and its translate on each summand of the pinned Galois
comparison. This gives the invariance criterion for Riou's cycle descent in
*Opérations de Steenrod motiviques*, arXiv:1207.3121v1, Definition 2.1.3, map (4).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Descent Stacks.Descent.GaloisDescentData

universe u v w

namespace Stacks.Chow

variable {X Y : Scheme.{u}} {G : Type v} [Group G] [Finite G]
  {R : Type w} [AddCommMonoid R]

/-- Agreement on the two actual étale pullbacks is pointwise invariance under
the action on the cover. -/
theorem finiteEtaleCyclePullback_fst_eq_snd_iff (f : X ⟶ Y) [IsFinite f] [Etale f]
    (a : Gᵐᵒᵖ →* Aut (Over.mk f)) [IsIso (galoisCoverComparison f a)]
    (c : AlgebraicCycle X R) :
    finiteEtaleCyclePullback (pullback.fst f f) c =
        finiteEtaleCyclePullback (pullback.snd f f) c ↔
      ∀ (σ : G) (x : X), c (twist G f a σ x) = c x := by
  constructor
  · intro h σ x
    have hx : f x = f (twist G f a σ x) :=
      (congrArg (fun g : X ⟶ Y ↦ g x) (twist_comp G f a σ)).symm
    obtain ⟨z, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback x
      (twist G f a σ x) hx
    simpa only [finiteEtaleCyclePullback_apply, h₁, h₂] using
      (congrArg (fun d : AlgebraicCycle (pullback f f) R ↦ d z) h).symm
  · intro h
    obtain ⟨V, p, hp, g, hcover, h₁, h₂⟩ :=
      exists_openCover_twist f a (pullback.fst f f) (pullback.snd f f) pullback.condition
    ext z
    have hz : z ∈ ⨆ σ, (p σ).opensRange := by rw [hcover]; trivial
    obtain ⟨σ, hzσ⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    obtain ⟨x, rfl⟩ := hzσ
    change c (pullback.fst f f (p σ x)) = c (pullback.snd f f (p σ x))
    rw [← Scheme.Hom.comp_apply, h₁, ← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply]
    exact (h σ (g σ x)).symm

variable {S T : Scheme.{u}} (r : T ⟶ S)
  (U V : Scheme.SmoothSite S) [IsFinite r] [Etale r] [Surjective r]

local notation "b" => baseChangeCorrespondenceProductMap r U V

/-- For a torsor action on the actual base-changed ambient product, pointwise
invariance is equivalent to unique finite-correspondence descent. -/
theorem existsUnique_finiteEtaleBaseChangeCorrespondences_iff_invariant
    (a : Gᵐᵒᵖ →* Aut (Over.mk b)) [IsIso (galoisCoverComparison b a)]
    (c : finiteCorrespondences (pullback.snd U.hom r) (pullback.snd V.hom r)) :
    (∃! d : finiteCorrespondences U.hom V.hom, finiteEtaleBaseChangeCorrespondences r U V d = c) ↔
      ∀ (σ : G) (x : (pullback (pullback.snd U.hom r) (pullback.snd V.hom r) : Scheme.{u})),
        c.val (twist G b a σ x) = c.val x :=
  (existsUnique_finiteEtaleBaseChangeCorrespondences r U V c).trans
    (finiteEtaleCyclePullback_fst_eq_snd_iff b a c.val)

end Stacks.Chow
