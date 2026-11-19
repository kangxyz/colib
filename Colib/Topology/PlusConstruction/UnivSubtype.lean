/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Homeomorph
public import Colib.Topology.LocalCoefficients.HomotopySquareChains
public import Colib.Topology.LocalCoefficients.UniverseLiftQuasiIso
public import Colib.Topology.PlusConstruction.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-! # Exact plus-certificate transport to the whole-space subtype

The canonical homeomorphism identifies a space X with its whole-space subtype. It retains
the original map, based path and subgroup through the canonical homeomorphism.
All coefficient conversions are the existing actual equivalence-square maps.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory FundamentalGroupoid FundamentalGroupoid.LocalCoefficients
universe u
namespace Topology.PlusConstruction.UnivSubtype
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The canonical continuous inclusion into the whole-space subtype. -/
def up (X : Type u) [TopologicalSpace X] : C(X, (Set.univ : Set X)) :=
  (Homeomorph.Set.univ X).symm.toHomotopyEquiv.toFun

/-- The literal original value of a whole-space subtype point. -/
def down (X : Type u) [TopologicalSpace X] : C((Set.univ : Set X), X) :=
  (Homeomorph.Set.univ X).toHomotopyEquiv.toFun

/-- The original map, with only the whole-space subtype wrappers inserted. -/
def map (f : C(X, Y)) : C((Set.univ : Set X), (Set.univ : Set Y)) :=
  (up Y).comp (f.comp (down X))

/-- The original induced Pi-one map is a multiplicative equivalence. -/
def piEquiv (x : X) :
    HomotopyGroup.Pi 1 X x ≃*
      HomotopyGroup.Pi 1 (Set.univ : Set X) (up X x) :=
  HomotopyGroup.homeomorphPiEquiv (Homeomorph.Set.univ X).symm rfl 0

/-- Transport the specified original subgroup by the displayed induced map. -/
def liftSubgroup {x : X} (N : Subgroup (HomotopyGroup.Pi 1 X x)) :
    Subgroup (HomotopyGroup.Pi 1 (Set.univ : Set X) (up X x)) :=
  N.map (piEquiv x).toMonoidHom

variable (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y)

/-- The original chosen basepoint path with its literal subtype wrapper. -/
def liftPath : Path (map f (up X x)) (up Y y) := γ.map (up Y).continuous

/-- Every time of the original basepoint track is retained. -/
theorem liftPath_apply (t : unitInterval) : liftPath f γ t = up Y (γ t) := rfl

/-- The based nonabelian square retains the actual supplied path transport. -/
theorem basedPiOneMap_lift_apply (a : HomotopyGroup.Pi 1 X x) :
    basedPiOneMap (map f) (liftPath f γ) (piEquiv x a) =
      piEquiv y (basedPiOneMap f γ a) := by
  change pathTransport (γ.map (up Y).continuous) 1
      (HomotopyGroup.map (map f) rfl (HomotopyGroup.map (up X) rfl a)) =
    HomotopyGroup.map (up Y) rfl (pathTransport γ 1 (HomotopyGroup.map f rfl a))
  have hm : HomotopyGroup.map (map f) rfl (HomotopyGroup.map (up X) rfl a) =
      HomotopyGroup.map (up Y) rfl (HomotopyGroup.map f rfl a) := by
    refine Quotient.inductionOn a (fun _ ↦ ?_)
    rfl
  exact (congrArg (pathTransport (γ.map (up Y).continuous) 1) hm).trans
    (pathTransport_naturality (up Y) γ 1 (HomotopyGroup.map f rfl a))

/-- The lifted original based map is surjective when the original one is. -/
theorem basedPiOneMap_lift_surjective (h : Function.Surjective (basedPiOneMap f γ)) :
    Function.Surjective (basedPiOneMap (map f) (liftPath f γ)) := by
  intro b
  obtain ⟨b, rfl⟩ := (piEquiv y).surjective b
  obtain ⟨a, rfl⟩ := h b
  exact ⟨piEquiv x a, basedPiOneMap_lift_apply f γ a⟩

/-- The original kernel is transported by the actual Pi-one equivalence. -/
theorem kernel_lift :
    (basedPiOneMap (map f) (liftPath f γ)).ker = liftSubgroup (basedPiOneMap f γ).ker := by
  ext b
  obtain ⟨a, rfl⟩ := (piEquiv x).surjective b
  change _ ↔ piEquiv x a ∈ (basedPiOneMap f γ).ker.map (piEquiv x).toMonoidHom
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  change basedPiOneMap (map f) (liftPath f γ) (piEquiv x a) = 1 ↔ basedPiOneMap f γ a = 1
  rw [basedPiOneMap_lift_apply]
  constructor
  · intro h
    apply (piEquiv y).injective
    simpa only [map_one] using h
  · intro h
    rw [h, map_one]

/-- The exact whole-space subtype certificate follows from the original certificate. -/
theorem isPlusConstruction (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (h : IsPlusConstruction.{u, u, u} f γ N) :
    IsPlusConstruction.{u, u, u} (map f) (liftPath f γ) (liftSubgroup N) := by
  let := h.sourcePathConnected
  let := h.targetPathConnected
  let := h.perfect
  refine {
    sourcePathConnected := (Homeomorph.Set.univ X).symm.pathConnectedSpace
    targetPathConnected := (Homeomorph.Set.univ Y).symm.pathConnectedSpace
    perfect := Group.IsPerfect.map (piEquiv x).toMonoidHom
    surjective := basedPiOneMap_lift_surjective f γ h.surjective
    kernelEq := by rw [kernel_lift, h.kernelEq]
    localCoefficients := ?_ }
  intro A
  apply (UniverseLift.quasiIso_chainMap_iff (map f) A).mpr
  apply pushforwardChainMap_quasiIso_of_equivalence_square
    (Homeomorph.Set.univ X).toHomotopyEquiv
    (Homeomorph.Set.univ Y).toHomotopyEquiv f (map f) rfl
  intro V
  exact (UniverseLift.quasiIso_chainMap_iff f V).mp (h.localCoefficients V)

/-- Removing both subtype wrappers returns the original spatial map exactly. -/
theorem forward_down : (down Y).comp ((map f).comp (up X)) = f := rfl

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/UnivSubtype.lean:113-132"
  "adaptation" "The original coefficient certificate transported to the whole-space subtype"]
  isPlusConstruction

end Topology.PlusConstruction.UnivSubtype
