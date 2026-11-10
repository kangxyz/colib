/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.CommonUniverseChains
public import Colib.Topology.PlusConstruction.Basic
public import Colib.Topology.Homotopy.HomotopyGroup.Homeomorph

/-! # Exact based transport of the original plus certificate to a common universe

The original map, path and subgroup are transported by the
actual ULift homeomorphisms. The coefficient hypothesis already ranges over
the common universe; no enlargement from smaller coefficients is asserted.
-/
@[expose] public section

open FundamentalGroupoid FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory
universe u v w
namespace Topology.PlusConstruction.CommonUniverse
open LocalCoefficients

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y)

/-! The spatial map is the existing `UniverseLift.map`; the Pi-one equivalence
is the existing `HomotopyGroup.homeomorphPiEquiv`. Subgroups and paths use native
`Subgroup.map` and `Path.map` directly, with no replacement model or alias. -/

/-- The complete based Pi-one square uses the originally specified path transport. -/
theorem basedPiOneMap_lift_apply (a : HomotopyGroup.Pi 1 X x) :
    basedPiOneMap (UniverseLift.map.{u, v, max u v w} f)
        (γ.map continuous_uliftUp) ((HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) (y := ULift.up x) rfl 0) a) =
      (HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, v} (X := Y)).symm (x := y)
        (y := ULift.up y) rfl 0) (basedPiOneMap f γ a) := by
  change pathTransport (γ.map continuous_uliftUp) 1
      (HomotopyGroup.map (UniverseLift.map.{u, v, max u v w} f) rfl
        (HomotopyGroup.map (UniverseLift.up X) rfl a)) =
    HomotopyGroup.map (UniverseLift.up Y) rfl
      (pathTransport γ 1 (HomotopyGroup.map f rfl a))
  have hm : HomotopyGroup.map (UniverseLift.map.{u, v, max u v w} f) rfl
      (HomotopyGroup.map (UniverseLift.up X) rfl a) =
        HomotopyGroup.map (UniverseLift.up Y) rfl (HomotopyGroup.map f rfl a) := by
    refine Quotient.inductionOn a (fun _ => ?_)
    rfl
  exact (congrArg (pathTransport (γ.map continuous_uliftUp) 1) hm).trans
    (pathTransport_naturality (UniverseLift.up Y) γ 1 (HomotopyGroup.map f rfl a))

/-- The based square is an equality of the original nonabelian group homomorphisms. -/
theorem basedPiOneMap_square :
    (basedPiOneMap (UniverseLift.map.{u, v, max u v w} f) (γ.map continuous_uliftUp)).comp
        ((HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x)
        (y := ULift.up x) rfl 0)).toMonoidHom =
      ((HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, v} (X := Y)).symm (x := y)
        (y := ULift.up y) rfl 0)).toMonoidHom.comp
        (basedPiOneMap f γ) := by
  ext a
  exact basedPiOneMap_lift_apply f γ a

/-- Surjectivity transfers through the displayed based square. -/
theorem basedPiOneMap_lift_surjective (h : Function.Surjective (basedPiOneMap f γ)) :
    Function.Surjective
      (basedPiOneMap (UniverseLift.map.{u, v, max u v w} f) (γ.map continuous_uliftUp)) := by
  intro b
  obtain ⟨b, rfl⟩ := ((HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, v} (X := Y)).symm (x := y)
        (y := ULift.up y) rfl 0)).surjective b
  obtain ⟨a, rfl⟩ := h b
  exact ⟨(HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) (y := ULift.up x) rfl 0) a,
    basedPiOneMap_lift_apply f γ a⟩

/-- The kernel is the image of the original kernel under the specified Pi-one equivalence. -/
theorem kernel_lift :
    (basedPiOneMap (UniverseLift.map.{u, v, max u v w} f) (γ.map continuous_uliftUp)).ker =
      (basedPiOneMap f γ).ker.map (HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x)
        (y := ULift.up x) rfl 0).toMonoidHom := by
  ext b
  obtain ⟨a, rfl⟩ := ((HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x)
        (y := ULift.up x) rfl 0)).surjective b
  change _ ↔ (HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) (y := ULift.up x) rfl 0) a ∈
    (basedPiOneMap f γ).ker.map ((HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) (y := ULift.up x) rfl 0)).toMonoidHom
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  change basedPiOneMap (UniverseLift.map.{u, v, max u v w} f)
      (γ.map continuous_uliftUp) ((HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) (y := ULift.up x) rfl 0) a) = 1 ↔
    basedPiOneMap f γ a = 1
  rw [basedPiOneMap_lift_apply]
  constructor
  · intro h
    apply ((HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, v} (X := Y)).symm (x := y) (y := ULift.up y) rfl 0)).injective
    simpa only [map_one] using h
  · intro h
    rw [h, map_one]

/-- The common-universe certificate retains the transported original map, path and subgroup. -/
theorem isPlusConstruction (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (h : IsPlusConstruction.{u, v, max u v w} f γ N) :
    IsPlusConstruction.{max u v w, max u v w, max u v w}
      (UniverseLift.map.{u, v, max u v w} f) (γ.map continuous_uliftUp)
      (N.map (HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x)
        (y := ULift.up x) rfl 0).toMonoidHom) := by
  let := h.sourcePathConnected
  let := h.targetPathConnected
  let := h.perfect
  exact {
    sourcePathConnected := Homeomorph.ulift.symm.pathConnectedSpace
    targetPathConnected := Homeomorph.ulift.symm.pathConnectedSpace
    perfect := Group.IsPerfect.map ((HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) (y := ULift.up x) rfl 0)).toMonoidHom
    surjective := basedPiOneMap_lift_surjective f γ h.surjective
    kernelEq := by
      rw [kernel_lift, h.kernelEq]
    localCoefficients := CommonUniverseChains.all_localCoefficients_liftMap f h.localCoefficients }

/-- Removing the two actual spatial lifts recovers exactly the original forward map. -/
theorem forward_down :
    (UniverseLift.down Y).comp
      ((UniverseLift.map.{u, v, max u v w} f).comp (UniverseLift.up X)) = f := by
  ext z
  rfl

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/CommonUniverse.lean:78-93"
  "adaptation" "Original maps and tracks; coefficients already in the maximum universe"]
  basedPiOneMap_lift_apply

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/CommonUniverse.lean:96-101"
  "adaptation" "Original maps and tracks; coefficients already in the maximum universe"]
  basedPiOneMap_square

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/CommonUniverse.lean:104-110"
  "adaptation" "Original maps and tracks; coefficients already in the maximum universe"]
  basedPiOneMap_lift_surjective

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/CommonUniverse.lean:113-129"
  "adaptation" "Original maps and tracks; coefficients already in the maximum universe"]
  kernel_lift

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/CommonUniverse.lean:132-146"
  "adaptation" "Original maps and tracks; coefficients already in the maximum universe"]
  isPlusConstruction

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/CommonUniverse.lean:149-153"
  "adaptation" "Original maps and tracks; coefficients already in the maximum universe"]
  forward_down

attribute [colib_tag "COL-0518"] isPlusConstruction

end Topology.PlusConstruction.CommonUniverse
