module

import Colib.Topology.PlusConstruction.CommonUniverse

open CategoryTheory FundamentalGroupoid FundamentalGroupoid.LocalCoefficients
open Topology Topology.PlusConstruction
open scoped Simplicial

universe u v w
noncomputable section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y)

example (z : X) : UniverseLift.map.{u, v, max u v w} f (ULift.up z) =
    ULift.up (f z) := rfl

example (t : unitInterval) :
    (γ.map (continuous_uliftUp : Continuous (ULift.up : Y → ULift.{max u v w} Y))) t =
      ULift.up (γ t) := rfl

example : (γ.map (continuous_uliftUp :
    Continuous (ULift.up : Y → ULift.{max u v w} Y))).map continuous_uliftDown = γ := by
  ext t
  rfl

example (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) rfl 0 a =
    HomotopyGroup.piMap 0 (UniverseLift.up.{u, max u v w} X) rfl a := rfl

example (a : HomotopyGroup.Pi 1 X x) :
    basedPiOneMap (UniverseLift.map.{u, v, max u v w} f) (γ.map continuous_uliftUp)
      (HomotopyGroup.homeomorphPiEquiv
        (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) rfl 0 a) =
    HomotopyGroup.homeomorphPiEquiv
      (Homeomorph.ulift.{max u v w, v} (X := Y)).symm (x := y) rfl 0
        (basedPiOneMap f γ a) := CommonUniverse.basedPiOneMap_lift_apply f γ a

example : (basedPiOneMap (UniverseLift.map.{u, v, max u v w} f)
    (γ.map continuous_uliftUp)).ker = (basedPiOneMap f γ).ker.map
      (HomotopyGroup.homeomorphPiEquiv
        (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) rfl 0).toMonoidHom :=
  CommonUniverse.kernel_lift f γ

example (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (h : IsPlusConstruction.{u, v, max u v w} f γ N) :
    IsPlusConstruction.{max u v w, max u v w, max u v w}
      (UniverseLift.map.{u, v, max u v w} f) (γ.map continuous_uliftUp)
      (N.map (HomotopyGroup.homeomorphPiEquiv
        (Homeomorph.ulift.{max u v w, u} (X := X)).symm (x := x) rfl 0).toMonoidHom) :=
  CommonUniverse.isPlusConstruction f γ N h

example : (UniverseLift.down Y).comp
    ((UniverseLift.map.{u, v, max u v w} f).comp (UniverseLift.up X)) = f :=
  CommonUniverse.forward_down f

example (B : System.{max u v w, max u v w} (ULift.{max u v w} Y))
    (z : ULift.{max u v w} Y)
    (a : fiber (UniverseLift.system.{v, max u v w, u}
      (pullback (UniverseLift.up.{v, max u v w} Y) B)) z) :
    (CommonUniverseChains.coefficientRetractIso B).hom.app (FundamentalGroupoid.mk z) a =
      a.down := CommonUniverseChains.coefficientRetractIso_apply B z a

example (A : System.{v, max u v w} Y) {n : ℕ}
    (σ : SingularSimplex (ULift.{max u v w} X) ⦋n⦌) :
    chainInclusion (UniverseLift.system.{u, max u v w, v} (pullback f A)) σ ≫
      (UniverseLift.chainMap.{u, v, max u v w} f A).f n =
    chainInclusion (UniverseLift.system.{v, max u v w, u} A)
      ((UniverseLift.map.{u, v, max u v w} f).comp σ) :=
  CommonUniverseChains.original_chainMap_inclusion f A σ

example (h : ∀ A : System.{v, max u v w} Y,
    QuasiIso (UniverseLift.chainMap.{u, v, max u v w} f A))
    (B : System.{max u v w, max u v w} (ULift.{max u v w} Y)) :
    QuasiIso (UniverseLift.chainMap.{max u v w, max u v w, max u v w}
      (UniverseLift.map.{u, v, max u v w} f) B) :=
  CommonUniverseChains.all_localCoefficients_liftMap f h B
