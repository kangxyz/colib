module

public import Colib.Topology.HomotopyCofiber.UnreducedFirstObstruction

set_option autoImplicit false

open Topology Topology.ReducedMappingCone
open scoped Topology unitInterval

universe u

section
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))

-- Neither of the two stored paths is replaced by an abstract replacement.
example (y : Y) (z : HomotopyFiber f y) (t : unitInterval) :
    (unreducedFirstObstructionMap f y z).1.2 = z.1.2 ∧
      (unreducedFirstObstructionMap f y z).1.1.1.2 t =
        unreducedCylinder f (z.1.1, ULift.up t) :=
  ⟨unreducedFirstObstructionMap_outerPath f y z, unreducedFirstObstructionMap_innerPath f y z t⟩

-- In the lowest range the actual fiber fundamental group is the second cone homotopy group.
noncomputable example [SimplyConnectedSpace X] (x : X) (hf : IsHomotopyConnectedMap f 1) :
    HomotopyGroup.Pi 1 (HomotopyFiber f (f x)) (HomotopyFiber.basepoint f (f x) x rfl) ≃
      HomotopyGroup.Pi 2 (UnreducedSpace f) (unreducedVertex f) :=
  firstObstructionEquivCone f x 0 hf

-- The lower vanishing theorem covers arbitrary points of the same literal cone.
example [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (x : X)
    (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1)) (z : UnreducedSpace f)
    (k : ℕ) (hk : k < m + 2) : Subsingleton (HomotopyGroup.Pi k (UnreducedSpace f) z) :=
  unreducedCone_subsingleton_below_first f x m hf z k hk

end
