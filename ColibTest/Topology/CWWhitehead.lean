module

public import Colib.Topology.CWComplex.Whitehead

open Set Topology Topology.CWComplex
open scoped Topology unitInterval

universe u v

section Lift
variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]
  {E B : Type v} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
  (hp : CubicalSubdivision.BoundaryLifting p)

example (a₀ a₁ : C(C, E)) (H : (p.comp a₀).Homotopy (p.comp a₁)) :
    ∃ K : a₀.Homotopy a₁,
      (∀ t x, p (K (t, x)) = H (t, x)) ∧
        (∀ x, K (0, x) = a₀ x) ∧ (∀ x, K (1, x) = a₁ x) :=
  ⟨homotopyLift C p hp a₀ a₁ H, homotopyLift_project C p hp a₀ a₁ H,
    homotopyLift_zero C p hp a₀ a₁ H, homotopyLift_one C p hp a₀ a₁ H⟩

end Lift

section Whitehead
variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D] (f : C(C, D))

example (hf : IsWeakHomotopyEquivalence f) :
    ∃ g : C(D, C),
      Nonempty ((g.comp f).Homotopy (ContinuousMap.id C)) ∧
        Nonempty ((f.comp g).Homotopy (ContinuousMap.id D)) :=
  ⟨weakMapInverse C D f hf, ⟨weakMapLeftHomotopy C D f hf⟩,
    ⟨weakMapRightHomotopy C D f hf⟩⟩

example :
    IsWeakHomotopyEquivalence f ↔ ∃ e : ContinuousMap.HomotopyEquiv C D, e.toFun = f :=
  isWeakHomotopyEquivalence_iff_exists_homotopyEquiv C D f

#print axioms homotopyLift_project
#print axioms homotopyEquivOfWeakHomotopyEquivalence

end Whitehead
