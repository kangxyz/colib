module

public import Colib.Topology.LocalCoefficients.HomologicalWhiteheadCovering

set_option autoImplicit false

open CategoryTheory Topology
open scoped Topology
universe u

-- The original map induces every based homotopy bijection, not just the lift.
example {X Y E : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
    [PathConnectedSpace X] [PathConnectedSpace Y] [SimplyConnectedSpace E]
    (f : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q)
    (x : X) (e : E) (h : f x = q e)
    (hπ : Function.Bijective (HomotopyGroup.piMap 0 f (x := x) rfl))
    (hH : ∀ A : FundamentalGroupoid.LocalCoefficients.System.{u, u} Y,
      QuasiIso (FundamentalGroupoid.LocalCoefficients.UniverseLift.chainMap.{u, u, u} f A))
    (p : X) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := p) rfl) :=
  (LocalCoefficients.isWeakHomotopyEquivalence_of_twisted_quasiIso_of_cover
    f q hq x e h hπ hH).homotopy_bijective p n

#print axioms LocalCoefficients.isWeakHomotopyEquivalence_of_twisted_quasiIso_of_cover
