module

public import Colib.Topology.LocalCoefficients.HomologicalWhiteheadSimplyConnected

set_option autoImplicit false

open CategoryTheory FundamentalGroupoid.LocalCoefficients Topology
open scoped Topology

universe u

section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y))

-- The ordinary integral quasi-isomorphism concludes weakness of exactly the original map.
example (hH : QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
    integralCoefficients.{u}).map (TopCat.ofHom f))) : IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_singular_quasiIso f hH

-- The original singular homology formulation retains all degrees and all original fibers.
example (hH : ∀ n : ℕ, IsIso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        integralCoefficients.{u}).map (TopCat.ofHom f))) :
    IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_singularHomology_isIso f hH

example (x : X)
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficients.{u})))
    (y : Y) (z : HomotopyFiber f y) (k : ℕ) :
    Subsingleton (HomotopyGroup.Pi k (HomotopyFiber f y) z) :=
  fiber_subsingleton_of_integral_quasiIso f x hH y z k

end
