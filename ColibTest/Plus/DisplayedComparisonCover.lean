module

public import Colib.Topology.PlusConstruction.DisplayedComparisonCover

set_option autoImplicit false

open CategoryTheory FundamentalGroupoid Topology
open scoped Topology

universe u v w

-- The source, target and covering total space may be in three independent universes.
example {X : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
    [PathConnectedSpace X] [SimplyConnectedSpace E]
    (f : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q)
    (x : X) (e : E) (h : f x = q e)
    (hf : Function.Bijective (HomotopyGroup.piMap 0 f h)) :
    SimplyConnectedSpace {z : X × E // f z.1 = q z.2} :=
  Covering.Pullback.simplyConnectedSpace f q hq ⟨(x, e), h⟩ hf

-- The homology map tested is the literal second projection, not an abstract equivalence.
example {A B D E : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace D] [TopologicalSpace E] [PathConnectedSpace B] [SimplyConnectedSpace E]
    (f : C(A, B)) (g : C(A, D)) (k : C(B, D)) (H : (k.comp f).Homotopy g)
    {x : A} {y : B} {z : D} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 A x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    (q : C(E, D)) (hq : IsCoveringMap q) (e : E) (he : k y = q e) :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
      LocalCoefficients.integralCoefficients).map
        (TopCat.ofHom (⟨fun z : {p : B × E // k p.1 = q p.2} ↦ z.val.2,
          continuous_snd.comp continuous_subtype_val⟩ : C(_, E)))) :=
  (IsPlusConstruction.displayedComparison_simplyConnected_pullback_singular_quasiIso
    f g k H γ δ N hf hg q hq e he).2
