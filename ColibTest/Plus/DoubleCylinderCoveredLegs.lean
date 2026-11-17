module

public import Colib.Topology.LocalCoefficients.DoubleCylinderCoveredLegs

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Topology TopCat.DoubleCylinder
open scoped Topology unitInterval
universe u

example {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (lo hi : unitInterval) (band : Band lo hi)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N)
    {E : Type u} [TopologicalSpace E] [SimplyConnectedSpace E]
    (q : C(E, D)) (hq : IsCoveringMap q) (hs : Function.Surjective q)
    (x : B) (y : C) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (gapLeftEndpoint e) (x := x) rfl) ∧
      Function.Bijective (HomotopyGroup.map (N := Fin n) (gapRightEndpoint e) (x := y) rfl) := by
  obtain ⟨hL, hR⟩ := plus_legs_isWeakHomotopyEquivalence_of_cover
    f g sq lo hi band a b c γ δ N hf hg q hq hs
  exact ⟨hL.homotopy_bijective x n, hR.homotopy_bijective y n⟩

#print axioms TopCat.DoubleCylinder.plus_legs_isWeakHomotopyEquivalence_of_cover
