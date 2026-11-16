module

public import Colib.Topology.DoubleMappingCylinder.PlusGapConnectivity

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory TopCat.DoubleCylinder Topology
open scoped Topology

universe u w

-- Both assertions concern the original gap and do not assume the two kernels agree.
example {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N M : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, w} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, w} g.hom δ M) :
    Function.Surjective (HomotopyGroup.piMap 0 (gap f g sq) (x := a) rfl) ∧
      Function.Bijective (HomotopyGroup.map (N := Fin 0) (gap f g sq) (x := a) rfl) :=
  ⟨plus_gap_piOne_surjective f g sq a b c γ δ N M hf hg,
    plus_gap_piZero_bijective f g sq a b c γ δ N M hf hg⟩

#print axioms plus_gap_piOne_surjective
#print axioms plus_gap_piZero_bijective
