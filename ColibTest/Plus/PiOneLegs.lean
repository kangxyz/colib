module

public import Colib.Topology.DoubleMappingCylinder.PiOneLegs

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Topology TopCat.DoubleCylinder
open scoped Topology

universe u w

-- Both original endpoint maps induce bijections at their literal image basepoints.
example {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, w} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, w} g.hom δ N) :
    Function.Bijective (HomotopyGroup.piMap 0 (gapLeftEndpoint e) (x := f a) rfl) ∧
      Function.Bijective (HomotopyGroup.piMap 0 (gapRightEndpoint e) (x := g a) rfl) :=
  plus_legs_piOne_bijective f g sq a b c γ δ N hf hg

#print axioms leftEnd_piOne_bijective_of_equal_kernel
#print axioms rightEnd_piOne_bijective_of_equal_kernel
#print axioms plus_legs_piOne_bijective
