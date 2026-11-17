module

public import Colib.Topology.PlusConstruction.ClassicalCWUniquenessAssembly

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory TopCat.DoubleCylinder
open scoped Topology unitInterval

universe u

variable {A B C D S : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {ls : A ⊗ TopCat.I ⟶ S} {es : TopCat.of (B ⊕ B) ⟶ S}
variable {lm : A ⊗ TopCat.I ⟶ D} {em : TopCat.of (B ⊕ C) ⟶ D}

example (ss : IsPushout (TopCat.intervalEndpoints A) (endMap f f) ls es)
    (L : ContinuousMap.HomotopyEquiv B S) (hL : L.toFun = gapLeftEndpoint es)
    {Y : Type u} [TopologicalSpace Y] (k : C(A, Y)) (h₀ h₁ : C(B, Y))
    (H₀ : (h₀.comp f.hom).Homotopic k) (H₁ : (h₁.comp f.hom).Homotopic k) :
    h₀.Homotopic h₁ :=
  homotopic_underSource_of_leftLegEquiv f ss L hL k h₀ h₁ H₀ H₁

example
    (sm : IsPushout (TopCat.intervalEndpoints A) (endMap f g) lm em)
    (ss : IsPushout (TopCat.intervalEndpoints A) (endMap f f) ls es)
    (I : ContinuousMap.HomotopyEquiv B D) (J : ContinuousMap.HomotopyEquiv C D)
    (L : ContinuousMap.HomotopyEquiv B S)
    (hI : I.toFun = gapLeftEndpoint em) (hJ : J.toFun = gapRightEndpoint em)
    (hL : L.toFun = gapLeftEndpoint es) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f.hom).Homotopic g.hom ∧
        ∀ k : C(B, C), (k.comp f.hom).Homotopic g.hom → k.Homotopic h.toFun :=
  exists_homotopyEquiv_underSource_of_legEquivs f g sm ss I J L hI hJ hL

#print axioms TopCat.DoubleCylinder.exists_homotopyEquiv_underSource_of_legEquivs
