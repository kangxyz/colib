module

import Colib.Topology.HomotopyCofiber.UnreducedConeHomology

open CategoryTheory Limits MonoidalCategory FundamentalGroupoid.LocalCoefficients
open TopCat.DoubleCylinder Topology.ReducedMappingCone
open scoped Topology unitInterval
universe u
noncomputable section

section DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (lo hi : unitInterval) (b : Band lo hi) (V : ModuleCat.{u} ℤ)
  (hf : QuasiIso (pushforwardChainMap f.hom (constant B V)))

example : QuasiIso (pushforwardChainMap (leftOverlapInclusion f g sq lo hi)
    (constant (LeftCollar f g sq hi) V)) :=
  leftOverlap_constantChainMap_quasiIso f g sq lo hi b V hf

example : (relativeSingularChainComplex (rightCollarSet f g sq lo)
    (constant D V)).Acyclic :=
  doubleCylinder_rightCollar_relative_acyclic f g sq lo hi b V hf

example (n : ℕ) (hC : IsZero (homology (constant C V) n)) :
    IsZero (homology (constant D V) n) :=
  doubleCylinder_homology_isZero_of_quasiIso f g sq lo hi b V hf n hC
end DoubleCylinder

section Cone
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (V : ModuleCat.{u} ℤ)
  (hf : QuasiIso (pushforwardChainMap f (constant Y V)))

example (n : ℕ) : IsZero (homology (constant (UnreducedSpace f) V) (n + 1)) :=
  unreducedCone_positive_homology_isZero_of_quasiIso f V hf n

example (n : ℕ) : IsZero
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj V).obj
      (UnreducedSpace f)) :=
  unreducedCone_positive_singularHomology_isZero_of_quasiIso f V hf n
end Cone
