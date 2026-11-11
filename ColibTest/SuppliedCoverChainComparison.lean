module

import Colib.Topology.LocalCoefficients.CoveringHomologyComparison

open CategoryTheory FundamentalGroupoid.LocalCoefficients
open scoped Simplicial
universe u
noncomputable section
variable {E B E' B' : Type u}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
  {p : E → B} {p' : E' → B'} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
  [SimplyConnectedSpace E] [SimplyConnectedSpace E']
  (k : C(E, E')) (f : C(B, B')) (h : ∀ e, p' (k e) = f (p e)) (e₀ : E)

example {n : SimplexCategory} (s : RegularSimplex (p e₀) n) :
    coveringRegularSimplexEquiv hp e₀ n s =
      IsCoveringMap.lift hp s.1 (hp.monodromy s.2 ⟨e₀, rfl⟩).1
        (hp.monodromy s.2 ⟨e₀, rfl⟩).2 := rfl

example {m n : SimplexCategory} (s : RegularSimplex (p e₀) n) (α : m ⟶ n) :
    coveringRegularSimplexEquiv hp e₀ m (restrictRegularSimplex (p e₀) s α) =
      restrictSimplex (coveringRegularSimplexEquiv hp e₀ n s) α :=
  coveringRegularSimplexEquiv_restrict hp e₀ s α

example {n : SimplexCategory} (s : RegularSimplex (p e₀) n) (z : ℤ) :
    (coveringModuleIso hp e₀ n).hom (regularChainGenerator (p e₀) s z) =
      integralChainGenerator (coveringRegularSimplexEquiv hp e₀ n s) z :=
  coveringModuleIso_generator hp e₀ s z

example {n : SimplexCategory} (s : RegularSimplex (p e₀) n) :
    coveringRegularSimplexEquiv hp' (k e₀) n
      (mapRegularSimplex f (p e₀) (p' (k e₀)) (h e₀) s) =
    k.comp (coveringRegularSimplexEquiv hp e₀ n s) :=
  coveringRegularSimplexEquiv_map hp hp' k f h e₀ s

example : regularPushforwardChainMap f (p e₀) (p' (k e₀)) (h e₀) ≫
      (coveringConstantChainIso hp' (k e₀)).hom =
    (coveringConstantChainIso hp e₀).hom ≫
      pushforwardChainMap k (constant E' integralCoefficients) :=
  coveringConstantChainIso_map hp hp' k f h e₀

variable [PathConnectedSpace B]
  (hπ : Function.Bijective (HomotopyGroup.piMap 0 f (x := p e₀) rfl))

example : (coveringConstantArrowIso hp hp' k f h e₀ hπ).hom.left =
    (coveringPullbackConstantChainIso hp k f h e₀ hπ).hom := rfl

example : (coveringConstantArrowIso hp hp' k f h e₀ hπ).hom.right =
    (coveringConstantChainIso hp' (k e₀)).hom := rfl

example : Arrow.mk (UniverseLift.chainMap.{u, u, u} f (regular (p' (k e₀)))) ≅
    Arrow.mk (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integralCoefficients).map (TopCat.ofHom k)) :=
  coveringUniverseLiftSingularArrowIso hp hp' k f h e₀ hπ

example : QuasiIso (UniverseLift.chainMap.{u, u, u} f (regular (p' (k e₀)))) ↔
    QuasiIso (pushforwardChainMap k (constant E' integralCoefficients)) :=
  covering_quasiIso_iff hp hp' k f h e₀ hπ

example (hH : ∀ A : System.{u, u} B', QuasiIso (UniverseLift.chainMap.{u, u, u} f A)) :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integralCoefficients).map (TopCat.ofHom k)) :=
  covering_singular_quasiIso_of_all_localCoefficients hp hp' k f h e₀ hπ hH
