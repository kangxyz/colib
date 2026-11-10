/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.CoveringChains
public import Colib.Topology.LocalCoefficients.RegularFunctoriality

/-!
# The original-map square for regular covering chains

A supplied commuting square of actual covering maps induces a commuting
square between regular twisted chains and ordinary chains of the covers.
The lower map is the original map between total spaces, and the upper map
is the existing pushforward preceded by the actual path-class coefficient
map. The corner basepoint equality is explicit.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Convexity Opposite
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {E B E' B' : Type u}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
variable {p : E → B} {p' : E' → B'} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
variable [SimplyConnectedSpace E] [SimplyConnectedSpace E']
variable (k : C(E, E')) (f : C(B, B')) (h : ∀ e, p' (k e) = f (p e))

/-- The regular-basis equivalence respects the original maps of a covering square. -/
theorem coveringRegularSimplexEquiv_map (e₀ : E) {n : SimplexCategory}
    (s : RegularSimplex (p e₀) n) :
    coveringRegularSimplexEquiv hp' (k e₀) n
        (mapRegularSimplex f (p e₀) (p' (k e₀)) (h e₀) s) =
      k.comp (coveringRegularSimplexEquiv hp e₀ n s) := by
  rw [coveringRegularSimplexEquiv_apply, coveringRegularSimplexEquiv_apply]
  apply (IsCoveringMap.eq_lift hp' _ _ _ _ ?_ ?_).symm
  · change (IsCoveringMap.projection hp').comp
      (k.comp (IsCoveringMap.lift hp s.1 _ _)) = f.comp s.1
    ext t
    have he := congrArg (fun g ↦ g t)
      (hp.projection_lift s.1 (hp.monodromy s.2 ⟨e₀, rfl⟩).1
        (hp.monodromy s.2 ⟨e₀, rfl⟩).2)
    exact (h _).trans (congrArg f he)
  · change k (IsCoveringMap.lift hp s.1 _ _ (StdSimplex.single 0)) =
      (hp'.monodromy ((s.2.map f).cast (h e₀) rfl) ⟨k e₀, rfl⟩).1
    exact (congrArg k (hp.lift_vertex s.1 (hp.monodromy s.2 ⟨e₀, rfl⟩).1
      (hp.monodromy s.2 ⟨e₀, rfl⟩).2)).trans
      (IsCoveringMap.monodromy_naturality_basepoint hp hp' k f h e₀ s.2).symm

/-- Degreewise naturality uses the original coefficient and spatial maps. -/
@[reassoc]
theorem coveringModuleIso_map (e₀ : E) (n : SimplexCategory) :
    regularPushforwardModuleMap f (p e₀) (p' (k e₀)) (h e₀) n ≫
        (coveringModuleIso hp' (k e₀) n).hom =
      (coveringModuleIso hp e₀ n).hom ≫
        pushforwardModuleMap k (constant E' integralCoefficients) n := by
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro q z
  change (coveringModuleIso hp' (k e₀) n).hom
      (regularPushforwardModuleMap f (p e₀) (p' (k e₀)) (h e₀) n
        (regularChainGenerator (p e₀) ⟨σ, q⟩ z)) =
    pushforwardModuleMap k (constant E' integralCoefficients) n
      ((coveringModuleIso hp e₀ n).hom (regularChainGenerator (p e₀) ⟨σ, q⟩ z))
  simp [coveringRegularSimplexEquiv_map hp hp' k f h]

/-- The original-map square commutes before taking alternating faces. -/
@[reassoc]
theorem coveringSimplicialIso_map (e₀ : E) :
    regularPushforwardSimplicialMap f (p e₀) (p' (k e₀)) (h e₀) ≫
        (coveringSimplicialIso hp' (k e₀)).hom =
      (coveringSimplicialIso hp e₀).hom ≫
        pushforwardSimplicialMap k (constant E' integralCoefficients) := by
  ext n : 1
  exact coveringModuleIso_map hp hp' k f h e₀ n.unop

/-- The comparison intertwines genuine chain maps, retaining the original covering square. -/
@[reassoc]
theorem coveringConstantChainIso_map (e₀ : E) :
    regularPushforwardChainMap f (p e₀) (p' (k e₀)) (h e₀) ≫
        (coveringConstantChainIso hp' (k e₀)).hom =
      (coveringConstantChainIso hp e₀).hom ≫
        pushforwardChainMap k (constant E' integralCoefficients) := by
  let F := AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} ℤ)
  rw [regularPushforwardChainMap_eq]
  change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (coveringSimplicialIso_map hp hp' k f h e₀)).trans (F.map_comp _ _))

/-- The final comparison square uses mathlib's ordinary singular-chain map of the original `k`. -/
@[reassoc]
theorem coveringChainIso_map (e₀ : E) :
    regularPushforwardChainMap f (p e₀) (p' (k e₀)) (h e₀) ≫
        (coveringChainIso hp' (k e₀)).hom =
      (coveringChainIso hp e₀).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
          integralCoefficients).map (TopCat.ofHom k) := by
  simp only [coveringChainIso, Iso.trans_hom, ← Category.assoc]
  rw [coveringConstantChainIso_map hp hp' k f h]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun t ↦ (coveringConstantChainIso hp e₀).hom ≫ t)
      (constantChainComplexIso_naturality k integralCoefficients))

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringNaturality.lean:43-56"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringRegularSimplexEquiv_map

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringNaturality.lean:60-75"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringModuleIso_map

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringNaturality.lean:79-85"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringSimplicialIso_map

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringNaturality.lean:89-97"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringConstantChainIso_map

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringNaturality.lean:101-109"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringChainIso_map

end FundamentalGroupoid.LocalCoefficients
