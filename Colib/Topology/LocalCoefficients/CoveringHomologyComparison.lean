/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.RegularIsomorphism
public import Colib.Topology.LocalCoefficients.CoveringNaturality
public import Colib.Topology.LocalCoefficients.UniverseLift
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Original twisted chains and a commuting map of supplied simply connected covers

Bijectivity of the actual Pi one map makes the existing regular coefficient
conversion invertible. Cancelling that conversion in the proved covering
naturality square gives an isomorphism between the original chain-map arrows.
The same-universe UniverseLift comparison then retains the original twisted
chain map used by the plus-construction API. No universal cover is constructed,
and no local covering-space hypothesis is inferred from CW homotopy type.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u

namespace FundamentalGroupoid.LocalCoefficients
variable {E B E' B' : Type u}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
variable {p : E → B} {p' : E' → B'} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
variable [SimplyConnectedSpace E] [SimplyConnectedSpace E'] [PathConnectedSpace B]
variable (k : C(E, E')) (f : C(B, B')) (h : ∀ e, p' (k e) = f (p e))
variable (e₀ : E) (hπ : Function.Bijective (HomotopyGroup.piMap 0 f (x := p e₀) rfl))

/-- The actual pulled-back regular complex identifies with constant chains
of the supplied source cover, retaining the specified basepoint equality. -/
def coveringPullbackConstantChainIso :
    singularChainComplex (pullback f (regular (p' (k e₀)))) ≅
      singularChainComplex (constant E integralCoefficients) :=
  (regularCoefficientChainIso f (p e₀) (p' (k e₀)) (h e₀) hπ).symm ≪≫
    coveringConstantChainIso hp e₀

/-- The original spatial pushforward with pulled-back regular coefficients
is the same arrow as the original constant-coefficient map of the covers. -/
def coveringConstantArrowIso :
    Arrow.mk (pushforwardChainMap f (regular (p' (k e₀)))) ≅
      Arrow.mk (pushforwardChainMap k (constant E' integralCoefficients)) := by
  let eR := regularCoefficientChainIso f (p e₀) (p' (k e₀)) (h e₀) hπ
  let eS := coveringConstantChainIso hp e₀
  let eT := coveringConstantChainIso hp' (k e₀)
  refine Arrow.isoMk (eR.symm ≪≫ eS) eT ?_
  change (eR.inv ≫ eS.hom) ≫ pushforwardChainMap k (constant E' integralCoefficients) =
    pushforwardChainMap f (regular (p' (k e₀))) ≫ eT.hom
  exact (Category.assoc _ _ _).trans (eR.inv_comp_eq.mpr
    ((coveringConstantChainIso_map hp hp' k f h e₀).symm.trans (Category.assoc _ _ _)))

/-- The domain comparison in the preceding arrow is the explicitly displayed
coefficient inverse followed by the original covering-chain isomorphism. -/
@[simp] theorem coveringConstantArrowIso_hom_left :
    (coveringConstantArrowIso hp hp' k f h e₀ hπ).hom.left =
      (coveringPullbackConstantChainIso hp k f h e₀ hπ).hom := rfl

/-- The codomain comparison is the original target covering-chain map. -/
@[simp] theorem coveringConstantArrowIso_hom_right :
    (coveringConstantArrowIso hp hp' k f h e₀ hπ).hom.right =
      (coveringConstantChainIso hp' (k e₀)).hom := rfl

/-- The identical comparison lands in mathlib's actual singular-chain map
of k, rather than an isomorphic replacement map chosen without a square. -/
def coveringSingularArrowIso :
    Arrow.mk (pushforwardChainMap f (regular (p' (k e₀)))) ≅
      Arrow.mk (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).map (TopCat.ofHom k)) := by
  let eR := regularCoefficientChainIso f (p e₀) (p' (k e₀)) (h e₀) hπ
  let eS := coveringChainIso hp e₀
  let eT := coveringChainIso hp' (k e₀)
  refine Arrow.isoMk (eR.symm ≪≫ eS) eT ?_
  change (eR.inv ≫ eS.hom) ≫ _ = _ ≫ eT.hom
  exact (Category.assoc _ _ _).trans (eR.inv_comp_eq.mpr
    ((coveringChainIso_map hp hp' k f h e₀).symm.trans (Category.assoc _ _ _)))

/-- The original arbitrary-universe API, specialized to this same universe,
retains the actual covering map after its proved coefficient/simplex comparison. -/
def coveringUniverseLiftConstantArrowIso :
    Arrow.mk (UniverseLift.chainMap.{u, u, u} f (regular (p' (k e₀)))) ≅
      Arrow.mk (pushforwardChainMap k (constant E' integralCoefficients)) :=
  (Arrow.isoMk
    (f := Arrow.mk (UniverseLift.chainMap.{u, u, u} f (regular (p' (k e₀)))))
    (g := Arrow.mk (pushforwardChainMap f (regular (p' (k e₀)))))
    (UniverseLift.chainComparisonIso (pullback f (regular (p' (k e₀)))))
    (UniverseLift.chainComparisonIso (regular (p' (k e₀))))
    (UniverseLift.chainComparisonIso_naturality f (regular (p' (k e₀)))).symm) ≪≫
    coveringConstantArrowIso hp hp' k f h e₀ hπ

/-- The original UniverseLift twisted arrow also identifies with mathlib's
original singular-chain arrow of the displayed map between total spaces. -/
def coveringUniverseLiftSingularArrowIso :
    Arrow.mk (UniverseLift.chainMap.{u, u, u} f (regular (p' (k e₀)))) ≅
      Arrow.mk (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).map (TopCat.ofHom k)) :=
  (Arrow.isoMk
    (f := Arrow.mk (UniverseLift.chainMap.{u, u, u} f (regular (p' (k e₀)))))
    (g := Arrow.mk (pushforwardChainMap f (regular (p' (k e₀)))))
    (UniverseLift.chainComparisonIso (pullback f (regular (p' (k e₀)))))
    (UniverseLift.chainComparisonIso (regular (p' (k e₀))))
    (UniverseLift.chainComparisonIso_naturality f (regular (p' (k e₀)))).symm) ≪≫
    coveringSingularArrowIso hp hp' k f h e₀ hπ

include hp hp' h hπ in
/-- Quasi-isomorphism is transferred only through the proved square of the
actual original twisted and covering maps. -/
theorem covering_quasiIso_iff :
    QuasiIso (UniverseLift.chainMap.{u, u, u} f (regular (p' (k e₀)))) ↔
      QuasiIso (pushforwardChainMap k (constant E' integralCoefficients)) :=
  quasiIso_iff_of_arrow_mk_iso _ _
    (coveringUniverseLiftConstantArrowIso hp hp' k f h e₀ hπ)

include hp hp' h hπ in
/-- Testing all original target systems includes the regular system in this
coefficient universe, and therefore makes the supplied lift an integral
homology equivalence. No existence of covers is part of this theorem. -/
theorem covering_integral_quasiIso_of_all_localCoefficients
    (hH : ∀ A : System.{u, u} B', QuasiIso (UniverseLift.chainMap.{u, u, u} f A)) :
    QuasiIso (pushforwardChainMap k (constant E' integralCoefficients)) :=
  (covering_quasiIso_iff hp hp' k f h e₀ hπ).mp (hH (regular (p' (k e₀))))

include hp hp' h hπ in
/-- The original mathlib singular-chain map has the same quasi-isomorphism
property, retaining the exact map k in its conclusion. -/
theorem covering_singular_quasiIso_of_all_localCoefficients
    (hH : ∀ A : System.{u, u} B', QuasiIso (UniverseLift.chainMap.{u, u, u} f A)) :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integralCoefficients).map (TopCat.ofHom k)) :=
  (quasiIso_iff_of_arrow_mk_iso _ _
    (coveringUniverseLiftSingularArrowIso hp hp' k f h e₀ hπ)).mp
      (hH (regular (p' (k e₀))))

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:42-46"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringPullbackConstantChainIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:50-61"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringConstantArrowIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:65-67"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringConstantArrowIso_hom_left

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:70-72"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringConstantArrowIso_hom_right

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:76-87"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringSingularArrowIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:91-100"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringUniverseLiftConstantArrowIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:104-114"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringUniverseLiftSingularArrowIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:119-123"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  covering_quasiIso_iff

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:129-132"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  covering_integral_quasiIso_of_all_localCoefficients

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringHomologyComparison.lean:137-143"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  covering_singular_quasiIso_of_all_localCoefficients

attribute [colib_tag "COL-0522"]
  coveringUniverseLiftSingularArrowIso covering_singular_quasiIso_of_all_localCoefficients

end FundamentalGroupoid.LocalCoefficients
