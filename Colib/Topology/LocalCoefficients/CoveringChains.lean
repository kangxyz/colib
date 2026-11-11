/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.RegularChains
public import Colib.Topology.Covering.SingularSimplices
public import Colib.Topology.Covering.PathClasses

/-!
# Regular local-coefficient chains and a supplied simply connected cover

For an actual covering with simply connected total space, regular
local-coefficient chains of the base are isomorphic to ordinary integral
singular chains of the total space. The comparison sends a regular basis
path to the unique simplex lift beginning at its monodromy endpoint.
It commutes with every simplicial restriction, hence with all faces,
degeneracies, and differentials.

The chain models use one explicitly specified common universe and the
ordinary coefficient object is `ULift ℤ` in that universe. No universal
cover is constructed, and no Hurewicz or Whitehead recognition is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Convexity Opposite
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p) [SimplyConnectedSpace E]

/-- Regular basis paths specify exactly the possible first vertices of a lifted simplex. -/
def coveringRegularSimplexEquiv (e₀ : E) (n : SimplexCategory) :
    RegularSimplex (p e₀) n ≃ SingularSimplex E n :=
  (Equiv.sigmaCongrRight fun σ : SingularSimplex B n ↦
    IsCoveringMap.pathClassEquiv hp e₀ (σ (StdSimplex.single 0))).trans
      (IsCoveringMap.simplexEquiv hp n).symm

/-- The comparison uses the actual simplex lift at the actual monodromy endpoint. -/
theorem coveringRegularSimplexEquiv_apply (e₀ : E) {n : SimplexCategory}
    (s : RegularSimplex (p e₀) n) :
    coveringRegularSimplexEquiv hp e₀ n s =
      IsCoveringMap.lift hp s.1 (hp.monodromy s.2 ⟨e₀, rfl⟩).1
        (hp.monodromy s.2 ⟨e₀, rfl⟩).2 := rfl

/-- Every simplicial restriction agrees with the transported regular basis restriction. -/
theorem coveringRegularSimplexEquiv_restrict (e₀ : E) {m n : SimplexCategory}
    (s : RegularSimplex (p e₀) n) (α : m ⟶ n) :
    coveringRegularSimplexEquiv hp e₀ m (restrictRegularSimplex (p e₀) s α) =
      restrictSimplex (coveringRegularSimplexEquiv hp e₀ n s) α := by
  change (IsCoveringMap.simplexEquiv hp m).symm
    ⟨_, IsCoveringMap.pathClassEquiv hp e₀ _ _⟩ =
      restrictSimplex ((IsCoveringMap.simplexEquiv hp n).symm
        ⟨_, IsCoveringMap.pathClassEquiv hp e₀ _ _⟩) α
  rw [← IsCoveringMap.lift_restrict]
  congr 1
  exact congrArg (fun e ↦
    (⟨restrictSimplex s.1 α, e⟩ : IsCoveringMap.BasedSimplex p m))
    (hp.pathClassEquiv_trans e₀ s.2 (.mk
      ((PathConnectedSpace.somePath (StdSimplex.single 0)
        ((StdSimplex.single 0).map α)).map s.1.continuous)))

/-- Degreewise linear isomorphism of the existing coproduct chain modules. -/
def coveringModuleIso (e₀ : E) (n : SimplexCategory) :
    chainModule (regular (p e₀)) n ≅
      chainModule (constant E integralCoefficients) n :=
  regularBasisIso (p e₀) n ≪≫
    (Finsupp.mapDomain.linearEquiv ℤ ℤ
      (coveringRegularSimplexEquiv hp e₀ n)).toModuleIso ≪≫
    (integralBasisIso n).symm

/-- The degreewise comparison retains the integer and lifts the actual simplex. -/
@[simp]
theorem coveringModuleIso_generator (e₀ : E) {n : SimplexCategory}
    (s : RegularSimplex (p e₀) n) (z : ℤ) :
    (coveringModuleIso hp e₀ n).hom (regularChainGenerator (p e₀) s z) =
      integralChainGenerator (coveringRegularSimplexEquiv hp e₀ n s) z := by
  change integralBasisInv n
    (Finsupp.mapDomain (coveringRegularSimplexEquiv hp e₀ n)
      (regularBasisHom (p e₀) n (regularChainGenerator (p e₀) s z))) = _
  rw [regularBasisHom_generator, Finsupp.mapDomain_single, integralBasisInv_single]

/-- The linear isomorphisms commute with all faces and degeneracies, including face zero. -/
@[reassoc]
theorem coveringModuleIso_naturality (e₀ : E) {m n : SimplexCategory}
    (α : m ⟶ n) :
    chainMap (regular (p e₀)) α ≫ (coveringModuleIso hp e₀ m).hom =
      (coveringModuleIso hp e₀ n).hom ≫ chainMap (constant E integralCoefficients) α := by
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro q z
  change (coveringModuleIso hp e₀ m).hom
      (chainMap (regular (p e₀)) α (regularChainGenerator (p e₀) ⟨σ, q⟩ z)) =
    chainMap (constant E integralCoefficients) α
      ((coveringModuleIso hp e₀ n).hom (regularChainGenerator (p e₀) ⟨σ, q⟩ z))
  simp [coveringRegularSimplexEquiv_restrict]

/-- The actual simplicial-module isomorphism, with all restriction identities proved. -/
def coveringSimplicialIso (e₀ : E) :
    simplicialModule (regular (p e₀)) ≅
      simplicialModule (constant E integralCoefficients) :=
  NatIso.ofComponents (fun n ↦ coveringModuleIso hp e₀ n.unop)
    (by
      intro n m α
      exact coveringModuleIso_naturality hp e₀ α.unop)

/-- The genuine chain isomorphism before the standard ordinary-chain reindexing. -/
def coveringConstantChainIso (e₀ : E) :
    singularChainComplex (regular (p e₀)) ≅
      singularChainComplex (constant E integralCoefficients) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (coveringSimplicialIso hp e₀)

/-- Regular local coefficients recover mathlib's ordinary singular chains of this cover. -/
def coveringChainIso (e₀ : E) :
    singularChainComplex (regular (p e₀)) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).obj (TopCat.of E) :=
  coveringConstantChainIso hp e₀ ≪≫ constantChainComplexIso integralCoefficients

/-- The actual differential square commutes in every degree. -/
@[reassoc]
theorem coveringModuleIso_d (e₀ : E) (m n : ℕ) :
    (singularChainComplex (regular (p e₀))).d m n ≫
        (coveringModuleIso hp e₀ ⦋n⦌).hom =
      (coveringModuleIso hp e₀ ⦋m⦌).hom ≫
        (singularChainComplex (constant E integralCoefficients)).d m n :=
  ((coveringConstantChainIso hp e₀).hom.comm m n).symm

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:46-50"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringRegularSimplexEquiv

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:53-57"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringRegularSimplexEquiv_apply

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:60-72"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringRegularSimplexEquiv_restrict

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:75-81"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringModuleIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:85-92"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringModuleIso_generator

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:96-109"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringModuleIso_naturality

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:112-118"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringSimplicialIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:121-124"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringConstantChainIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:127-131"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringChainIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/CoveringChains.lean:135-140"
  "adaptation" "Original maps of supplied covers; no existence statement"]
  coveringModuleIso_d

attribute [colib_tag "COL-0522"]
  coveringChainIso

end FundamentalGroupoid.LocalCoefficients
