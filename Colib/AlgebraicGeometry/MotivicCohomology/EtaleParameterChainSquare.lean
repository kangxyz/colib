/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ParameterMapSquare
public import Colib.AlgebraicGeometry.MotivicCohomology.ParameterProduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleParameterReindex

/-! # The actual ordinary parameter chain square under change of topology

The comparison of reindexing and change of topology is a map, not an isomorphism.
The two outside chain isomorphisms are exactly the native double-sheafification ones.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicSimplex AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The native Nisnevich parameter map becomes the native étale parameter map,
using the canonical reindex comparison and the actual double-sheafification isos. -/
theorem sheafifiedReducedTorusSingularParameterProduct_etale_square (q : ℕ) :
    let S := Spec (CommRingCat.of k)
    let J := SmoothSite.nisnevichTopology S
    let K := SmoothSite.etaleTopology S
    let G := SmoothSite.multiplicativeGroupObject S
    let N := (presheafToSheaf J AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)
    let E := (SmoothSite.nisnevichToEtaleSheaf S
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)
    let Re := ((SmoothSite.Contraction.parameterProduct G).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} K K).mapHomologicalComplex (.down ℕ)
    let φ := NatTrans.mapHomologicalComplex
      (SmoothSite.parameterNisnevichToEtaleComparison S AddCommGrpCat.{u + 1} G) (.down ℕ)
    let e := Functor.mapHomologicalComplexCompIso
      (SmoothSite.nisnevichToEtaleSheafificationIso S) (.down ℕ)
    let L := (singularChainsFunctor k).obj ((toPresheaf k).obj (reducedTorus k q))
    let L' := (singularChainsFunctor k).obj ((toPresheaf k).obj (reducedTorus k (q + 1)))
    E.map (sheafifiedReducedTorusSingularParameterProduct k q) ≫
      φ.app (N.obj L') ≫ Re.map (e.hom.app L') =
    e.hom.app L ≫ etaleReducedTorusSingularParameterProduct k q := by
  intro S J K G N E Re φ e L L'
  apply HomologicalComplex.hom_ext
  intro n
  exact SmoothSite.parameterNisnevichToEtaleComparison_map S G
    ((reducedTorusSingularParameterProduct k q).f n)

end AlgebraicGeometry.PresheafWithTransfers
