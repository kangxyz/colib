/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleParameterSquare
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ParameterContinuity
public import Colib.CategoryTheory.Sites.SheafifyContinuous

/-! # The canonical étale reindexing comparison for the actual parameter square

The last arrow is the native sheafification/reindexing comparison, not an
asserted isomorphism. Both the original parameter map and integral chain
insertion/pairing are unchanged.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology AlgebraicGeometry.Scheme AlgebraicSimplex

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "J" => SmoothSite.etaleTopology (Spec (CommRingCat.of k))
local notation "G" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "R" => SmoothSite.Contraction.parameterProduct G
local notation "N" q:max =>
  Functor.obj (singularChainsFunctor k) (Functor.obj (toPresheaf k) (reducedTorus k q))

/-- The original ordinary singular parameter map sheafified for the étale topology. -/
def etaleReducedTorusSingularParameterProduct (q : ℕ) :
    let A := (presheafToSheaf J AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)
    A.obj (N q) ⟶
      (((R).sheafPushforwardContinuous _ J J).mapHomologicalComplex (.down ℕ)).obj
        (A.obj (N (q + 1))) :=
  (R).sheafifyReindexComplexMap J J _ (.down ℕ)
    (reducedTorusSingularParameterProduct k q)

/-- The actual integral parameter square followed by the canonical reindex comparison. -/
theorem reducedTorusEtaleParameterSquare_reindex (q : ℕ) :
    let F := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat
    let M := (presheafToSheaf J (ModuleCat.{u + 1} ℤ)).mapHomologicalComplex (.down ℕ)
    let A := (presheafToSheaf J AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)
    let H := (sheafCompose J F).mapHomologicalComplex (.down ℕ)
    let T := (parameterReindex k
      (A := AddCommGrpCat.{u + 1}) G).mapHomologicalComplex (.down ℕ)
    let T' := (parameterReindex k
      (A := ModuleCat.{u + 1} ℤ) G).mapHomologicalComplex (.down ℕ)
    let K := (alternatingFaceMapComplex _).obj (reducedTorusIntSimplicial k q)
    let L := T'.obj ((alternatingFaceMapComplex _).obj
      (reducedTorusIntSimplicial k (q + 1)))
    H.map (M.map (reducedTorusChainCoordinateInsertion k q ≫
      T'.map (reducedTorusPresheafChainPairing k q))) ≫
        (integralEtaleChainsForgetIso k L).hom ≫
          A.map (T.map (reducedTorusIntChainsUnderlyingIso k (q + 1)).hom) ≫
            (NatTrans.mapHomologicalComplex
              ((R).sheafifyReindexComparison J J AddCommGrpCat.{u + 1})
                (.down ℕ)).app (N (q + 1)) =
    (integralEtaleChainsForgetIso k K).hom ≫
      A.map (reducedTorusIntChainsUnderlyingIso k q).hom ≫
        etaleReducedTorusSingularParameterProduct k q := by
  intro F M A H T T' K L
  have h := congrArg (fun f => f ≫
    (NatTrans.mapHomologicalComplex
      ((R).sheafifyReindexComparison J J AddCommGrpCat.{u + 1})
        (.down ℕ)).app (N (q + 1))) (reducedTorusEtaleParameterSquare k q)
  simpa only [Category.assoc, etaleReducedTorusSingularParameterProduct,
    Functor.sheafifyReindexComplexMap] using h

/-- Before sheafification the map is the original parameter map followed by
reindexing the genuine étale sheafification unit. -/
theorem toSheafify_etaleReducedTorusSingularParameterProduct (q n : ℕ) :
    toSheafify J ((N q).X n) ≫
      ((etaleReducedTorusSingularParameterProduct k q).f n).hom =
    (reducedTorusSingularParameterProduct k q).f n ≫
      Functor.whiskerLeft (R).op (toSheafify J ((N (q + 1)).X n)) :=
  (R).toSheafify_sheafifyReindexComplexMap_f J J _ (.down ℕ)
    (reducedTorusSingularParameterProduct k q) n

end AlgebraicGeometry.PresheafWithTransfers
