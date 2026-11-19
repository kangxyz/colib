/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.ParameterProduct
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.EtaleContinuity
public import Colib.CategoryTheory.Sites.SheafifyContinuous
public import Colib.AlgebraicGeometry.Simplex.SheafifiedChains

/-! # The original reduced-torus parameter map on étale singular chains

Reconstruction from the native singular map and sheafification adjunction.
No coefficient or topology comparison is inverted.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicSimplex
open AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]
local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Jₖ" => SmoothSite.etaleTopology Sₖ
local notation "T" =>
  SmoothSite.Contraction.parameterProduct (SmoothSite.multiplicativeGroupObject Sₖ)
local notation "P₀" q:max => Functor.obj (toPresheaf k) (reducedTorus k q)
local notation "K" q:max => Functor.obj (singularChainsFunctor k) (P₀ q)
local notation "L" q:max => Functor.obj (sheafifiedSingularChainsFunctor k Jₖ) (P₀ q)

/-- Sheafify the actual reduced-torus chain map along the literal parameter product. -/
def etaleReducedTorusSingularParameterProduct (q : ℕ) :
    L q ⟶ (((T).sheafPushforwardContinuous AddCommGrpCat.{u + 1} Jₖ Jₖ).mapHomologicalComplex
      (.down ℕ)).obj (L (q + 1)) :=
  (T).sheafifyReindexComplexMap Jₖ Jₖ _ (.down ℕ) (reducedTorusSingularParameterProduct k q)

/-- The étale lift retains the original chain map after the sheafification unit. -/
@[reassoc]
theorem toSheafify_etaleReducedTorusSingularParameterProduct_f (q n : ℕ) :
    toSheafify Jₖ ((K q).X n) ≫ ((etaleReducedTorusSingularParameterProduct k q).f n).hom =
      (reducedTorusSingularParameterProduct k q).f n ≫
        Functor.whiskerLeft (T).op (toSheafify Jₖ ((K (q + 1)).X n)) :=
  (T).toSheafify_sheafifyReindexComplexMap_f Jₖ Jₖ _ (.down ℕ)
    (reducedTorusSingularParameterProduct k q) n

end AlgebraicGeometry.PresheafWithTransfers
