/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.Prism
public import Colib.AlgebraicGeometry.Simplex.OrdinaryChains
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Interval endpoint homotopy for the original ordinary singular chains

The geometric prism produces a native simplicial homotopy between the two
original restrictions from `U × Δ¹` to `U`. Mathlib's `toChainHomotopy` supplies
the signed chain homotopy. Its degree-raising component is the negative
alternating sum of the actual prism pullbacks, with no manually changed sign.

The final comparison is Mathlib's existing evaluation/alternating-face
interchange isomorphism, whose components are identities. It identifies the
endpoint maps with restrictions of the previously constructed presheaf-valued
`singularChainsFunctor`, without introducing a new chain model. Coefficients
are arbitrary preadditive categories, and no homotopy-invariance assumption is
made. Equality on homology additionally needs `CategoryWithHomology`.

Reference: MVW2006, Lemma 2.18, printed pp. 17-18, generalized to commutative
base rings and preadditive coefficients. Transfer structures are not claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A]
variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)

/-- A simplicial homotopy of the original endpoint restrictions. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/Algebra/Homology/SingularComplex/Endpoints.lean:120-153"
  "adaptation" "Native simplicial homotopy of the actual relative endpoint restrictions"]
def intervalEndpointSimplicialHomotopy (U : SmoothSite (Spec (.of R))) :
    SimplicialObject.Homotopy
      ((simplicialPresheaf R P).flip.map (intervalInclusion R U 0).op)
      ((simplicialPresheaf R P).flip.map (intervalInclusion R U 1).op) where
  h i := P.map (prismMap R U i).op
  h_zero_comp_δ_zero n := by
    change P.map (prismMap R U (0 : Fin (n + 1))).op ≫
      P.map (SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ 0)).op =
        P.map (SmoothSite.productMap (intervalInclusion R U 1) (𝟙 _)).op
    rw [← P.map_comp, ← op_comp, prismMap_zero_face]
  h_last_comp_δ_last n := by
    change P.map (prismMap R U (Fin.last n)).op ≫
      P.map (SmoothSite.productMap (𝟙 U)
        ((cosimplicialSmoothSite R).δ (Fin.last (n + 1)))).op =
          P.map (SmoothSite.productMap (intervalInclusion R U 0) (𝟙 _)).op
    rw [← P.map_comp, ← op_comp, prismMap_last_face]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    change P.map (prismMap R U j.succ).op ≫
      P.map (SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ i.castSucc)).op =
        P.map (SmoothSite.productMap (𝟙 _) ((cosimplicialSmoothSite R).δ i)).op ≫
          P.map (prismMap R U j).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, prismMap_face_left R U i j hij]
  h_succ_comp_δ_castSucc_succ j := by
    change P.map (prismMap R U j.succ).op ≫
      P.map (SmoothSite.productMap (𝟙 U)
        ((cosimplicialSmoothSite R).δ j.castSucc.succ)).op =
          P.map (prismMap R U j.castSucc).op ≫
            P.map (SmoothSite.productMap (𝟙 U)
              ((cosimplicialSmoothSite R).δ j.castSucc.succ)).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, prismMap_face_middle]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    change P.map (prismMap R U j.castSucc).op ≫
      P.map (SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).δ i.succ)).op =
        P.map (SmoothSite.productMap (𝟙 _) ((cosimplicialSmoothSite R).δ i)).op ≫
          P.map (prismMap R U j).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, prismMap_face_right R U i j hji]
  h_comp_σ_castSucc_of_le i j hij := by
    change P.map (prismMap R U j).op ≫
      P.map (SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).σ i.castSucc)).op =
        P.map (SmoothSite.productMap (𝟙 _) ((cosimplicialSmoothSite R).σ i)).op ≫
          P.map (prismMap R U j.succ).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp,
      prismMap_degeneracy_left R U i j hij]
  h_comp_σ_succ_of_lt i j hji := by
    change P.map (prismMap R U j).op ≫
      P.map (SmoothSite.productMap (𝟙 U) ((cosimplicialSmoothSite R).σ i.succ)).op =
        P.map (SmoothSite.productMap (𝟙 _) ((cosimplicialSmoothSite R).σ i)).op ≫
          P.map (prismMap R U j.castSucc).op
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp,
      prismMap_degeneracy_right R U i j hji]

variable [Preadditive A]

/-- Apply the native signed simplicial-to-chain homotopy construction. -/
@[colib_ref "MVW2006" "Lecture 2, Lemma 2.18 and its proof, pp. 17-18"
  "generalization" "Endpoint homotopy without assuming homotopy-invariant coefficients"]
def intervalEndpointHomotopy (U : SmoothSite (Spec (.of R))) :
    _root_.Homotopy
      ((alternatingFaceMapComplex A).map
        ((simplicialPresheaf R P).flip.map (intervalInclusion R U 0).op))
      ((alternatingFaceMapComplex A).map
        ((simplicialPresheaf R P).flip.map (intervalInclusion R U 1).op)) :=
  (intervalEndpointSimplicialHomotopy R P U).toChainHomotopy

/-- The native homotopy convention retains the negative alternating prism sum. -/
theorem intervalEndpointHomotopy_hom (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (intervalEndpointHomotopy R P U).hom n (n + 1) =
      -∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • P.map (prismMap R U i).op :=
  SimplicialObject.Homotopy.ToChainHomotopy.hom_eq _ n

/-- Native evaluation of the previously constructed chain complex commutes with
the native alternating-face construction, with identity components. -/
def singularChainsEvaluationIso (U : SmoothSite (Spec (.of R))) :
    (((evaluation _ A).obj (op U)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((singularChainsFunctor R).obj P) ≅
        (alternatingFaceMapComplex A).obj ((simplicialPresheaf R P).flip.obj (op U)) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    ((evaluation _ A).obj (op U))).app (simplicialPresheaf R P)

/-- This comparison retains the original restriction maps of the chain presheaf. -/
@[reassoc]
theorem singularChainsEvaluationIso_naturality
    {U V : SmoothSite (Spec (.of R))} (f : U ⟶ V) :
    ((NatTrans.mapHomologicalComplex ((evaluation _ A).map f.op)
      (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) ≫
        (singularChainsEvaluationIso R P U).hom =
          (singularChainsEvaluationIso R P V).hom ≫
            (alternatingFaceMapComplex A).map ((simplicialPresheaf R P).flip.map f.op) := by
  ext n
  change P.map (SmoothSite.productMap f
    (𝟙 ((cosimplicialSmoothSite R).obj ⦋n⦌))).op ≫ 𝟙 _ =
      𝟙 _ ≫ P.map (SmoothSite.productMap f
        (𝟙 ((cosimplicialSmoothSite R).obj ⦋n⦌))).op
  simp

/-- The two actual restrictions of the original presheaf-valued singular complex
are chain homotopic. No replacement chain complex or transfer action is used. -/
def ordinaryIntervalEndpointHomotopy (U : SmoothSite (Spec (.of R))) :
    _root_.Homotopy
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map (intervalInclusion R U 0).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P))
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map (intervalInclusion R U 1).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) := by
  have H := ((intervalEndpointHomotopy R P U).compLeft
    (singularChainsEvaluationIso R P
      (SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌))).hom).compRight
      (singularChainsEvaluationIso R P U).inv
  have h (v : Fin 2) :
      ((singularChainsEvaluationIso R P
      (SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌))).hom ≫
        (alternatingFaceMapComplex A).map
          ((simplicialPresheaf R P).flip.map (intervalInclusion R U v).op)) ≫
            (singularChainsEvaluationIso R P U).inv =
              (NatTrans.mapHomologicalComplex
                ((evaluation _ A).map (intervalInclusion R U v).op)
                (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P) := by
    rw [← singularChainsEvaluationIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (_root_.Homotopy.ofEq (h 0).symm).trans
    (H.trans (_root_.Homotopy.ofEq (h 1)))

/-- The two original endpoint maps agree on homology in every degree. -/
theorem ordinaryIntervalEndpoint_homologyMap_eq [CategoryWithHomology A]
    (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map (intervalInclusion R U 0).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) n =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          ((evaluation _ A).map (intervalInclusion R U 1).op)
          (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) n :=
  (ordinaryIntervalEndpointHomotopy R P U).homologyMap_eq n

end AlgebraicSimplex

attribute [colib_tag "COL-0320"] AlgebraicSimplex.intervalEndpointSimplicialHomotopy
attribute [colib_tag "COL-0320"] AlgebraicSimplex.intervalEndpointHomotopy_hom
attribute [colib_tag "COL-0320"] AlgebraicSimplex.ordinaryIntervalEndpointHomotopy
