/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.CategoryTheory.Sites.Simplicial.ReducedChains
public import Colib.CategoryTheory.Sites.Simplicial.ReducedConeContraction
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# The reduced simplicial chains of the cone

The maximum cylinder on the actual reduced cone determines the ordinary
simplicial homotopy operators. These operators are natural at the site
objects and preserve the specified point. Reduction and sheafification
retain the homotopy, and the normalized Moore retract gives the contraction
of the actual normalized chain complex.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

namespace ReducedConeChains

variable (X : PointedSimplicialPresheaf.{w} C)

local notation "Q[" X "]" => Under.right (reducedCone X)
local notation "p[" X "]" => Under.hom (reducedCone X)

/-- The native simplicial homotopy at a site object. -/
def evaluationHomotopy (U : Cᵒᵖ) :
    SSet.Homotopy (𝟙 (Q[X].obj U)) ((terminal.from Q[X]).app U ≫ p[X].app U) :=
  mapReducedConeHomotopy ((CategoryTheory.evaluation Cᵒᵖ SSet).obj U) (Iso.refl _) X

/-- Evaluation of the original cylinder in the pointwise tensor. -/
def evaluatedCylinder (U : Cᵒᵖ) :
    Q[X].obj U ⊗ (Δ[1] : SSet.{w}) ⟶ Q[X].obj U :=
  (reducedConeCylinder X).app U

@[simp]
theorem evaluationHomotopy_h (U : Cᵒᵖ) :
    (evaluationHomotopy X U).h = evaluatedCylinder X U := by
  let F := (CategoryTheory.evaluation Cᵒᵖ (SSet.{w})).obj U
  let e : (Q[X].obj U ⊗ (Δ[1] : SSet.{w})) ≅ (Q[X].obj U ⊗ Δ[1]) :=
    intervalCylinderComparison F (Iso.refl _) Q[X]
  change e.inv ≫ evaluatedCylinder X U = _
  have hh : e.hom = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]
      exact intervalCylinderComparison_hom_fst F (Iso.refl _) Q[X]
    · rw [Category.id_comp]
      have h := intervalCylinderComparison_hom_snd F (Iso.refl _) Q[X]
      change e.hom ≫ snd _ _ = snd _ _ ≫ 𝟙 (Δ[1] : SSet.{w}) at h
      rwa [Category.comp_id] at h
  have hi : e.inv = 𝟙 _ := by
    simpa only [hh, Category.id_comp] using e.hom_inv_id
  rw [hi, Category.id_comp]

theorem cylinder_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Q[X].map f ▷ (Δ[1] : SSet.{w})) ≫ evaluatedCylinder X V =
      evaluatedCylinder X U ≫ Q[X].map f := by
  have h := (reducedConeCylinder X).naturality f
  change (Q[X].map f ⊗ₘ 𝟙 (Δ[1] : SSet.{w})) ≫ evaluatedCylinder X V =
    evaluatedCylinder X U ≫ Q[X].map f at h
  simpa only [tensorHom_id] using h

theorem cylinder_point (U : Cᵒᵖ) :
    (p[X].app U ▷ (Δ[1] : SSet.{w})) ≫ evaluatedCylinder X U =
      fst _ _ ≫ p[X].app U :=
  congrArg (fun f => f.app U) (reducedCone_point_whisker_comp_cylinder X)

theorem evaluationOperator_apply (U : Cᵒᵖ) {n : ℕ} (i : Fin (n + 1))
    (x : Q[X].obj U _⦋n⦌) :
    (evaluationHomotopy X U).toSimplicialObjectHomotopy.h i x =
      (SSet.yonedaEquiv.symm x ▷ Δ[1] ≫ evaluatedCylinder X U).app _
        (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1 := by
  rw [← evaluationHomotopy_h X U]
  rfl

/-- The natural degree-raising operator from the native simplicial homotopy. -/
def simplicialOperator {n : ℕ} (i : Fin (n + 1)) :
    Q[X].flip _⦋n⦌ ⟶ Q[X].flip _⦋n + 1⦌ where
  app U := (evaluationHomotopy X U).toSimplicialObjectHomotopy.h i
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro x
    change (evaluationHomotopy X V).toSimplicialObjectHomotopy.h i
        ((Q[X].map f).app _ x) =
      (Q[X].map f).app _ ((evaluationHomotopy X U).toSimplicialObjectHomotopy.h i x)
    rw [evaluationOperator_apply, evaluationOperator_apply, ← SSet.yonedaEquiv_symm_comp,
      comp_whiskerRight, Category.assoc, cylinder_naturality, ← Category.assoc]
    rfl

/-- The operators preserve the supplied point, in each degree. -/
theorem simplicialOperator_point {n : ℕ} (i : Fin (n + 1)) :
    ((flipFunctor Cᵒᵖ SimplexCategoryᵒᵖ (Type w)).map p[X]).app (op ⦋n⦌) ≫
        simplicialOperator X i =
      SimplicialObject.σ ((⊤_ (Cᵒᵖ ⥤ SSet.{w})).flip) i ≫
        ((flipFunctor Cᵒᵖ SimplexCategoryᵒᵖ (Type w)).map p[X]).app (op ⦋n + 1⦌) := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  change (evaluationHomotopy X U).toSimplicialObjectHomotopy.h i ((p[X].app U).app _ x) =
    (p[X].app U).app _ (SimplicialObject.σ ((⊤_ (Cᵒᵖ ⥤ SSet.{w})).obj U) i x)
  rw [evaluationOperator_apply, ← SSet.yonedaEquiv_symm_comp, comp_whiskerRight,
    Category.assoc, cylinder_point, ← Category.assoc]
  let : Unique (((⊤_ (Cᵒᵖ ⥤ SSet.{w})).obj U).obj (op ⦋n + 1⦌)) :=
    terminalSimplexUnique C _ U
  exact congrArg (fun z => (p[X].app U).app (op ⦋n + 1⦌) z) (Subsingleton.elim _ _)

/-- The native operators assembled in the category of presheaves of sets. -/
def simplicialHomotopy : SimplicialObject.Homotopy (𝟙 Q[X].flip)
    ((flipFunctor Cᵒᵖ SimplexCategoryᵒᵖ (Type w)).map (terminal.from Q[X] ≫ p[X])) where
  h i := simplicialOperator X i
  h_zero_comp_δ_zero n := by
    apply NatTrans.ext
    funext U
    exact (evaluationHomotopy X U).toSimplicialObjectHomotopy.h_zero_comp_δ_zero n
  h_last_comp_δ_last n := by
    apply NatTrans.ext
    funext U
    exact (evaluationHomotopy X U).toSimplicialObjectHomotopy.h_last_comp_δ_last n
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply NatTrans.ext
    funext U
    exact (evaluationHomotopy X U).toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_of_lt i j hij
  h_succ_comp_δ_castSucc_succ j := by
    apply NatTrans.ext
    funext U
    exact (evaluationHomotopy X U).toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_succ j
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply NatTrans.ext
    funext U
    exact (evaluationHomotopy X U).toSimplicialObjectHomotopy.h_castSucc_comp_δ_succ_of_lt i j hji
  h_comp_σ_castSucc_of_le i j hij := by
    apply NatTrans.ext
    funext U
    exact (evaluationHomotopy X U).toSimplicialObjectHomotopy.h_comp_σ_castSucc_of_le i j hij
  h_comp_σ_succ_of_lt i j hji := by
    apply NatTrans.ext
    funext U
    exact (evaluationHomotopy X U).toSimplicialObjectHomotopy.h_comp_σ_succ_of_lt i j hji

/-- The same operators after ordinary free abelianization. -/
def freeHomotopy : SimplicialObject.Homotopy
    ((freeAbelian C).map (𝟙 Q[X])) ((freeAbelian C).map (terminal.from Q[X] ≫ p[X])) :=
  (simplicialHomotopy X).whiskerRight
    ((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free)

theorem freeOperator_point {n : ℕ} (i : Fin (n + 1)) :
    ((freeAbelian C).map p[X]).app (op ⦋n⦌) ≫ (freeHomotopy X).h i =
      ((freeAbelian C).obj (⊤_ (Cᵒᵖ ⥤ SSet.{w}))).σ i ≫
        ((freeAbelian C).map p[X]).app (op ⦋n + 1⦌) := by
  let F := (Functor.whiskeringRight Cᵒᵖ (Type w) AddCommGrpCat.{w}).obj AddCommGrpCat.free
  change F.map (((flipFunctor Cᵒᵖ SimplexCategoryᵒᵖ (Type w)).map p[X]).app (op ⦋n⦌)) ≫
      F.map (simplicialOperator X i) =
    F.map (SimplicialObject.σ ((⊤_ (Cᵒᵖ ⥤ SSet.{w})).flip) i) ≫
      F.map (((flipFunctor Cᵒᵖ SimplexCategoryᵒᵖ (Type w)).map p[X]).app (op ⦋n + 1⦌))
  simpa only [Functor.map_comp] using
    congrArg (fun g => F.map g) (simplicialOperator_point X i)

theorem basepoint_reduction_app (Y : PointedSimplicialPresheaf.{w} C)
    (m : SimplexCategoryᵒᵖ) :
    ((freeAbelian C).map Y.hom).app m ≫ (reduction C Y).app m = 0 := by
  simpa only [NatTrans.comp_app, Limits.zero_app] using congr_app (basepoint_reduction C Y) m

/-- Evaluation at a simplicial degree retains the actual reduction cokernel. -/
def reductionIsCokernel (Y : PointedSimplicialPresheaf.{w} C) (m : SimplexCategoryᵒᵖ) :
    IsColimit (CokernelCofork.ofπ ((reduction C Y).app m) (basepoint_reduction_app Y m)) :=
  isColimitOfHasCokernelOfPreservesColimit ((CategoryTheory.evaluation _ _).obj m)
    ((freeAbelian C).map Y.hom)

theorem freeOperator_kills_point {n : ℕ} (i : Fin (n + 1)) :
    ((freeAbelian C).map p[X]).app (op ⦋n⦌) ≫
        ((freeHomotopy X).h i ≫ (reduction C (reducedCone X)).app (op ⦋n + 1⦌)) = 0 := by
  rw [← Category.assoc, freeOperator_point, Category.assoc, basepoint_reduction_app, comp_zero]

/-- The original operator descended to the native reduced free abelian presheaf. -/
def reducedOperator {n : ℕ} (i : Fin (n + 1)) :
    (reducedFreeAbelian C).obj (reducedCone X) _⦋n⦌ ⟶
      (reducedFreeAbelian C).obj (reducedCone X) _⦋n + 1⦌ :=
  (CokernelCofork.IsColimit.desc' (reductionIsCokernel (reducedCone X) (op ⦋n⦌))
    ((freeHomotopy X).h i ≫ (reduction C (reducedCone X)).app (op ⦋n + 1⦌))
    (freeOperator_kills_point X i)).1

@[reassoc]
theorem reduction_app_reducedOperator {n : ℕ} (i : Fin (n + 1)) :
    (reduction C (reducedCone X)).app (op ⦋n⦌) ≫ reducedOperator X i =
      (freeHomotopy X).h i ≫ (reduction C (reducedCone X)).app (op ⦋n + 1⦌) :=
  (CokernelCofork.IsColimit.desc' (reductionIsCokernel (reducedCone X) (op ⦋n⦌))
    ((freeHomotopy X).h i ≫ (reduction C (reducedCone X)).app (op ⦋n + 1⦌))
    (freeOperator_kills_point X i)).2

local instance reduction_app_epi (Y : PointedSimplicialPresheaf.{w} C)
    (m : SimplexCategoryᵒᵖ) : Epi ((reduction C Y).app m) where
  left_cancellation _ _ h := Cofork.IsColimit.hom_ext (reductionIsCokernel Y m) h

@[reassoc]
theorem reduction_app_comp_δ (Y : PointedSimplicialPresheaf.{w} C) {n : ℕ}
    (i : Fin (n + 2)) :
    (reduction C Y).app (op ⦋n + 1⦌) ≫ ((reducedFreeAbelian C).obj Y).δ i =
      ((freeAbelian C).obj Y.right).δ i ≫ (reduction C Y).app (op ⦋n⦌) :=
  ((reduction C Y).naturality (SimplexCategory.δ i).op).symm

@[reassoc]
theorem reduction_app_comp_σ (Y : PointedSimplicialPresheaf.{w} C) {n : ℕ}
    (i : Fin (n + 1)) :
    (reduction C Y).app (op ⦋n⦌) ≫ ((reducedFreeAbelian C).obj Y).σ i =
      ((freeAbelian C).obj Y.right).σ i ≫ (reduction C Y).app (op ⦋n + 1⦌) :=
  ((reduction C Y).naturality (SimplexCategory.σ i).op).symm

theorem collapse_reduction_app (m : SimplexCategoryᵒᵖ) :
    ((freeAbelian C).map (terminal.from Q[X] ≫ p[X])).app m ≫
      (reduction C (reducedCone X)).app m = 0 := by
  have h : (freeAbelian C).map (terminal.from Q[X] ≫ p[X]) ≫
      reduction C (reducedCone X) = 0 := by
    rw [Functor.map_comp, Category.assoc, basepoint_reduction, comp_zero]
  simpa only [NatTrans.comp_app, Limits.zero_app] using congr_app h m

/-- The descended operators give a simplicial homotopy to zero. -/
def reducedHomotopy : SimplicialObject.Homotopy
    (𝟙 ((reducedFreeAbelian C).obj (reducedCone X))) 0 where
  h i := reducedOperator X i
  h_zero_comp_δ_zero n := by
    apply (cancel_epi ((reduction C (reducedCone X)).app (op ⦋n⦌))).mp
    simp only [reduction_app_reducedOperator_assoc, reduction_app_comp_δ,
      (freeHomotopy X).h_zero_comp_δ_zero_assoc, collapse_reduction_app, Limits.zero_app, comp_zero]
  h_last_comp_δ_last n := by
    apply (cancel_epi ((reduction C (reducedCone X)).app (op ⦋n⦌))).mp
    simp only [reduction_app_reducedOperator_assoc, reduction_app_comp_δ,
      (freeHomotopy X).h_last_comp_δ_last_assoc, Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.comp_id]
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    apply (cancel_epi ((reduction C (reducedCone X)).app (op ⦋n + 1⦌))).mp
    simp only [reduction_app_reducedOperator_assoc, reduction_app_comp_δ,
      reduction_app_comp_δ_assoc, reduction_app_reducedOperator,
      (freeHomotopy X).h_succ_comp_δ_castSucc_of_lt_assoc i j hij]
  h_succ_comp_δ_castSucc_succ {n} j := by
    apply (cancel_epi ((reduction C (reducedCone X)).app (op ⦋n + 1⦌))).mp
    simp only [reduction_app_reducedOperator_assoc, reduction_app_comp_δ,
      (freeHomotopy X).h_succ_comp_δ_castSucc_succ_assoc]
  h_castSucc_comp_δ_succ_of_lt {n} i j hji := by
    apply (cancel_epi ((reduction C (reducedCone X)).app (op ⦋n + 1⦌))).mp
    simp only [reduction_app_reducedOperator_assoc, reduction_app_comp_δ,
      reduction_app_comp_δ_assoc, reduction_app_reducedOperator,
      (freeHomotopy X).h_castSucc_comp_δ_succ_of_lt_assoc i j hji]
  h_comp_σ_castSucc_of_le {n} i j hij := by
    apply (cancel_epi ((reduction C (reducedCone X)).app (op ⦋n⦌))).mp
    simp only [reduction_app_reducedOperator_assoc, reduction_app_comp_σ,
      reduction_app_comp_σ_assoc, reduction_app_reducedOperator,
      (freeHomotopy X).h_comp_σ_castSucc_of_le_assoc i j hij]
  h_comp_σ_succ_of_lt {n} i j hji := by
    apply (cancel_epi ((reduction C (reducedCone X)).app (op ⦋n⦌))).mp
    simp only [reduction_app_reducedOperator_assoc, reduction_app_comp_σ,
      reduction_app_comp_σ_assoc, reduction_app_reducedOperator,
      (freeHomotopy X).h_comp_σ_succ_of_lt_assoc i j hji]

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- Degreewise sheafification retains the simplicial nullhomotopy. -/
def sheafifiedHomotopy : SimplicialObject.Homotopy
    (𝟙 ((sheafifiedReducedFreeAbelian C J).obj (reducedCone X))) 0 := by
  let F := (SimplicialObject.whiskering _ _).obj (presheafToSheaf J AddCommGrpCat.{w})
  change SimplicialObject.Homotopy (𝟙 (F.obj ((reducedFreeAbelian C).obj (reducedCone X)))) 0
  simpa only [Functor.map_id, Functor.map_zero] using
    (reducedHomotopy X).whiskerRight (presheafToSheaf J AddCommGrpCat.{w})

open AlgebraicTopology in
/-- A simplicial nullhomotopy contracts the native normalized Moore complex. -/
def normalizedContraction {A : Type*} [Category* A] [Abelian A]
    {Y : SimplicialObject A} (H : SimplicialObject.Homotopy (𝟙 Y) 0) :
    Homotopy (𝟙 ((normalizedMooreComplex A).obj Y)) 0 := by
  let K := (alternatingFaceMapComplex A).obj Y
  let hK : Homotopy (𝟙 K) 0 := by
    simpa only [Functor.map_id, Functor.map_zero] using H.toChainHomotopy
  let s := DoldKan.splitMonoInclusionOfMooreComplexMap Y
  have hs : inclusionOfMooreComplexMap Y ≫ s.retraction = 𝟙 _ := s.id
  simpa only [Category.comp_id, comp_zero, zero_comp, hs] using
    (hK.compLeft (inclusionOfMooreComplexMap Y)).compRight s.retraction

end ReducedConeChains

/-- The actual sheafified reduced normalized chains of the cone are contractible. -/
def sheafifiedReducedConeChainsContraction
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
    (X : PointedSimplicialPresheaf.{w} C) :
    Homotopy (𝟙 ((sheafifiedReducedChains C J).obj (reducedCone X))) 0 :=
  ReducedConeChains.normalizedContraction (ReducedConeChains.sheafifiedHomotopy X J)

end CategoryTheory.PointedSimplicialPresheaf

attribute [colib_ref "mathlib_dold_kan_pin"
  "Mathlib/AlgebraicTopology/DoldKan/HomotopyEquivalence.lean:78-89" "ingredient"
  "The literal normalized Moore retract of the alternating-face complex"]
  CategoryTheory.PointedSimplicialPresheaf.sheafifiedReducedConeChainsContraction
