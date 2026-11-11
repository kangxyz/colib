/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Hypercohomology.Basic
public import Colib.CategoryTheory.Sites.Simplicial.ReducedHypercohomology
public import Colib.CategoryTheory.Sites.Simplicial.UniverseLift
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Reduced hypercohomology of pointed representables

The reduced cochains of a freely pointed discrete representable identify
with the native free representing sheaf in degree zero. The comparison
retains the maps of the representables and permits a larger coefficient
universe.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

private def uliftPointedYonedaIso :
    CategoryTheory.uliftYoneda.{w} (C := C) ⋙ discretePresheaf C ⋙ free C ≅
      PointedSimplicialPresheaf.yoneda C ⋙ uliftPointed.{w, v} C := by
  let S := simplicialYoneda C
  let L := uliftPresheaf.{w, v} C
  let T := uliftPresheafTerminalIso.{w, v} C
  letI : PreservesColimitsOfShape (Discrete WalkingPair) L := by
    dsimp [L, uliftPresheaf, SSet.uliftFunctor]
    infer_instance
  let e (U : C) : (L.obj (S.obj U) ⨿ ⊤_ _) ≅ L.obj (S.obj U ⨿ ⊤_ _) :=
    coprod.mapIso (Iso.refl _) T.symm ≪≫ PreservesColimitPair.iso L (S.obj U) (⊤_ _)
  have hi (U : C) : coprod.inl ≫ (e U).hom =
      L.map (coprod.inl : S.obj U ⟶ S.obj U ⨿ ⊤_ _) := by
    change coprod.inl ≫ (coprod.map (𝟙 (L.obj (S.obj U))) T.inv ≫
      coprodComparison L (S.obj U) (⊤_ _)) = _
    simp
  have hr (U : C) : coprod.inr ≫ (e U).hom =
      T.inv ≫ L.map (coprod.inr : (⊤_ _) ⟶ S.obj U ⨿ ⊤_ _) := by
    change coprod.inr ≫ (coprod.map (𝟙 (L.obj (S.obj U))) T.inv ≫
      coprodComparison L (S.obj U) (⊤_ _)) = _
    simp
  refine NatIso.ofComponents (fun U => Under.isoMk (e U) (hr U)) ?_
  intro U V f
  apply Under.UnderMorphism.ext
  change coprod.map (L.map (S.map f)) (𝟙 _) ≫ (e V).hom =
    (e U).hom ≫ L.map (coprod.map (S.map f) (𝟙 _))
  apply coprod.hom_ext
  · rw [coprod.inl_map_assoc, hi V, ← Category.assoc, hi U, ← L.map_comp, ← L.map_comp,
      coprod.inl_map]
  · rw [coprod.inr_map_assoc, Category.id_comp, hr V, ← Category.assoc, hr U,
      Category.assoc, ← L.map_comp, coprod.inr_map, Category.id_comp]

private def extendSingleZeroIso (A : Type*) [Category* A] [Abelian A] :
    ChainComplex.single₀ A ⋙ (ComplexShape.embeddingUpIntLE 0).extendFunctor _ ≅
      CochainComplex.singleFunctor A 0 := by
  let e := ComplexShape.embeddingUpIntLE 0
  have h : e.f 0 = 0 := rfl
  refine NatIso.ofComponents (fun X => HomologicalComplex.extendSingleIso e X 0 0 h) ?_
  intro X Y f
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  change (HomologicalComplex.extendMap
      ((HomologicalComplex.single A (.down ℕ) 0).map f) e).f 0 ≫
      (HomologicalComplex.extendSingleIso e Y 0 0 h).hom.f 0 =
    (HomologicalComplex.extendSingleIso e X 0 0 h).hom.f 0 ≫
      ((HomologicalComplex.single A (.up ℤ) 0).map f).f 0
  rw [HomologicalComplex.extendMap_f _ _ h,
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_hom_f]
  simp only [HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max v w}]

private def freeDiscreteReducedCochainsNatIso :
    discretePresheaf.{max v w} C ⋙ free C ⋙ reducedCochains C J ≅
      (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free ⋙
        presheafToSheaf J AddCommGrpCat.{max v w} ⋙ CochainComplex.singleFunctor _ 0 := by
  let e := Functor.isoWhiskerRight (discreteSheafifiedReducedChainsIso C J)
      ((ComplexShape.embeddingUpIntLE 0).extendFunctor _) ≪≫
    Functor.isoWhiskerLeft
      ((Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf J _)
      (extendSingleZeroIso _)
  exact NatIso.ofComponents (reducedCochainsFreeDiscreteIso C J)
    (fun {_ _} f => e.hom.naturality f)

variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max v w})]

/-- The lifted pointed representable has the native free sheaf as its reduced derived chains. -/
@[no_expose]
def liftedPointedYonedaReducedDerivedChainsIso :
    (yoneda C ⋙ uliftPointed.{w, v} C) ⋙ reducedDerivedChains.{d, max v w} C J ≅
      freeYoneda.{w} J ⋙ DerivedCategory.singleFunctor
        (Sheaf J AddCommGrpCat.{max v w}) 0 :=
  Functor.isoWhiskerRight (uliftPointedYonedaIso.{w} C).symm
      (reducedDerivedChains.{d, max v w} C J) ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.uliftYoneda.{w} (C := C))
      (Functor.isoWhiskerRight (freeDiscreteReducedCochainsNatIso.{w} C J)
        DerivedCategory.Q) ≪≫
    Functor.isoWhiskerLeft (freeYoneda.{w} J)
      (DerivedCategory.singleFunctorIsoCompQ (Sheaf J AddCommGrpCat.{max v w}) 0).symm

/-- On freely pointed representables, reduced hypercohomology is ordinary hypercohomology. -/
@[no_expose]
def reducedHypercohomologyYonedaIso
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) (p : ℤ) :
    (yoneda C ⋙ uliftPointed.{w, v} C).op ⋙ reducedHypercohomology.{d} C J K p ≅
      hypercohomologyPresheaf.{d, w} J K p := by
  let e := liftedPointedYonedaReducedDerivedChainsIso.{d, w} C J
  let Z := (DerivedCategory.Q.obj K)⟦p⟧
  refine NatIso.ofComponents (fun U => (preadditiveYoneda.obj Z).mapIso
    ((e.app U.unop).symm.op)) ?_
  intro U V f
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact (e.inv.naturality_assoc f.unop x).symm

/-- The forward map precomposes by the inverse of the representing-sheaf identification. -/
theorem reducedHypercohomologyYonedaIso_hom_app_apply
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) (p : ℤ) (U : C)
    (x : ((yoneda C ⋙ uliftPointed.{w, v} C).op ⋙
      reducedHypercohomology.{d} C J K p).obj (op U)) :
    (reducedHypercohomologyYonedaIso.{d, w} C J K p).hom.app (op U) x =
      (liftedPointedYonedaReducedDerivedChainsIso.{d, w} C J).inv.app U ≫ x := by
  unfold reducedHypercohomologyYonedaIso
  rfl

end CategoryTheory.PointedSimplicialPresheaf
