/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.CoproductHomology
public import Colib.Topology.FilteredRealization.Compact
public import Colib.Topology.Realization.SingularChainComparison
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.ContinuousMap.Sigma

/-!
# Colimits of singular simplicial sets of realizations

Compactness of a topological simplex gives factorization and eventual equality
of its maps into filtered realizations. Connectedness gives the singular
simplex comparison for topological coproducts. Exactness of these colimits
for modules carries the stage quasi-isomorphisms of the chain comparison to
the original unit map at the colimit.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Convexity
open scoped Simplicial

universe w ju jv

private theorem toSSetObjEquiv_map {X Y : TopCat.{w}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj X).obj n) :
    Y.toSSetObjEquiv n ((TopCat.toSSet.map f).app n x) =
      f.hom.comp (X.toSSetObjEquiv n x) := rfl

namespace SSet

/-- Realization followed by the singular simplicial set functor preserves filtered
colimits indexed by a small category in the simplicial universe. -/
theorem realizationSingular_preservesFilteredColimitsOfShape
    (J : Type w) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (SSet.toTop.{w} ⋙ TopCat.toSSet.{w}) := by
  apply preservesColimitsOfShape_of_evaluation _ J
  intro n
  refine ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨?_⟩⟩⟩
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun j x y h ↦ ?_)
  · obtain ⟨j, g, hg⟩ := Topology.FilteredRealization.compact_factors F c hc
      ((SSet.toTop.obj c.pt).toSSetObjEquiv n x)
    refine ⟨j, ((SSet.toTop.obj (F.obj j)).toSSetObjEquiv n).symm g, ?_⟩
    change x = (TopCat.toSSet.map (SSet.toTop.map (c.ι.app j))).app n _
    apply ((SSet.toTop.obj c.pt).toSSetObjEquiv n).injective
    rw [toSSetObjEquiv_map, Equiv.apply_symm_apply, hg]
  · change (TopCat.toSSet.map (SSet.toTop.map (c.ι.app j))).app n x =
      (TopCat.toSSet.map (SSet.toTop.map (c.ι.app j))).app n y at h
    have he := congrArg ((SSet.toTop.obj c.pt).toSSetObjEquiv n) h
    rw [toSSetObjEquiv_map, toSSetObjEquiv_map] at he
    obtain ⟨k, u, hu⟩ := Topology.FilteredRealization.compact_eq_eventually F c hc j
      ((SSet.toTop.obj (F.obj j)).toSSetObjEquiv n x)
      ((SSet.toTop.obj (F.obj j)).toSSetObjEquiv n y) he
    refine ⟨k, u, ?_⟩
    change (TopCat.toSSet.map (SSet.toTop.map (F.map u))).app n x =
      (TopCat.toSSet.map (SSet.toTop.map (F.map u))).app n y
    apply ((SSet.toTop.obj (F.obj k)).toSSetObjEquiv n).injective
    rw [toSSetObjEquiv_map, toSSetObjEquiv_map]
    exact hu

end SSet

namespace TopCat

/-- The singular simplicial set functor preserves coproducts indexed by a type
in the universe of the spaces. -/
theorem toSSet_preservesCoproducts (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) TopCat.toSSet.{w} := by
  apply preservesColimitsOfShape_of_evaluation _ (Discrete ι)
  intro n
  let E := TopCat.toSSet.{w} ⋙ (evaluation SimplexCategoryᵒᵖ (Type w)).obj n
  let (X : ι → TopCat.{w}) : PreservesColimit (Discrete.functor X) E := by
    apply preservesColimit_of_preserves_colimit_cocone (TopCat.sigmaCofanIsColimit X)
    refine (isColimitMapCoconeCofanMkEquiv E X (TopCat.sigmaι X)).symm ?_
    let s : Cofan (fun i ↦ E.obj (X i)) :=
      Cofan.mk (E.obj (TopCat.of (Σ i, X i))) (fun i ↦ E.map (TopCat.sigmaι X i))
    change IsColimit s
    apply Classical.choice
    rw [Cofan.nonempty_isColimit_iff_bijective_fromSigma]
    let T := StdSimplex ℝ (Fin (n.unop.len + 1))
    let e := (Equiv.sigmaCongrRight fun i ↦ (X i).toSSetObjEquiv n).trans
      ((ContinuousMap.sigmaCodHomeomorph T (fun i ↦ (X i : Type w))).symm.toEquiv.trans
        ((TopCat.of (Σ i, X i)).toSSetObjEquiv n).symm)
    have he : s.cofanTypes.fromSigma = e := by
      funext x
      rcases x with ⟨i, g⟩
      apply ((TopCat.of (Σ i, X i)).toSSetObjEquiv n).injective
      change (TopCat.of (Σ i, X i)).toSSetObjEquiv n ((toSSet.map (sigmaι X i)).app n g) = _
      rw [toSSetObjEquiv_map]
      simp only [e, Equiv.trans_apply, Equiv.sigmaCongrRight_apply, Equiv.apply_symm_apply]
      rfl
    rw [he]
    exact e.bijective
  exact preservesColimitsOfShape_of_discrete E

end TopCat

namespace SSet

private theorem quasiIso_realizationChainComparison_of_colimit {J : Type ju} [Category.{jv} J]
    (R : ModuleCat.{w} ℤ) (F : J ⥤ SSet.{w}) (c : Cocone F) (hc : IsColimit c)
    [PreservesColimitsOfShape J ((chainComplexFunctor.{w} (ModuleCat.{w} ℤ)).obj R)]
    [PreservesColimitsOfShape J (SSet.toTop.{w} ⋙ TopCat.toSSet.{w})]
    [∀ n : ℕ, PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} ℤ) (.down ℕ) n)]
    (h : ∀ j, QuasiIso (realizationChainComparison (F.obj j) R)) :
    QuasiIso (realizationChainComparison c.pt R) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{w} ℤ) (.down ℕ) n
  let A := (chainComplexFunctor.{w} (ModuleCat.{w} ℤ)).obj R
  let α := Functor.whiskerRight sSetTopAdj.unit (A ⋙ H)
  have hα (j : J) : IsIso ((Functor.whiskerLeft F α).app j) := by
    change IsIso (HomologicalComplex.homologyMap (realizationChainComparison (F.obj j) R) n)
    have := h j
    infer_instance
  have : IsIso (Functor.whiskerLeft F α) := NatIso.isIso_of_isIso_app _
  change IsIso (α.app c.pt)
  exact isIso_app_coconePt_of_preservesColimit F α c hc

/-- The actual unit comparison is a quasi-isomorphism on a filtered colimit
when it is a quasi-isomorphism at each stage. -/
theorem quasiIso_realizationChainComparison_of_filteredColimit
    {J : Type ju} [Category.{jv} J] [IsFiltered J] [UnivLE.{ju, w}] [UnivLE.{jv, w}]
    (R : ModuleCat.{w} ℤ) (F : J ⥤ SSet.{w}) (c : Cocone F) (hc : IsColimit c)
    [PreservesColimitsOfShape J ((chainComplexFunctor.{w} (ModuleCat.{w} ℤ)).obj R)]
    (h : ∀ j, QuasiIso (realizationChainComparison (F.obj j) R)) :
    QuasiIso (realizationChainComparison c.pt R) := by
  let G := SSet.toTop.{w} ⋙ TopCat.toSSet.{w}
  have hlarge : PreservesFilteredColimitsOfSize.{w, w} G :=
    ⟨fun K _ _ ↦ realizationSingular_preservesFilteredColimitsOfShape K⟩
  have hsmall : PreservesFilteredColimitsOfSize.{jv, ju} G :=
    preservesFilteredColimitsOfSize_of_univLE.{w, w, jv, ju} G
  have : PreservesColimitsOfShape J G := hsmall.preserves_filtered_colimits J
  have hH (n : ℕ) : PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} ℤ) (.down ℕ) n) :=
    ModuleCat.homologyFunctor_preservesFilteredColimits.{w} ℤ J (.down ℕ) n
  exact quasiIso_realizationChainComparison_of_colimit R F c hc h

/-- The actual unit comparison is a quasi-isomorphism on a coproduct
when it is a quasi-isomorphism on each summand. -/
theorem quasiIso_realizationChainComparison_of_coproduct
    {ι : Type w} (R : ModuleCat.{w} ℤ) (F : Discrete ι ⥤ SSet.{w}) (c : Cocone F) (hc : IsColimit c)
    [PreservesColimitsOfShape (Discrete ι) ((chainComplexFunctor.{w} (ModuleCat.{w} ℤ)).obj R)]
    (h : ∀ i, QuasiIso (realizationChainComparison (F.obj i) R)) :
    QuasiIso (realizationChainComparison c.pt R) := by
  have := TopCat.toSSet_preservesCoproducts ι
  have : PreservesColimitsOfShape (Discrete ι) (SSet.toTop.{w} ⋙ TopCat.toSSet.{w}) :=
    inferInstance
  have hH (n : ℕ) : PreservesColimitsOfShape (Discrete ι)
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} ℤ) (.down ℕ) n) :=
    ModuleCat.homologyFunctor_preservesCoproducts ℤ ι (.down ℕ) n
  exact quasiIso_realizationChainComparison_of_colimit R F c hc h

end SSet
