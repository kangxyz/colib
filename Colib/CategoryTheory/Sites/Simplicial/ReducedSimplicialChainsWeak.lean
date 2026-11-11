/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseDerivedChains
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Module.ULift
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Absolute and reduced chains of simplicial sets

The basepoint splits off its terminal source before normalization. The short
exact sequence for the actual reduction cokernel turns quasi-isomorphisms
on absolute normalized chains into quasi-isomorphisms on reduced chains.

The Moore inclusion and the free abelian coproduct comparison identify the
absolute hypothesis with one for Mathlib's simplicial chains. The
equivalence between integer modules and abelian groups also gives the
form of the hypothesis with lifted integer coefficients.
-/

@[expose] public noncomputable section

open AlgebraicTopology CategoryTheory Limits

universe w

namespace CategoryTheory.PointedSimplicialPresheaf

private def basepointCokernelSequence (P : Arrow (SimplicialObject AddCommGrpCat.{w})) :
    ShortComplex (SimplicialObject AddCommGrpCat.{w}) :=
  ShortComplex.mk P.hom (cokernel.π P.hom) (cokernel.condition P.hom)

private def basepointCokernelSequenceMap
    {P Q : Arrow (SimplicialObject AddCommGrpCat.{w})} (g : P ⟶ Q) :
    basepointCokernelSequence P ⟶ basepointCokernelSequence Q where
  τ₁ := g.left
  τ₂ := g.right
  τ₃ := (coker _).map g
  comm₁₂ := Arrow.w g
  comm₂₃ := (coker.π _).naturality g

private theorem basepointCokernelSequence_shortExact (P : Arrow SSet.{w})
    (hP : IsTerminal P.left) :
    (basepointCokernelSequence (simplicialSetFreeAbelian.mapArrow.obj P)).ShortExact := by
  have h : P.hom ≫ hP.from P.right = 𝟙 P.left := hP.hom_ext _ _
  have h' := simplicialSetFreeAbelian.congr_map h
  rw [Functor.map_comp, Functor.map_id] at h'
  refine ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) ?_ ?_
  · change Mono (simplicialSetFreeAbelian.map P.hom)
    exact SplitMono.mono ⟨simplicialSetFreeAbelian.map (hP.from P.right), h'⟩
  · change Epi (cokernel.π (simplicialSetFreeAbelian.map P.hom))
    infer_instance

/-- Absolute normalized chains control reduction at the actual basepoint. -/
theorem pointedSimplicialSetChainsPreserveRealizationWeakEquivalences_of_normalized
    (h : ∀ ⦃X Y : SSet.{w}⦄ (f : X ⟶ Y), SSet.IsRealizationWeakEquivalence f →
      QuasiIso ((simplicialSetFreeAbelian ⋙ normalizedMooreComplex _).map f)) :
    PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w} := by
  intro P Q g hP hQ hg
  let N := (Abelian.DoldKan.equivalence (A := AddCommGrpCat.{w})).functor
  let φ := N.mapShortComplex.map
    (basepointCokernelSequenceMap (simplicialSetFreeAbelian.mapArrow.map g))
  have h₁ : QuasiIso φ.τ₁ := by
    have := isIso_of_isTerminal hP hQ g.left
    change QuasiIso (N.map (simplicialSetFreeAbelian.map g.left))
    infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    ((basepointCokernelSequence_shortExact P hP).map_of_exact N)
    ((basepointCokernelSequence_shortExact Q hQ).map_of_exact N) h₁ (h g.right hg)

private def freeCoproductIso :
    AddCommGrpCat.free.{w} ≅ sigmaConst.obj (AddCommGrpCat.free.obj (PUnit : Type w)) :=
  AddCommGrpCat.adj.leftAdjointUniq
    ((sigmaConstAdj _).ofNatIsoRight
      ((AddCommGrpCat.adj.corepresentableBy (PUnit : Type w)).toIso ≪≫
        Functor.isoWhiskerLeft (CategoryTheory.forget AddCommGrpCat.{w}) Coyoneda.punitIso.{w} ≪≫
        Functor.rightUnitor _))

private def freeAlternatingIso :
    simplicialSetFreeAbelian.{w} ⋙ alternatingFaceMapComplex _ ≅
      (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj
        (AddCommGrpCat.free.obj (PUnit : Type w)) :=
  Functor.isoWhiskerRight ((SimplicialObject.whiskering _ _).mapIso freeCoproductIso)
    (alternatingFaceMapComplex _)

/-- The native Moore complex and Mathlib's simplicial chain complex detect the same
quasi-isomorphisms with the free abelian group on one generator as coefficient. -/
theorem quasiIso_normalizedSimplicialSetFreeAbelian_map_iff_chainComplexMap
    {X Y : SSet.{w}} (f : X ⟶ Y) :
    QuasiIso ((simplicialSetFreeAbelian ⋙ normalizedMooreComplex _).map f) ↔
      QuasiIso (SSet.chainComplexMap f (AddCommGrpCat.free.obj (PUnit : Type w))) := by
  let N := normalizedMooreComplex AddCommGrpCat.{w}
  let A := alternatingFaceMapComplex AddCommGrpCat.{w}
  let i := inclusionOfMooreComplex AddCommGrpCat.{w}
  let F := simplicialSetFreeAbelian.{w}
  have hX : QuasiIso (i.app (F.obj X)) :=
    DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.quasiIso_hom
  have hY : QuasiIso (i.app (F.obj Y)) :=
    DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.quasiIso_hom
  have comm : (F ⋙ N).map f ≫ i.app (F.obj Y) =
      i.app (F.obj X) ≫ (F ⋙ A).map f := i.naturality (F.map f)
  let e := freeAlternatingIso.{w}
  calc
    _ ↔ QuasiIso ((F ⋙ N).map f ≫ i.app (F.obj Y)) :=
      (quasiIso_iff_comp_right _ _).symm
    _ ↔ QuasiIso (i.app (F.obj X) ≫ (F ⋙ A).map f) := by rw [comm]
    _ ↔ QuasiIso ((F ⋙ A).map f) := quasiIso_iff_comp_left _ _
    _ ↔ _ := quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm)

/-- The simplicial-chain implication at the integral coefficient gives the
pointed reduced-chain implication used for stalkwise descent. -/
theorem pointedSimplicialSetChainsPreserveRealizationWeakEquivalences_of_chainComplexMap
    (h : ∀ ⦃X Y : SSet.{w}⦄ (f : X ⟶ Y), SSet.IsRealizationWeakEquivalence f →
      QuasiIso (SSet.chainComplexMap f (AddCommGrpCat.free.obj (PUnit : Type w)))) :
    PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w} := by
  apply pointedSimplicialSetChainsPreserveRealizationWeakEquivalences_of_normalized
  intro X Y f hf
  exact (quasiIso_normalizedSimplicialSetFreeAbelian_map_iff_chainComplexMap f).2 (h f hf)

private theorem quasiIso_chainComplexMap_freePUnit_iff_liftedIntegers
    {X Y : SSet.{w}} (f : X ⟶ Y) :
    QuasiIso (SSet.chainComplexMap f (AddCommGrpCat.free.obj (PUnit : Type w))) ↔
      QuasiIso (SSet.chainComplexMap f (ModuleCat.of ℤ (ULift.{w} ℤ))) := by
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let U := forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}
  let eR : U.obj R ≅ AddCommGrpCat.free.obj (PUnit : Type w) :=
    (AddEquiv.ulift.trans (FreeAbelianGroup.uniqueEquiv (PUnit : Type w)).symm).toAddCommGrpIso
  let e : (SSet.chainComplexFunctor _).obj R ⋙ U.mapHomologicalComplex (.down ℕ) ≅
      (SSet.chainComplexFunctor AddCommGrpCat.{w}).obj
        (AddCommGrpCat.free.obj (PUnit : Type w)) :=
    SSet.chainComplexFunctorObjCompMapIso U R ≪≫
      (SSet.chainComplexFunctor AddCommGrpCat.{w}).mapIso eR
  exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm)).symm.trans
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology (SSet.chainComplexMap f R) U)

/-- The realization comparison can use the lifted integers in the native module category. -/
theorem pointedSimplicialSetChainsPreserveRealizationWeakEquivalences_of_integralChainComplexMap
    (h : ∀ ⦃X Y : SSet.{w}⦄ (f : X ⟶ Y), SSet.IsRealizationWeakEquivalence f →
      QuasiIso (SSet.chainComplexMap f (ModuleCat.of ℤ (ULift.{w} ℤ)))) :
    PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w} := by
  apply pointedSimplicialSetChainsPreserveRealizationWeakEquivalences_of_chainComplexMap
  intro X Y f hf
  exact (quasiIso_chainComplexMap_freePUnit_iff_liftedIntegers f).2 (h f hf)

end CategoryTheory.PointedSimplicialPresheaf
