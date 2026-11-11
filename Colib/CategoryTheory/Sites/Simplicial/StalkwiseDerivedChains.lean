/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ReducedHypercohomology
public import Colib.CategoryTheory.Sites.Simplicial.ReducedNormalizedChainsFiber
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Conditional descent of reduced derived chains

Suppose reduced normalized chains of pointed simplicial sets send realization
weak equivalences to quasi-isomorphisms. On a site with enough points, the
fiber comparison then makes sheafified reduced derived chains descend to the
stalkwise localization. The simplicial-set implication is a premise.
-/

@[expose] public noncomputable section

open AlgebraicTopology CategoryTheory Limits

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

/-- Normalize the cokernel of free abelianization of a simplicial-set arrow.
For an arrow from a terminal simplicial set this is reduction at its basepoint. -/
abbrev reducedSimplicialSetArrowChains : Arrow SSet.{w} ⥤ ChainComplex AddCommGrpCat.{w} ℕ :=
  simplicialSetFreeAbelian.mapArrow ⋙ coker _ ⋙ normalizedMooreComplex _

/-- The input that reduced chains of pointed simplicial sets take realization
weak equivalences to quasi-isomorphisms. Both basepoints have terminal source. -/
def PointedSimplicialSetChainsPreserveRealizationWeakEquivalences : Prop :=
  ∀ ⦃P Q : Arrow SSet.{w}⦄ (g : P ⟶ Q), IsTerminal P.left → IsTerminal Q.left →
    SSet.IsRealizationWeakEquivalence g.right → QuasiIso (reducedSimplicialSetArrowChains.map g)

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  [LocallySmall.{w} C] [HasSheafify J AddCommGrpCat.{w}] [J.HasEnoughPoints.{w}]

/-- Under the pointed simplicial-set chain hypothesis, stalkwise weak
equivalences induce quasi-isomorphisms on sheafified reduced chains. -/
theorem quasiIso_sheafifiedReducedChains_map_of_stalkwise
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w})
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (hf : stalkwiseWeakEquivalences C J f) :
    QuasiIso ((sheafifiedReducedChains C J).map f) := by
  refine (quasiIso_sheafifiedReducedChains_map_iff (J := J) f).2 fun Φ ↦ ?_
  let g : Arrow.mk (Φ.presheafFiber.map X.hom) ⟶ Arrow.mk (Φ.presheafFiber.map Y.hom) :=
    Arrow.homMk' (𝟙 _) ((fiberAtPoint C Φ).map f) (by
      change 𝟙 _ ≫ Φ.presheafFiber.map Y.hom =
        Φ.presheafFiber.map X.hom ≫ Φ.presheafFiber.map f.right
      rw [Category.id_comp, ← Functor.map_comp, Under.w f])
  have hg : simplicialSetFreeAbelian.mapArrow.map g = (fiberBasepointArrow Φ).map f := by
    apply Arrow.hom_ext
    · exact simplicialSetFreeAbelian.map_id _
    · rfl
  have hq := h g (isTerminalFiberTerminal Φ) (isTerminalFiberTerminal Φ)
    ((stalkwiseWeakEquivalences_iff C f).1 hf Φ)
  change QuasiIso ((normalizedMooreComplex _).map
    ((coker _).map (simplicialSetFreeAbelian.mapArrow.map g))) at hq
  rw [hg] at hq
  exact hq

variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{w})]

/-- Under the pointed simplicial-set chain hypothesis, the selected reduced
derived-chain functor inverts stalkwise weak equivalences. -/
theorem stalkwiseWeakEquivalences_isInvertedBy_reducedDerivedChains
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w}) :
    (stalkwiseWeakEquivalences C J).IsInvertedBy (reducedDerivedChains C J) := by
  intro X Y f hf
  change IsIso (DerivedCategory.Q.map ((reducedCochains C J).map f))
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  change QuasiIso (HomologicalComplex.extendMap ((sheafifiedReducedChains C J).map f)
    (ComplexShape.embeddingUpIntLE 0))
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2
    (quasiIso_sheafifiedReducedChains_map_of_stalkwise C J h f hf)

/-- Under the pointed simplicial-set chain hypothesis, reduced derived
chains descend to the stalkwise homotopy category. -/
def stalkwiseReducedDerivedChains
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w}) :
    StalkwiseHomotopyCategory.{w} C J ⥤ DerivedCategory (Sheaf J AddCommGrpCat.{w}) :=
  Localization.lift (reducedDerivedChains C J)
    (stalkwiseWeakEquivalences_isInvertedBy_reducedDerivedChains C J h)
    (toStalkwiseHomotopyCategory C J)

/-- Under the same hypothesis, pulling back the descended functor recovers
the selected reduced derived-chain functor. -/
def stalkwiseReducedDerivedChainsFactors
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w}) :
    toStalkwiseHomotopyCategory C J ⋙ stalkwiseReducedDerivedChains C J h ≅
      reducedDerivedChains C J :=
  Localization.fac (reducedDerivedChains C J)
    (stalkwiseWeakEquivalences_isInvertedBy_reducedDerivedChains C J h)
    (toStalkwiseHomotopyCategory C J)

end CategoryTheory.PointedSimplicialPresheaf
