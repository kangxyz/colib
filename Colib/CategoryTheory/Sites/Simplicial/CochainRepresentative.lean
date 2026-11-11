/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicTopology.DoldKan.CochainRepresentative
public import Colib.CategoryTheory.Sites.Simplicial.AbelianPresheaf
public import Colib.CategoryTheory.Sites.Simplicial.ReducedHypercohomology
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Pointed presheaf representatives of coefficient complexes

Apply the inverse Dold–Kan functor to the good truncation of the
shifted sheaf complex, then take its underlying presheaf with the
actual additive zero as basepoint. The strict map comparison uses
reduced free chains and degreewise sheafification for the chosen topology.

The derived comparison for a local fibrant representative is a separate
statement.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- The pointed underlying simplicial presheaf of the good truncation of a shifted complex. -/
def pointedCochainRepresentative (p : ℤ) :
    CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ ⥤ PointedSimplicialPresheaf.{w} C :=
  CochainComplex.simplicialRepresentative _ p ⋙
    (Functor.whiskeringRight _ _ _).obj (sheafToPresheaf J AddCommGrpCat.{w}) ⋙
    pointedUnderlyingAbelian C

/-- The right adjoint of the actual sheafified reduced normalized chains. -/
def reducedChainsForgetAdjunction : sheafifiedReducedChains.{w} C J ⊣
    Abelian.DoldKan.equivalence.inverse ⋙
      (Functor.whiskeringRight _ _ _).obj (sheafToPresheaf J AddCommGrpCat.{w}) ⋙
      pointedUnderlyingAbelian C :=
  ((reducedFreeForgetAdjunction C).comp
    ((sheafificationAdjunction J AddCommGrpCat.{w}).whiskerRight SimplexCategoryᵒᵖ)).comp
      Abelian.DoldKan.equivalence.toAdjunction

/-- The strict map correspondence with the same reduced chains used in cohomology. -/
def pointedCochainRepresentativeHomEquiv (p : ℤ)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (X : PointedSimplicialPresheaf.{w} C) :
    (X ⟶ (pointedCochainRepresentative C J p).obj K) ≃
      ((sheafifiedReducedChains C J).obj X ⟶
        (CochainComplex.shiftedNonpositiveChains _ p).obj K) :=
  ((reducedChainsForgetAdjunction C J).homEquiv X _).symm

/-- Strict pointed maps correspond to cochain maps from the actual reduced source
into the shifted coefficient complex. -/
def pointedCochainRepresentativeCochainHomEquiv (p : ℤ)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (X : PointedSimplicialPresheaf.{w} C) :
    (X ⟶ (pointedCochainRepresentative C J p).obj K) ≃
      ((reducedCochains C J).obj X ⟶ K⟦p⟧) :=
  (pointedCochainRepresentativeHomEquiv C J p K X).trans
    (CochainComplex.shiftedNonpositiveChainsHomEquiv _ p K
      ((sheafifiedReducedChains C J).obj X)).symm

end CategoryTheory.PointedSimplicialPresheaf
