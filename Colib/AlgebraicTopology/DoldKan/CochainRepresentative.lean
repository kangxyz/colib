/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence

/-!
# Simplicial representatives of cochain complexes

The inverse Dold–Kan functor applied to the good nonpositive truncation of
a shifted cochain complex gives its simplicial additive representative.
This file records the normalization and the map correspondence on the
actual truncated complex.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace CochainComplex

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The actual good truncation at zero after shifting the coefficient complex. -/
def shiftedNonpositiveChains (p : ℤ) : CochainComplex A ℤ ⥤ ChainComplex A ℕ :=
  shiftFunctor _ p ⋙ (ComplexShape.embeddingUpIntLE 0).truncLE'Functor A

/-- A strict cochain map from extended nonpositive chains factors uniquely through
the good truncation of the shifted target. -/
def shiftedNonpositiveChainsHomEquiv (p : ℤ) (K : CochainComplex A ℤ)
    (P : ChainComplex A ℕ) :
    (P.extend (ComplexShape.embeddingUpIntLE 0) ⟶ K⟦p⟧) ≃
      (P ⟶ (shiftedNonpositiveChains A p).obj K) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let F := e.extendFunctor A
  let T := K⟦p⟧
  let ι := HomologicalComplex.ιTruncLE T e
  let c := T.truncLEIso e
  let mapToTarget : (P ⟶ T.truncLE' e) → ((F.obj P) ⟶ T) :=
    fun g ↦ F.map g ≫ c.inv ≫ ι
  refine (Equiv.ofBijective mapToTarget ⟨?_, ?_⟩).symm
  · intro f g h
    apply F.map_injective
    change F.map f ≫ c.inv ≫ ι = F.map g ≫ c.inv ≫ ι at h
    exact (cancel_mono (c.inv ≫ ι)).mp h
  · intro f
    let f' : P.extend e ⟶ T := f
    let a := HomologicalComplex.ιTruncLE (P.extend e) e
    have ha : IsIso a := by dsimp [a]; infer_instance
    let g := inv a ≫ HomologicalComplex.truncLEMap f' e ≫ c.hom
    have hn : HomologicalComplex.truncLEMap f' e ≫ ι = a ≫ f' :=
      HomologicalComplex.ιTruncLE_naturality f' e
    have hg : g ≫ c.inv ≫ ι = f' := by
      change (inv a ≫ HomologicalComplex.truncLEMap f' e ≫ c.hom) ≫ c.inv ≫ ι = f'
      calc
        _ = inv a ≫ (HomologicalComplex.truncLEMap f' e ≫ ι) := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
        _ = f' := by rw [hn]; simp
    refine ⟨(e.fullyFaithfulExtendFunctor A).preimage g, ?_⟩
    change F.map ((e.fullyFaithfulExtendFunctor A).preimage g) ≫ c.inv ≫ ι = f
    exact (congrArg (fun x ↦ x ≫ c.inv ≫ ι)
      ((e.fullyFaithfulExtendFunctor A).map_preimage g)).trans hg

/-- The simplicial additive representative of the shifted good truncation. -/
def simplicialRepresentative (p : ℤ) : CochainComplex A ℤ ⥤ SimplicialObject A :=
  shiftedNonpositiveChains A p ⋙ Abelian.DoldKan.equivalence.inverse

/-- Normalizing the actual simplicial representative recovers its truncation. -/
def simplicialRepresentativeNormalization (p : ℤ) (K : CochainComplex A ℤ) :
    (AlgebraicTopology.normalizedMooreComplex A).obj ((simplicialRepresentative A p).obj K) ≅
      (shiftedNonpositiveChains A p).obj K :=
  Abelian.DoldKan.equivalence.counitIso.app _

/-- Strict maps to the representative correspond to maps of the native normalized chains. -/
def simplicialRepresentativeHomEquiv (p : ℤ) (K : CochainComplex A ℤ) (X : SimplicialObject A) :
    (X ⟶ (simplicialRepresentative A p).obj K) ≃
      ((AlgebraicTopology.normalizedMooreComplex A).obj X ⟶
        (shiftedNonpositiveChains A p).obj K) :=
  (Abelian.DoldKan.equivalence.toAdjunction.homEquiv X _).symm

end CochainComplex

attribute [colib_tag "COL-0387"]
  CochainComplex.simplicialRepresentative
  CochainComplex.simplicialRepresentativeNormalization
  CochainComplex.simplicialRepresentativeHomEquiv
  CochainComplex.shiftedNonpositiveChainsHomEquiv
attribute [colib_ref "Voevodsky2003ReducedPowers" "Section 2, p. 3" "ingredient"
  "The additive simplicial representative of the shifted good truncation"]
  CochainComplex.simplicialRepresentative
