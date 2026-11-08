/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.IntervalMultiplication
public import Colib.AlgebraicGeometry.Simplex.EndpointHomotopy

/-!
# Ordinary algebraic singular chains are interval homotopy invariant

The actual multiplication contraction of the barycentric interval and the
actual prism homotopy show that projection `U × Δ¹ → U` induces a native
`HomotopyEquiv` on the original evaluated ordinary singular-chain presheaf.
The inverse is the original restriction along barycentric vertex zero.

No new chain carrier, generic interval parameter package, transfer action, or
homotopy-invariance assumption on the coefficient presheaf is introduced.
Equality in each homology degree is strengthened to an isomorphism whose
forward map is the original restriction along projection.

The published references are MVW2006, Lemma 2.16 and its multiplication proof,
Lemma 2.18, and Corollary 2.19, printed pp. 17-18. The ordinary geometric
argument is extended to arbitrary commutative base rings and preadditive
coefficients. This is not the transfer-valued or motivic-derived comparison, nor the
covariant representable-presheaf assertion of Corollary 2.24.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme
open scoped Simplicial

universe u v w

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Preadditive A]
variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)

/-- Identity restriction on the existing chain presheaf is the identity chain map. -/
theorem singularChains_restriction_id (U : SmoothSite (Spec (.of R))) :
    (NatTrans.mapHomologicalComplex ((evaluation _ A).map (𝟙 U).op)
      (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P) = 𝟙 _ := by
  simp

/-- The original evaluated restriction maps retain contravariant composition. -/
theorem singularChains_restriction_comp {U V W : SmoothSite (Spec (.of R))}
    (f : U ⟶ V) (g : V ⟶ W) :
    (NatTrans.mapHomologicalComplex ((evaluation _ A).map (f ≫ g).op)
      (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P) =
        (NatTrans.mapHomologicalComplex ((evaluation _ A).map g.op)
          (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P) ≫
            (NatTrans.mapHomologicalComplex ((evaluation _ A).map f.op)
              (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P) := by
  rw [op_comp, Functor.map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/-- A genuine geometric interval map yields a homotopy on the original chains. -/
def ordinaryIntervalMapHomotopy {U V : SmoothSite (Spec (.of R))}
    (h : SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌) ⟶ V) :
    _root_.Homotopy
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map (intervalInclusion R U 0 ≫ h).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P))
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map (intervalInclusion R U 1 ≫ h).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) :=
  (_root_.Homotopy.ofEq (singularChains_restriction_comp R P _ h)).trans
    (((ordinaryIntervalEndpointHomotopy R P U).compLeft
      ((NatTrans.mapHomologicalComplex ((evaluation _ A).map h.op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P))).trans
          (_root_.Homotopy.ofEq (singularChains_restriction_comp R P _ h).symm))

/-- Projection induces a chain homotopy equivalence on the original singular chains.
Its inverse is the original barycentric vertex-zero restriction. -/
@[colib_ref "MVW2006" "Lecture 2, Lemmas 2.16 and 2.18; Corollary 2.19, pp. 17-18"
  "generalization" "Actual interval projection is a chain homotopy equivalence over any base ring"]
def ordinaryIntervalHomotopyEquiv (U : SmoothSite (Spec (.of R))) :
    _root_.HomotopyEquiv
      ((((evaluation _ A).obj (op U)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((singularChainsFunctor R).obj P))
      ((((evaluation _ A).obj
        (op (SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌)))).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj ((singularChainsFunctor R).obj P)) where
  hom := (NatTrans.mapHomologicalComplex
    ((evaluation _ A).map
      (SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋1⦌)).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)
  inv := (NatTrans.mapHomologicalComplex ((evaluation _ A).map (intervalInclusion R U 0).op)
    (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)
  homotopyHomInvId := _root_.Homotopy.ofEq (by
    rw [← singularChains_restriction_comp, intervalInclusion_fst,
      singularChains_restriction_id])
  homotopyInvHomId := by
    simpa only [intervalInclusion_zero_comp_intervalContraction,
      intervalInclusion_one_comp_intervalContraction, singularChains_restriction_comp,
      singularChains_restriction_id] using
        ordinaryIntervalMapHomotopy R P (intervalContraction R U)

/-- The forward map of the equivalence is exactly restriction along projection. -/
theorem ordinaryIntervalHomotopyEquiv_hom (U : SmoothSite (Spec (.of R))) :
    (ordinaryIntervalHomotopyEquiv R P U).hom =
      (NatTrans.mapHomologicalComplex
        ((evaluation _ A).map
          (SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋1⦌)).op)
            (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P) := rfl

/-- The inverse map is exactly restriction along the original vertex-zero inclusion. -/
theorem ordinaryIntervalHomotopyEquiv_inv (U : SmoothSite (Spec (.of R))) :
    (ordinaryIntervalHomotopyEquiv R P U).inv =
      (NatTrans.mapHomologicalComplex ((evaluation _ A).map (intervalInclusion R U 0).op)
        (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P) := rfl

variable [CategoryWithHomology A]

/-- The actual projection induces an isomorphism in every ordinary singular homology degree. -/
def ordinaryIntervalHomologyIso (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (((((evaluation _ A).obj (op U)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((singularChainsFunctor R).obj P)).homology n) ≅
        (((((evaluation _ A).obj
          (op (SmoothSite.product U ((cosimplicialSmoothSite R).obj ⦋1⦌)))).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj ((singularChainsFunctor R).obj P)).homology n) :=
  (ordinaryIntervalHomotopyEquiv R P U).toHomologyIso n

/-- The homology isomorphism retains the original projection restriction. -/
theorem ordinaryIntervalHomologyIso_hom (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    (ordinaryIntervalHomologyIso R P U n).hom =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          ((evaluation _ A).map
            (SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋1⦌)).op)
              (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) n := rfl

/-- Homotopy invariance is a property of the original projection-induced homology map. -/
theorem isIso_ordinaryInterval_homologyMap (U : SmoothSite (Spec (.of R))) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex
        ((evaluation _ A).map
          (SmoothSite.productFst U ((cosimplicialSmoothSite R).obj ⦋1⦌)).op)
            (ComplexShape.down ℕ)).app ((singularChainsFunctor R).obj P)) n) := by
  change IsIso (ordinaryIntervalHomologyIso R P U n).hom
  infer_instance

end AlgebraicSimplex

attribute [colib_tag "COL-0320"] AlgebraicSimplex.ordinaryIntervalHomotopyEquiv
attribute [colib_tag "COL-0320"] AlgebraicSimplex.ordinaryIntervalHomologyIso
attribute [colib_tag "COL-0320"] AlgebraicSimplex.isIso_ordinaryInterval_homologyMap
