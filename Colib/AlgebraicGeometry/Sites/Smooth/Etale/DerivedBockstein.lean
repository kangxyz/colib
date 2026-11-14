/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedNaturality
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Derived

/-!
# The actual signed Bockstein comparison in consecutive degrees

The Nisnevich and etale groups retain their original coefficient complexes.
Native derived shift coherence makes the comparison square land in degree `p + 1`,
not just in degree `p` of a shifted coefficient complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE

universe u w w'

namespace AlgebraicGeometry.Scheme.SmoothSite
variable (S : Scheme.{u})
variable [HasSheafify (nisnevichTopology S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{w} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'} (Sheaf (etaleTopology S) AddCommGrpCat.{u + 1})]
/-- The original signed Nisnevich coefficient boundary in consecutive degrees. -/
def derivedBocksteinDegree
    (X : SmoothSite S)
    (K : CochainComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (n : ℕ) (p : ℤ) :
    ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{u + 1} (nisnevichTopology S)).obj X) ⟶
      (DerivedCategory.Q.obj (CochainComplex.finiteCoefficients K n))⟦p⟧) →+
    ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{u + 1} (nisnevichTopology S)).obj X) ⟶
      (DerivedCategory.Q.obj K)⟦p + 1⟧) where
  toFun f := f ≫ CochainComplex.finiteCoefficients.derivedBockstein K n p
  map_zero' := by simp
  map_add' f g := by simp [Preadditive.add_comp]
/-- The actual mapped signed etale coefficient boundary in consecutive degrees. -/
def etaleDerivedBocksteinDegree
    (X : SmoothSite S)
    (K : CochainComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (n : ℕ) (p : ℤ) :
    ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{u + 1} (etaleTopology S)).obj X) ⟶
      (DerivedCategory.Q.obj
        (((nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.finiteCoefficients K n)))⟦p⟧) →+
    ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{u + 1} (etaleTopology S)).obj X) ⟶
      (DerivedCategory.Q.obj
        (((nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).obj K))
        ⟦p + 1⟧) where
  toFun f := f ≫ CochainComplex.finiteCoefficients.mappedDerivedBockstein
    (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}) K n p
  map_zero' := by simp
  map_add' f g := by simp [Preadditive.add_comp]
/-- The actual exact derived comparison preserves the original signed Bockstein,
including normalization to the next cohomological degree. -/
@[colib_tag "COL-1228", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:39-132" "ingredient"
  "The exact derived lift and its native localization and shift-compatible factors"]
theorem nisnevichToEtaleDerivedHomMap_bockstein_degree (X : SmoothSite S)
    (K : CochainComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (n : ℕ) (p : ℤ)
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (nisnevichTopology S)).obj X) ⟶
      (DerivedCategory.Q.obj (CochainComplex.finiteCoefficients K n))⟦p⟧) :
    nisnevichToEtaleDerivedHomMap S X K (p + 1) (derivedBocksteinDegree S X K n p f) =
      etaleDerivedBocksteinDegree S X K n p
        (nisnevichToEtaleDerivedHomMap S X (CochainComplex.finiteCoefficients K n) p f) := by
  simp only [derivedBocksteinDegree, etaleDerivedBocksteinDegree,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [nisnevichToEtaleDerivedHomMap_formula, nisnevichToEtaleDerivedHomMap_formula]
  simp only [nisnevichToEtaleDerivedTargetIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [CochainComplex.finiteCoefficients.mapDerivedCategory_derivedBockstein]

end AlgebraicGeometry.Scheme.SmoothSite
