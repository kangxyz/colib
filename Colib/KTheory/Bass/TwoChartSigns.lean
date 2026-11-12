/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Bass.TwoChart

/-!
Source: `Quillen/KTheory/Bass/TwoChartSigns.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The second-chart sign in Bass cokernels

The sum of the two original chart maps and their classical difference have canonically
isomorphic cokernels, using literal negation on the second summand. The original Laurent
representative map is fixed by this comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace KTheory.Bass

/-- The first chart is unchanged and the second chart is negated. -/
def secondChartNegation (A B : AddCommGrpCat.{u}) : A ⊞ B ≅ A ⊞ B where
  hom := biprod.map (𝟙 A) (-𝟙 B)
  inv := biprod.map (𝟙 A) (-𝟙 B)
  hom_inv_id := by apply biprod.hom_ext' <;> simp
  inv_hom_id := by apply biprod.hom_ext' <;> simp

/-- Precomposing the chart sum with the displayed involution gives the classical difference. -/
theorem secondChartNegation_sum {A B L : AddCommGrpCat.{u}} (p : A ⟶ L) (m : B ⟶ L) :
    (secondChartNegation A B).hom ≫ biprod.desc p m = biprod.desc p (-m) := by
  apply biprod.hom_ext' <;> simp [secondChartNegation]

/-- The actual sum and difference cokernels are compared without changing Laurent classes. -/
def chartSumDifferenceCokernelIso {A B L : AddCommGrpCat.{u}} (p : A ⟶ L) (m : B ⟶ L) :
    cokernel (biprod.desc p m) ≅ cokernel (biprod.desc p (-m)) :=
  cokernel.mapIso (biprod.desc p m) (biprod.desc p (-m))
    (secondChartNegation A B) (Iso.refl L) (by
      simpa using (secondChartNegation_sum p (-m)).symm)

/-- The comparison fixes the literal Laurent representative arrow. -/
@[reassoc]
theorem chartSumDifferenceCokernelIso_π {A B L : AddCommGrpCat.{u}}
    (p : A ⟶ L) (m : B ⟶ L) :
    cokernel.π (biprod.desc p m) ≫ (chartSumDifferenceCokernelIso p m).hom =
      cokernel.π (biprod.desc p (-m)) := by
  simp [chartSumDifferenceCokernelIso]

/-- A surjective pair of chart inclusions identifies the classical difference cokernel. -/
def chartDifferenceCokernelIsoOfEpi {A B X L : AddCommGrpCat.{u}}
    (i : A ⊞ B ⟶ X) [Epi i] (f : X ⟶ L) (p : A ⟶ L) (m : B ⟶ L)
    (h : i ≫ f = biprod.desc p m) : cokernel (biprod.desc p (-m)) ≅ cokernel f :=
  (chartSumDifferenceCokernelIso p m).symm ≪≫ cokernelIsoOfEq h.symm ≪≫ cokernelEpiComp i f

/-- Chart generation and second-summand negation leave each original target class unchanged. -/
@[reassoc]
theorem chartDifferenceCokernelIsoOfEpi_π {A B X L : AddCommGrpCat.{u}}
    (i : A ⊞ B ⟶ X) [Epi i] (f : X ⟶ L) (p : A ⟶ L) (m : B ⟶ L)
    (h : i ≫ f = biprod.desc p m) :
    cokernel.π (biprod.desc p (-m)) ≫ (chartDifferenceCokernelIsoOfEpi i f p m h).hom =
      cokernel.π f := by
  have hi : cokernel.π (biprod.desc p (-m)) ≫
      (chartSumDifferenceCokernelIso p m).inv = cokernel.π (biprod.desc p m) := by
    rw [← chartSumDifferenceCokernelIso_π p m, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  simp only [chartDifferenceCokernelIsoOfEpi, Iso.trans_hom, Iso.symm_hom,
    ← Category.assoc]
  rw [hi, π_comp_cokernelIsoOfEq_hom, cokernelEpiComp_hom, cokernel.π_desc]

end KTheory.Bass
