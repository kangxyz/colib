/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ParameterChangeOfTopology
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Native complex and signed shift compatibility of the original parameter comparison

Extends the existing public `parameterNisnevichToEtaleComparison`, preserving its
original one-way map and assumptions. No second ordinary comparison is defined.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace AlgebraicGeometry.Scheme.SmoothSite
variable (S : Scheme.{u}) (T : SmoothSite S) (A : Type v) [Category.{w} A]
  [HasWeakSheafify (etaleTopology S) A]

section Complexes

variable [Abelian A] [HasSheafify (etaleTopology S) A]
  {ι : Type*} (c : ComplexShape ι)

/-- The same one-way target comparison on actual complexes, with native composite
functor comparisons included explicitly. It applies in particular to the signed target. -/
def parameterChangeOfTopologyComplexComparison :
    ((Contraction.parameterProduct T).sheafPushforwardContinuous A
        (nisnevichTopology S) (nisnevichTopology S)).mapHomologicalComplex c ⋙
        (nisnevichToEtaleSheaf S A).mapHomologicalComplex c ⟶
      (nisnevichToEtaleSheaf S A).mapHomologicalComplex c ⋙
        ((Contraction.parameterProduct T).sheafPushforwardContinuous A
          (etaleTopology S) (etaleTopology S)).mapHomologicalComplex c :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl _) c).hom ≫
    NatTrans.mapHomologicalComplex (parameterNisnevichToEtaleComparison S A T) c ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) c).inv

/-- Each degree uses the original target comparison, without any derived-sections step. -/
theorem parameterChangeOfTopologyComplexComparison_app_f
    (P : HomologicalComplex (Sheaf (nisnevichTopology S) A) c) (i : ι) :
    ((parameterChangeOfTopologyComplexComparison S T A c).app P).f i =
      (parameterNisnevichToEtaleComparison S A T).app (P.X i) := by
  simp only [parameterChangeOfTopologyComplexComparison, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, NatTrans.mapHomologicalComplex_app_f]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Native shift compatibility of the actual one-way target comparison. In particular,
the shift by one retains its negative differential; no new sign convention is imposed. -/
instance parameterChangeOfTopologyComplexComparison_commShift :
    NatTrans.CommShift (parameterChangeOfTopologyComplexComparison S T A (.up ℤ)) ℤ := by
  unfold parameterChangeOfTopologyComplexComparison
  infer_instance

/-- The target comparison commutes with every integer shift using native shift maps. -/
theorem parameterChangeOfTopologyComplexComparison_shift_square
    (P : CochainComplex (Sheaf (nisnevichTopology S) A) ℤ) (n : ℤ) :
    type_of% (NatTrans.shift_app_comm
      (parameterChangeOfTopologyComplexComparison S T A (.up ℤ)) n P) :=
  NatTrans.shift_app_comm (parameterChangeOfTopologyComplexComparison S T A (.up ℤ)) n P

end Complexes

end AlgebraicGeometry.Scheme.SmoothSite
