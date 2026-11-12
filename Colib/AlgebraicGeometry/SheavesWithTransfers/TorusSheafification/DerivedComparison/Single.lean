/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Acyclic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# The actual derived torus comparison on a single coefficient

Every term of the single complex is A¹-invariant. The termwise
sheafification comparison and the derived unit on the corresponding
bounded-below acyclic complex are therefore both invertible.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers

variable (k : Type u) [Field k]

private theorem singleFunctor_term_isA1Invariant (P : PresheafWithTransfers.{u + 1} k)
    (hP : P.IsA1Invariant) (n i : ℤ) :
    (((CochainComplex.singleFunctor _ n).obj P).X i).IsA1Invariant := by
  by_cases hi : i = n
  · subst i
    exact hP.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) n P).symm
  · exact isA1Invariant_of_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) n P i hi)

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The exact derived comparison is invertible on an A¹-invariant
coefficient placed in any degree. -/
theorem isIso_torusSectionsDerivedSheafificationComparison_app_single
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) (n : ℤ) :
    IsIso ((torusSectionsDerivedSheafificationComparison k).app
      ((DerivedCategory.singleFunctor _ n).obj P)) := by
  let K := (CochainComplex.singleFunctor (PresheafWithTransfers.{u + 1} k) n).obj P
  let L := ((nisnevichSheafify k).mapHomologicalComplex (.up ℤ)).obj K
  have hTerm (i : ℤ) : (K.X i).IsA1Invariant := singleFunctor_term_isA1Invariant k P hP n i
  let (i : ℤ) : IsIso ((torusSectionsSheafificationComplexMap k (.up ℤ) K).f i) :=
    isIso_torusSectionsSheafificationComparison k _ (hTerm i)
  let : IsIso (torusSectionsSheafificationComplexMap k (.up ℤ) K) :=
    HomologicalComplex.Hom.isIso_of_components _
  let : K.IsStrictlyGE n := inferInstanceAs
    (((CochainComplex.singleFunctor (PresheafWithTransfers.{u + 1} k) n).obj P).IsStrictlyGE n)
  have hL : CochainComplex.plus _ L := ⟨n, inferInstance⟩
  let : IsIso ((torusSectionsDerivedUnit k).app L) :=
    isIso_torusSectionsDerivedUnit_app_of_rightAcyclic k L hL (fun i =>
      torusSectionsFunctor_rightAcyclic_of_perfect k _
        (nisnevichSheafify_isA1Invariant _ (hTerm i)))
  have hIso : IsIso ((torusSectionsDerivedSheafificationComparison k).app
      (DerivedCategory.Q.obj K)) := by
    rw [torusSectionsDerivedSheafificationComparison_app_Q_obj]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso _
    ((DerivedCategory.singleFunctorIsoCompQ (PresheafWithTransfers.{u + 1} k) n).app P)).2 hIso

end AlgebraicGeometry.SheafWithTransfers
