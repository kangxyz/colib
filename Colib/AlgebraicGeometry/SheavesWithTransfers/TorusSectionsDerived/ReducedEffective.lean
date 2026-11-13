/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Effective
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedFunctor
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Reduced derived torus sections of effective coefficients

The original constant sections make the kernel of unit restriction a
retract of total derived torus sections. Upper bounds and A¹-invariance
descend along that retract.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

private theorem isA1Invariant_of_retract {P Q : PresheafWithTransfers.{u + 1} k}
    (e : Retract P Q) (hQ : Q.IsA1Invariant) : P.IsA1Invariant := by
  intro X
  let U := toPresheaf k
  let d := ((SmoothSite.Contraction.projection
    (SmoothSite.additiveGroupObject (Spec (.of k)))).app X).op
  let F := U.obj P
  let G := U.obj Q
  let s := e.map U
  let a : RetractArrow (F.map d) (G.map d) :=
    { i := Arrow.homMk' (s.i.app _) (s.i.app _) (s.i.naturality d).symm
      r := Arrow.homMk' (s.r.app _) (s.r.app _) (s.r.naturality d).symm
      retract :=
        Arrow.hom_ext _ _ (NatTrans.congr_app s.retract _) (NatTrans.congr_app s.retract _) }
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _) a (hQ X)

variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [PerfectField k]

private def reducedTorusSectionsRetract
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) :
    Retract ((reducedTorusSectionsDerivedFunctor k).obj K)
      ((torusSectionsDerivedFunctor k).obj K) where
  i := (reducedTorusSectionsDerivedInclusion k).app K
  r := (reducedTorusSectionsDerivedProjection k).app K
  retract := reducedTorusSectionsDerivedInclusion_projection k K

/-- Reduced derived torus sections retain the upper bound of an
A¹-invariant bounded-above complex. -/
theorem reducedTorusSectionsDerived_isLE_of_isLE_of_isA1Invariant
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) (b : ℤ) [K.IsLE b]
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).obj.IsA1Invariant) :
    ((reducedTorusSectionsDerivedFunctor k).obj K).IsLE b := by
  let R := torusSectionsDerivedFunctor k
  let : (R.obj K).IsLE b := torusSectionsDerived_isLE_of_isLE_of_isA1Invariant k K b hK
  rw [DerivedCategory.isLE_iff]
  intro i hi
  let e := (reducedTorusSectionsRetract k K).map (DerivedCategory.homologyFunctor _ i)
  exact IsZero.of_epi e.r (DerivedCategory.isZero_of_isLE (R.obj K) b i hi)

/-- Reduced derived torus sections preserve A¹-invariant cohomology. -/
theorem reducedTorusSectionsDerived_homology_isA1Invariant
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k))
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).obj.IsA1Invariant) (i : ℤ) :
    PresheafWithTransfers.IsA1Invariant
      (((DerivedCategory.homologyFunctor _ i).obj
        ((reducedTorusSectionsDerivedFunctor k).obj K)).obj) :=
  isA1Invariant_of_retract k
    ((reducedTorusSectionsRetract k K).map
      (DerivedCategory.homologyFunctor _ i ⋙ SheafWithTransfers.forget k))
    (torusSectionsDerived_homology_isA1Invariant k K hK i)

end AlgebraicGeometry.SheafWithTransfers
