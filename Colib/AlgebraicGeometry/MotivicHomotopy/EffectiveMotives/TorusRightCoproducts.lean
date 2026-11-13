/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusRight
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Coproducts
import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# Uniformly bounded direct sums and effective torus sections

A family of effective motives with a common cohomological upper bound
has the same direct sum as its original derived family. The actual
reduced right functor preserves these direct sums.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

variable {I : Type (u + 1)} (K : I → EffectiveMotivesMinus k) (b : ℤ)

/-- The coproduct of an effective family with a common upper bound
is represented by its native derived coproduct. -/
def effectiveCofan
    (hK : ∀ j, ((effectiveMotivesMinusToDerived k).obj (K j)).IsLE b) : Cofan K := by
  let A := SheafWithTransfers.{u + 1} k
  let V := effectiveMotivesMinusToDerived k
  let M := fun j => V.obj (K j)
  let : HasCoproductsOfShape I (DerivedCategory A) :=
    Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory A I
  let P : EffectiveMotivesMinus k :=
    ⟨⟨∐ M, b, by exact Stacks.Duality.isLE_sigmaObj A M b hK⟩,
      a1InvariantCohomology_sigma k M (fun j => (K j).property)⟩
  exact Cofan.mk P (fun j => ObjectProperty.homMk (ObjectProperty.homMk (Sigma.ι M j)))

private def effectiveMotivesMinusToDerivedFullyFaithful :
    (effectiveMotivesMinusToDerived k).FullyFaithful :=
  (ObjectProperty.fullyFaithfulι (effectiveCohomologyCondition k)).comp
    (ObjectProperty.fullyFaithfulι
      (DerivedCategory.TStructure.t (C := SheafWithTransfers.{u + 1} k)).minus)

/-- The cofan of the original derived coproduct is colimiting in
effective motives. -/
@[no_expose]
def effectiveCofanIsColimit
    (hK : ∀ j, ((effectiveMotivesMinusToDerived k).obj (K j)).IsLE b) :
    IsColimit (C := EffectiveMotivesMinus k) (J := Discrete I) (effectiveCofan k K b hK) := by
  let A := SheafWithTransfers.{u + 1} k
  let V := effectiveMotivesMinusToDerived k
  let M := fun j => V.obj (K j)
  let : HasCoproductsOfShape I (DerivedCategory A) :=
    Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory A I
  let e := effectiveMotivesMinusToDerivedFullyFaithful k
  let : V.Full := e.full
  let : V.Faithful := e.faithful
  let hV : ReflectsColimitsOfShape (Discrete I) V :=
    (fullyFaithful_reflectsColimits V).reflectsColimitsOfShape
  unfold effectiveCofan
  refine isColimitOfIsColimitCofanMkObj V K _ ?_
  exact coproductIsCoproduct M

variable [PerfectField k] [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The effective reduced right functor preserves each direct sum with
a common upper bound. -/
theorem effectiveReducedTorusSections_preservesColimit
    (hK : ∀ j, ((effectiveMotivesMinusToDerived k).obj (K j)).IsLE b) :
    PreservesColimit (Discrete.functor K) (effectiveReducedTorusSectionsFunctor k) := by
  let A := SheafWithTransfers.{u + 1} k
  let V := effectiveMotivesMinusToDerived k
  let E := effectiveReducedTorusSectionsFunctor k
  let R := reducedTorusSectionsDerivedFunctor k
  let M := fun j => V.obj (K j)
  let : HasCoproductsOfShape I (DerivedCategory A) :=
    Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory A I
  let e := effectiveMotivesMinusToDerivedFullyFaithful k
  let : V.Full := e.full
  let : V.Faithful := e.faithful
  let hV : ReflectsColimitsOfShape (Discrete I) V :=
    (fullyFaithful_reflectsColimits V).reflectsColimitsOfShape
  let hR : IsIso (sigmaComparison R M) :=
    isIso_sigmaComparison_reducedTorusSectionsDerived k M (fun j => (K j).property)
  let : PreservesColimit (Discrete.functor M) R :=
    PreservesCoproduct.of_iso_comparison R M
  let t : IsColimit (Cofan.mk (R.obj (∐ M)) (fun j => R.map (Sigma.ι M j))) :=
    isColimitOfHasCoproductOfPreservesColimit R M
  apply preservesColimit_of_preserves_colimit_cocone (effectiveCofanIsColimit k K b hK)
  apply isColimitOfReflects V
  let c := effectiveCofan k K b hK
  let f := (Discrete.functor K) ⋙ E
  let F := fun j => (V ⋙ R).obj (K j)
  change IsColimit (V.mapCocone (E.mapCocone c))
  let d : f ⋙ V ≅ Discrete.functor F := Discrete.natIso (fun j => Iso.refl (F j.as))
  refine ((IsColimit.precomposeHomEquiv d _).symm t).ofIsoColimit ?_
  refine Cocone.ext (Iso.refl _) (fun j => ?_)
  change (d.hom.app j ≫ R.map (Sigma.ι M j.as)) ≫ 𝟙 _ = V.map (E.map (c.ι.app j))
  rw [Category.comp_id]
  unfold c effectiveCofan
  exact Category.id_comp _

end AlgebraicGeometry.MotivicHomotopy
