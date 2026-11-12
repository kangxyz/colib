/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalBoundaryDominance
public import Colib.AlgebraicGeometry.Correspondences.Composition.Pushforward

/-!
# Native finite correspondences produced by boundary-unit principal cycles

Each actual integral support of the native principal cycle is finite and dominates a
component of the source by the proper-boundary and smooth-relative-curve proofs.
It lifts to the retained open, and its original source-target map defines a finite
map to the correspondence ambient product. The cycle is the finite sum of its
original signed order coefficients multiplied by the actual residue-field degrees.
The prime summands are precisely native finite pushforwards, including image collisions.
No endpoint identity or incidence-Tor identification is asserted here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow.PrincipalBoundary

variable {C X Y S V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  (p : X ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
  [IsAffine X] [V.IsQuasiAffine] (q : C ⟶ X) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
  (f : Γ(C, U)) (hf : IsUnit f)
  (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ t)

/-- The native principal cycle, without changing its coefficients or cycle group. -/
abbrev cycle := principalCycle C (C.germToFunctionField U f)

/-- Its actual finite set of nonzero coefficients. -/
abbrev support := (cycle U f).support

omit [V.IsQuasiAffine] [IsOpenImmersion j] in
include hU hf in
theorem support_range (x : support U f) :
    Set.range (integralComponentAt x.val).subschemeι ⊆ Set.range j := by
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
  exact principalCycle_closure_subset_retained j U hU f hf x.val x.property

/-- The original integral support factors through the retained open. -/
def retainedMap (x : support U f) : (integralComponentAt x.val).subscheme ⟶ V :=
  IsOpenImmersion.lift j _ (support_range j U hU f hf x)

omit [V.IsQuasiAffine] in
@[reassoc (attr := simp)] theorem retainedMap_inclusion (x : support U f) :
    retainedMap j U hU f hf x ≫ j = (integralComponentAt x.val).subschemeι :=
  IsOpenImmersion.lift_fac _ _ _

/-- The source-target map is defined on the actual original integral support. -/
def componentMap (x : support U f) :
    (integralComponentAt x.val).subscheme ⟶ pullback p t :=
  pullback.lift ((integralComponentAt x.val).subschemeι ≫ q)
    (retainedMap j U hU f hf x ≫ g) (by
      rw [← retainedMap_inclusion j U hU f hf x]
      simpa only [Category.assoc] using
        congrArg (fun h => retainedMap j U hU f hf x ≫ h) hg)

omit [IsSeparated t] [LocallyOfFiniteType t] [IsAffine X] [IsProper q] [V.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)] in
@[reassoc (attr := simp)] theorem componentMap_fst (x : support U f) :
    componentMap p t q j U hU f hf g hg x ≫ pullback.fst p t =
      (integralComponentAt x.val).subschemeι ≫ q := pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency.types false in
instance componentMap_isFinite (x : support U f) :
    IsFinite (componentMap p t q j U hU f hf g hg x) := by
  have : IsFinite ((integralComponentAt x.val).subschemeι ≫ q) :=
    principalCycle_support_isFinite q j U hU f hf x.val x.property
  have : IsFinite (componentMap p t q j U hU f hf g hg x ≫ pullback.fst p t) := by
    rw [componentMap_fst]; infer_instance
  exact IsFinite.of_comp _ (pullback.fst p t)

/-- The image point of the actual generic point of the original integral support. -/
def imagePoint (x : support U f) : pullback (C := Scheme) p t := by
  let := isIntegral_integralComponentAt x.val
  exact componentMap p t q j U hU f hf g hg x
    (genericPoint (integralComponentAt x.val).subscheme)

set_option backward.isDefEq.respectTransparency.types false in
/-- Native finite-correspondence admissibility is produced, including dominance. -/
theorem imagePoint_admissible (x : support U f) :
    IsFiniteCorrespondencePoint p t (imagePoint p t q j U hU f hf g hg x) := by
  let D := integralComponentAt x.val
  let := isIntegral_integralComponentAt x.val
  let a := genericPoint D.subscheme
  let r := componentMap p t q j U hU f hf g hg x
  have hfin : IsFinite (D.subschemeι ≫ q) :=
    principalCycle_support_isFinite q j U hU f hf x.val x.property
  have hr : r ≫ pullback.fst p t = D.subschemeι ≫ q := componentMap_fst _ _ _ _ _ _ _ _ _ _ _
  have hcomp : (r ≫ pullback.fst p t).base ''
      ((integralComponentAt a).support : Set D.subscheme) ∈ irreducibleComponents X := by
    rw [coe_support_integralComponentAt, genericPoint_spec D.subscheme,
      Set.image_univ, hr]
    exact principalCycle_support_dominates_component q j U hU f hf x.val x.property
  constructor
  · apply finiteCyclePushforward_isFinite_integralComponentAt r (pullback.fst p t) a
    rw [Category.assoc, hr]
    infer_instance
  · rw [finiteCyclePushforward_range_integralComponentAt]
    exact finiteCyclePushforward_image_mem_irreducibleComponents r (pullback.fst p t) a hcomp

/-- Each original coefficient is pushed with its actual residue degree. -/
def componentCorrespondence (x : support U f) : finiteCorrespondences p t := by
  let := isIntegral_integralComponentAt x.val
  let a := genericPoint (integralComponentAt x.val).subscheme
  let r := componentMap p t q j U hU f hf g hg x
  exact ⟨single (imagePoint p t q j U hU f hf g hg x)
    ((cycle U f) x.val * (r.residueDegree a : ℤ)),
    single_mem_finiteCorrespondences p t _
      (imagePoint_admissible p t q j U hU f hf g hg x) _⟩

/-- This is the actual finite pushforward, not an unweighted image cycle. -/
theorem componentCorrespondence_val (x : support U f) :
    letI := isIntegral_integralComponentAt x.val
    (componentCorrespondence p t q j U hU f hf g hg x).val =
      finiteCyclePushforward (componentMap p t q j U hU f hf g hg x)
        (single (genericPoint (integralComponentAt x.val).subscheme) ((cycle U f) x.val)) := by
  rw [finiteCyclePushforward_single]
  rfl

/-- The signed principal correspondence constructed from the original boundary function.
The sum retains every source support, so distinct supports with equal image add their weights. -/
def correspondence : finiteCorrespondences p t := by
  classical
  let := (cycle U f).finite_support.fintype
  exact ∑ x : support U f, componentCorrespondence p t q j U hU f hf g hg x

/-- The entire produced correspondence is the sum of the actual weighted native
pushforwards of the original signed principal coefficients. -/
theorem correspondence_val :
    letI := (cycle U f).finite_support.fintype
    (correspondence p t q j U hU f hf g hg).val =
      ∑ x : support U f, (componentCorrespondence p t q j U hU f hf g hg x).val := by
  classical
  exact map_sum (finiteCorrespondences p t).subtype _ _

end Stacks.Chow.PrincipalBoundary
