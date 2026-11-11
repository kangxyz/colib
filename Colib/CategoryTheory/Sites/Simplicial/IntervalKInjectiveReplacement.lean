/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalHom
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseKInjectiveReplacement

/-!
# Interval-local representatives of cochain complexes

The pointed representative of the chosen functorial K-injective resolution
is interval-local precisely when reduced hypercohomology with the original
coefficients is invariant under the pointed cylinder projections.
-/

@[expose] public noncomputable section

open Opposite

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
  [IsGrothendieckAbelian.{w} (Sheaf J AddCommGrpCat.{w})]
  [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{w})] [J.HasEnoughPoints.{w}]
  (I : Cᵒᵖ ⥤ SSet.{w})
  (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w})
  (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)

include h

/-- The chosen K-injective representative is local exactly when each cylinder
projection acts bijectively on reduced hypercohomology with the original coefficients. -/
theorem isIntervalLocal_pointedKInjectiveCochainRepresentative_iff :
    IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj
      ((pointedKInjectiveCochainRepresentative C J p).obj K)) ↔
      ∀ X : PointedSimplicialPresheaf.{w} C,
        Function.Bijective ((reducedHypercohomology C J K p).map
          (cylinderProjection X I).op) := by
  change (∀ X, _) ↔ ∀ X, _
  refine forall_congr' fun X ↦ ?_
  let Q := toStalkwiseHomotopyCategory.{w} C J
  let R := (pointedKInjectiveCochainRepresentative C J p).obj K
  let F := reducedHypercohomology C J K p
  let g := cylinderProjection X I
  let e := stalkwiseKInjectiveReplacementHomEquiv C J h p K X
  let e' := stalkwiseKInjectiveReplacementHomEquiv C J h p K (parameterizedCylinder X I)
  change Function.Bijective (fun a : Q.obj X ⟶ Q.obj R ↦ Q.map g ≫ a) ↔
    Function.Bijective (F.map g.op)
  have he : (fun a : Q.obj X ⟶ Q.obj R ↦ Q.map g ≫ a) =
      e'.symm ∘ F.map g.op ∘ e := by
    funext a
    apply e'.injective
    change e' (Q.map g ≫ a) = e' (e'.symm (F.map g.op (e a)))
    rw [e'.apply_symm_apply]
    exact stalkwiseKInjectiveReplacementHomEquiv_naturality C J h p K g a
  rw [he, Function.Bijective.of_comp_iff' e'.symm.bijective _,
    Function.Bijective.of_comp_iff _ e.bijective]

variable (hK : ∀ X : PointedSimplicialPresheaf.{w} C,
  Function.Bijective ((reducedHypercohomology C J K p).map (cylinderProjection X I).op))

/-- Under the cylinder invariance hypothesis, maps in the interval localization
represent reduced hypercohomology with the original coefficients. -/
def intervalKInjectiveReplacementHomEquiv (X : PointedSimplicialPresheaf.{w} C) :
    ((toIntervalHomotopyCategory C J I).obj X ⟶
      (toIntervalHomotopyCategory C J I).obj
        ((pointedKInjectiveCochainRepresentative C J p).obj K)) ≃
      (reducedHypercohomology C J K p).obj (op X) :=
  (intervalLocalHomEquiv C J I ((pointedKInjectiveCochainRepresentative C J p).obj K)
    ((isIntervalLocal_pointedKInjectiveCochainRepresentative_iff C J I h p K).mpr hK) X).trans
    (stalkwiseKInjectiveReplacementHomEquiv C J h p K X)

/-- The interval comparison sends precomposition to the original restriction map. -/
theorem intervalKInjectiveReplacementHomEquiv_naturality
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (a : (toIntervalHomotopyCategory C J I).obj Y ⟶
      (toIntervalHomotopyCategory C J I).obj
        ((pointedKInjectiveCochainRepresentative C J p).obj K)) :
    intervalKInjectiveReplacementHomEquiv C J I h p K hK X
        ((toIntervalHomotopyCategory C J I).map f ≫ a) =
      (reducedHypercohomology C J K p).map f.op
        (intervalKInjectiveReplacementHomEquiv C J I h p K hK Y a) := by
  let R := (pointedKInjectiveCochainRepresentative C J p).obj K
  have hR : IsIntervalLocal C J I ((toStalkwiseHomotopyCategory C J).obj R) :=
    (isIntervalLocal_pointedKInjectiveCochainRepresentative_iff C J I h p K).mpr hK
  change stalkwiseKInjectiveReplacementHomEquiv C J h p K X
    (intervalLocalHomEquiv C J I R hR X ((toIntervalHomotopyCategory C J I).map f ≫ a)) = _
  rw [intervalLocalHomEquiv_naturality]
  exact stalkwiseKInjectiveReplacementHomEquiv_naturality C J h p K f _

end CategoryTheory.PointedSimplicialPresheaf
