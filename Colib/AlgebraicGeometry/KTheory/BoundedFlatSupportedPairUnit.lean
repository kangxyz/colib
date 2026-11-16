/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterSupportedTrack
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIdentityAction
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatTensorUnitSupportedEvaluationUnit

/-!
# Arbitrary global scalar units on the original supported pair Models

The existing Laurent unit is the specialization of this arbitrary global scalar
lift through the original supported inclusion. Every actual open-pair square
preserves it whenever its genuine pullback sends the source scalar to the target
scalar. Consequently all original transformation-cylinder times are retained.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedPairUnit.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedPairUnit
open GlobalSupportedSection


private theorem preservesRestricted {C D : Type*} [Category C] [Category D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (hF : ∀ x : P.FullSubcategory, Q (F.obj x.obj))
    (α : 𝟭 C ≅ 𝟭 C) (β : 𝟭 D ≅ 𝟭 D) (h : Preserves F α β) :
    Preserves (Q.lift (P.ι ⋙ F) hF) (lift P.ι α) (lift Q.ι β) := by
  intro x
  apply ObjectProperty.hom_ext
  change F.map (((lift P.ι α).hom.app x).hom) =
    ((lift Q.ι β).hom.app ((Q.lift (P.ι ⋙ F) hF).obj x)).hom
  rw [show ((lift P.ι α).hom.app x).hom = α.hom.app x.obj from map_lift_hom P.ι α x,
    show ((lift Q.ι β).hom.app ((Q.lift (P.ι ⋙ F) hF).obj x)).hom =
      β.hom.app (F.obj x.obj) from map_lift_hom Q.ι β _]
  exact h x.obj

/-- The full supported inclusion retains the original arbitrary global scalar. -/
theorem forget_preserves (A : Scheme.OpenPairs.{u}) (r : (Γ(A.right, ⊤))ˣ) :
    Preserves (boundedAboveFlatGlobalSupportedForget (X := op A.right) A.hom).hom.toFunctor
      (SupportedTensorEvaluation.unit (X := op A.right) A.hom r)
      (boundedAboveFlatGlobalSectionUnit (op A.right) r) := by
  have h : Preserves (boundedAboveFlatGlobalSectionSupported (X := op A.right) A.hom).ι
      (lift (boundedAboveFlatGlobalSectionSupported (X := op A.right) A.hom).ι
        (boundedAboveFlatGlobalSectionUnit (op A.right) r))
      (boundedAboveFlatGlobalSectionUnit (op A.right) r) := fun K =>
    map_lift_hom (boundedAboveFlatGlobalSectionSupported (X := op A.right) A.hom).ι
      (boundedAboveFlatGlobalSectionUnit _ r) K
  exact h

/-- An actual scalar equation gives the original supported pair-map preservation law. -/
theorem pairMap_preserves_of_eq {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (r : (Γ(B.right, ⊤))ˣ) (s : (Γ(A.right, ⊤))ˣ)
    (h : Units.map g.right.appTop.hom.toMonoidHom r = s) :
    Preserves (boundedAboveFlatGlobalSupportedPairModelMap g).hom.toFunctor
      (SupportedTensorEvaluation.unit (X := op B.right) B.hom r)
      (SupportedTensorEvaluation.unit (X := op A.right) A.hom s) :=
  preservesRestricted (boundedAboveFlatGlobalSectionSupported (X := op B.right) B.hom)
    (boundedAboveFlatGlobalSectionSupported (X := op A.right) A.hom) _
    (fun K => boundedAboveFlatGlobalPairReindex_supported g K.obj K.property) _ _
    (boundedAboveFlatGlobalSectionUnit_reindex_of_eq g.right.op r s h)

/-- Every original pair square preserves its genuine pulled-back scalar. -/
theorem pairMap_preserves {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (r : (Γ(B.right, ⊤))ˣ) :
    Preserves (boundedAboveFlatGlobalSupportedPairModelMap g).hom.toFunctor
      (SupportedTensorEvaluation.unit (X := op B.right) B.hom r)
      (SupportedTensorEvaluation.unit (X := op A.right) A.hom
        (Units.map g.right.appTop.hom.toMonoidHom r)) :=
  pairMap_preserves_of_eq g r _ rfl

/-- The pre-existing supported parameter Laurent unit is exactly this global scalar lift. -/
theorem laurentUnit_eq {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) :
    ParameterLaurentTrack.supportedUnit f X =
      SupportedTensorEvaluation.unit
        (X := op (GlobalSupportedParameter.pair f
          (AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.laurent.op.obj X).unop).right)
        (GlobalSupportedParameter.pair f
          (AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex.laurent.op.obj X).unop).hom
        (ParameterLaurentUnit.projectedLaurentScalar Q X) := rfl

open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

/-- The actual supported Laurent projection track is the target identity action after the
unchanged coefficient Model map, at every original level and time. -/
theorem parameterTrack_level {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (n : ℕ) :
    ((ParameterLaurentTrack.supportedTrack f).homotopy X).level n =
      ((prespectrumIsoHomotopy (𝟙 ((ParameterModels.supported f).obj (laurent.op.obj X)))
        (SupportedTensorEvaluation.unit
          (X := op (GlobalSupportedParameter.pair f (laurent.op.obj X).unop).right)
          (GlobalSupportedParameter.pair f (laurent.op.obj X).unop).hom
          (ParameterLaurentUnit.projectedLaurentScalar Q X))).precomp
        (prespectrumMap ((ParameterModels.supported f).map (coefficient.app X)))).level n := by
  change (prespectrumIsoHomotopy ((ParameterModels.supported f).map (coefficient.app X))
    (onFunctor _ (ParameterLaurentTrack.supportedUnit f X))).level n = _
  rw [laurentUnit_eq]
  exact prespectrumIsoHomotopy_onFunctor_level _ _ n

end AlgebraicGeometry.Scheme.Modules.SupportedPairUnit
