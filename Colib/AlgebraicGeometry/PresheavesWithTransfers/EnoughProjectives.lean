/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.YonedaLarge
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Projective presentations by transfer representables

Additive Yoneda makes the large representables projective. The sum indexed by
all sections of a presheaf gives an objectwise surjective evaluation map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The actual signed correspondence representable is projective. -/
instance representableLarge_projective (X : Cor k) : Projective ((representableLarge k).obj X) where
  factors {E A} f e _ := by
    have he : Epi ((AdditiveFunctor.forget (Cor k)ᵒᵖ AddCommGrpCat.{u + 1}).map e) :=
      Functor.map_epi _ _
    have hX : Epi (e.hom.app (op X)) := (NatTrans.epi_iff_epi_app _).1 he (op X)
    obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective (e.hom.app (op X))).1 hX
      (yonedaLargeAddEquiv A X f)
    let g := (yonedaLargeAddEquiv E X).symm s
    refine ⟨g, (yonedaLargeAddEquiv A X).injective ?_⟩
    change e.hom.app (op X) (yonedaLargeAddEquiv E X g) = _
    rw [show yonedaLargeAddEquiv E X g = s from
      (yonedaLargeAddEquiv E X).apply_symm_apply s]
    exact hs

/-- The sections indexing the canonical coproduct cover by transfer representables. -/
abbrev representableCoverIndex (P : PresheafWithTransfers.{u + 1} k) :=
  Σ X : Cor k, sections P X

/-- The actual transfer representable at each section of a presheaf. -/
def representableCoverFamily (P : PresheafWithTransfers.{u + 1} k)
    (i : representableCoverIndex P) : PresheafWithTransfers.{u + 1} k :=
  (representableLarge k).obj i.1

instance (P : PresheafWithTransfers.{u + 1} k) (i : representableCoverIndex P) :
    Projective (representableCoverFamily P i) := by
  change Projective ((representableLarge k).obj i.1)
  infer_instance

instance (P : PresheafWithTransfers.{u + 1} k) : HasCoproduct (representableCoverFamily P) := by
  let I := representableCoverIndex P
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfShape
  exact (hasColimitsOfShape_of_closedUnderColimits (Discrete I)
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})).has_colimit _

/-- The canonical coproduct of the actual representables indexed by all sections. -/
abbrev representableCover (P : PresheafWithTransfers.{u + 1} k) :=
  ∐ (representableCoverFamily P)

/-- Evaluation of the chosen section on each summand of the canonical cover. -/
def representableCoverπ (P : PresheafWithTransfers.{u + 1} k) : representableCover P ⟶ P :=
  Sigma.desc (fun i => sectionHomLarge P i.1 i.2)

instance representableCoverπ_epi (P : PresheafWithTransfers.{u + 1} k) :
    Epi (representableCoverπ P) := by
  let I := representableCoverIndex P
  let R := representableCoverFamily P
  let e (i : I) : R i ⟶ P := sectionHomLarge P i.1 i.2
  let f := representableCoverπ P
  have hf (X : Cor k) : Function.Surjective (f.hom.app (op X)) := by
    intro s
    let i : I := ⟨X, s⟩
    refine ⟨(Sigma.ι R i).hom.app (op X) (ULift.up (𝟙 X)), ?_⟩
    have hi : Sigma.ι R i ≫ f = e i := Sigma.ι_comp_desc e i
    have h := congrArg (fun g : R i ⟶ P => g.hom.app (op X) (ULift.up (𝟙 X))) hi
    exact h.trans ((yonedaLargeAddEquiv P X).apply_symm_apply s)
  let U : PresheafWithTransfers.{u + 1} k ⥤ (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} := forget
  have hUf : Epi (U.map f) := (NatTrans.epi_iff_epi_app _).2
    (fun X => (AddCommGrpCat.epi_iff_surjective _).2 (hf X.unop))
  exact U.epi_of_epi_map hUf

/-- Relations from the canonical cover of the actual kernel of the evaluation map. -/
def representablePresentationRelation (P : PresheafWithTransfers.{u + 1} k) :
    representableCover (kernel (representableCoverπ P)) ⟶ representableCover P :=
  representableCoverπ (kernel (representableCoverπ P)) ≫ kernel.ι (representableCoverπ P)

/-- The canonical two-step presentation has the original presheaf as its cokernel. -/
def representablePresentationIsColimit (P : PresheafWithTransfers.{u + 1} k) :
    IsColimit (CokernelCofork.ofπ (representableCoverπ P)
      (show representablePresentationRelation P ≫ representableCoverπ P = 0 by
        simp [representablePresentationRelation, Category.assoc])) :=
  isCokernelEpiComp
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (representableCoverπ P)))
    (representableCoverπ (kernel (representableCoverπ P))) rfl

/-- Every transfer presheaf is an epimorphic image of a sum of actual representables. -/
instance enoughProjectives : EnoughProjectives (PresheafWithTransfers.{u + 1} k) where
  presentation P := ⟨⟨representableCover P, representableCoverπ P⟩⟩

end AlgebraicGeometry.PresheafWithTransfers
