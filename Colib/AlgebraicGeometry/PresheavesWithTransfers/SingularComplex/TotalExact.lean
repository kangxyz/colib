/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Total
import Colib.Algebra.Homology.CochainComplex.TotalExact
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TermExactness
import Colib.CategoryTheory.Preadditive.AdditiveFunctorAB5
import Mathlib.Algebra.Category.Grp.AB

/-!
# Short exact sequences of singular total complexes

The fixed singular degree is exact. Exact coproducts along each native
antidiagonal give the short exact sequence on total complexes.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "c" => ComplexShape.up ℤ

set_option maxHeartbeats 380000 in
-- The occupied cochain degree is compared through the actual extension isomorphisms.
private theorem singularCochainTerm_shortExact
    (S : ShortComplex (PresheafWithTransfers.{v} k)) (hS : S.ShortExact) (q : ℤ) :
    (S.map (singularCochainFunctor 0 ⋙
      HomologicalComplex.eval (PresheafWithTransfers.{v} k) c q)).ShortExact := by
  let F : PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k :=
    singularCochainFunctor 0 ⋙ HomologicalComplex.eval (PresheafWithTransfers.{v} k) c q
  by_cases hq : q ≤ 0
  · let r := (-q).toNat
    let e := ComplexShape.embeddingUpIntLE 0
    have h : e.f r = q := by
      rw [ComplexShape.embeddingUpIntLE_f]
      dsimp [r]
      omega
    let G : PresheafWithTransfers.{v} k ⥤ PresheafWithTransfers.{v} k := singularTermFunctor r
    let η (P : PresheafWithTransfers.{v} k) : F.obj P ≅ G.obj P :=
      (singularComplex P).extendXIso e h
    have hn {P Q : PresheafWithTransfers.{v} k} (f : P ⟶ Q) :
        F.map f ≫ (η Q).hom = (η P).hom ≫ G.map f := by
      let d := singularComplexMap f
      change (HomologicalComplex.extendMap d e).f q ≫
          (HomologicalComplex.extendXIso (singularComplex Q) e h).hom =
        (HomologicalComplex.extendXIso (singularComplex P) e h).hom ≫ d.f r
      rw [HomologicalComplex.extendMap_f d e h, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    let e₁ := η S.X₁
    let e₂ := η S.X₂
    let e₃ := η S.X₃
    let iso : S.map F ≅ S.map G :=
      ShortComplex.isoMk e₁ e₂ e₃ (hn S.f).symm (hn S.g).symm
    exact ShortComplex.shortExact_of_iso iso.symm (hS.map_of_exact G)
  · have hz (P : PresheafWithTransfers.{v} k) : IsZero (F.obj P) :=
      isZero_singularCochainComplex_X P 0 q (by omega)
    exact ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_isZero_X₂ _ (hz S.X₂))
      ((hz S.X₁).mono _) ((hz S.X₃).epi _)

local instance : (singularBicomplexFunctor k :
    CochainComplex (PresheafWithTransfers.{v} k) ℤ ⥤
      HomologicalComplex₂ (PresheafWithTransfers.{v} k) c c).Additive := by
  unfold singularBicomplexFunctor
  infer_instance

/-- The original singular total functor preserves short exact sequences. -/
theorem singularTotalFunctor_shortExact (S : ShortComplex (CochainComplex
    (PresheafWithTransfers.{v} k) ℤ)) (hS : S.ShortExact) :
    (S.map (singularTotalFunctor k)).ShortExact := by
  let B := S.map (singularBicomplexFunctor k)
  let hcolim (n : ℤ) :
      HasColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n})) (PresheafWithTransfers.{v} k) :=
    hasColimitsOfShape_of_closedUnderColimits _
      (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v})
  let : ∀ n : ℤ,
      HasColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n}))
        (PresheafWithTransfers.{v} k) := hcolim
  let : ∀ n : ℤ,
      HasExactColimitsOfShape (Discrete ↥(ComplexShape.π c c c ⁻¹' {n}))
        (PresheafWithTransfers.{v} k) := fun _ => AdditiveFunctor.hasExactColimitsOfShape _
  apply HomologicalComplex₂.shortExact_total_of_bidegreewise B
  intro p q
  let E := HomologicalComplex.eval (PresheafWithTransfers.{v} k) c p
  exact singularCochainTerm_shortExact (S.map E) (hS.map_of_exact E) q

end AlgebraicGeometry.PresheafWithTransfers
