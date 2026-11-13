/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.SplittingSequence
public import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian

import Colib.AlgebraicGeometry.Sites.Nisnevich.FieldLifting
import Colib.AlgebraicGeometry.Sites.Nisnevich.SplittingStratum
import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen

/-!
# Finite splitting sequences on the smooth Nisnevich site

Noetherian induction successively enlarges the open over which a splitting
sequence has been constructed. The extra stratum is the actual restriction
of the reduced closed complement of the old open. A section of the original
covering morphism on that stratum extends the sequence by one step.

See [Voevodsky, Lemma 2.15](https://arxiv.org/pdf/0805.4576#page=10).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
private theorem range_restrict_closedComplement {X Z : Scheme.{u}}
    (z : Z ⟶ X) (C D : Closeds X) (h : Set.range z = C) (hDC : D ≤ C) :
    Set.range (z ∣_ D.compl) = (Set.range (X.homOfLE (show C.compl ≤ D.compl from
      fun _ hx hDx ↦ hx (hDC hDx))))ᶜ := by
  let U : X.Opens := D.compl
  have hrange : Set.range (z ∣_ U) = U.ι ⁻¹' Set.range z := by
    let pb := isPullback_morphismRestrict z U
    let e := pb.isoPullback
    have he : (fun x ↦ (z ∣_ U) (e.inv x)) = ⇑(pullback.fst U.ι z) := by
      funext x
      exact congrArg (fun f ↦ f x) pb.isoPullback_inv_fst
    rw [← Scheme.Pullback.range_fst U.ι z, ← he]
    change Set.range (z ∣_ U) = Set.range ((z ∣_ U) ∘ e.inv)
    have hsurj : Function.Surjective (⇑e.inv) := e.inv.homeomorph.surjective
    rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  rw [hrange, h]
  rw [show Set.range (X.homOfLE (show C.compl ≤ D.compl from
      fun _ hx hDx ↦ hx (hDC hDx))) = U.ι ⁻¹' (C.compl : Set X) from by
    exact congrArg (fun A : U.toScheme.Opens ↦ (A : Set U.toScheme))
      (Scheme.opensRange_homOfLE _)]
  change U.ι ⁻¹' (C : Set X) = (U.ι ⁻¹' (C : Set X)ᶜ)ᶜ
  rw [← Set.preimage_compl, compl_compl]

set_option backward.isDefEq.respectTransparency false in
/-- An actual smooth Nisnevich covering morphism admits a finite splitting sequence. -/
theorem nisnevichSplittingSequence_of_singleton_mem_precoverage [IsNoetherian S]
    {X Y : SmoothSite S}
    (q : Y ⟶ X) (hq : Presieve.singleton q.left ∈ Nisnevich.precoverage X.left) :
    NisnevichSplittingSequence q (𝟙 X) := by
  have hqEtale : Etale q.left :=
    (Nisnevich.mem_precoverage_iff.mp hq).1 _ (Presieve.singleton_self _)
  let : Etale q.left := hqEtale
  have hlift (K : Type u) [Field K] (x : Spec (.of K) ⟶ X.left) :
      ∃ y : Spec (.of K) ⟶ Y.left, y ≫ q.left = x := by
    obtain ⟨Z, p, hp, y, hy⟩ := Nisnevich.exists_lift_of_mem_precoverage hq K x
    cases hp
    exact ⟨y, hy⟩
  suffices h : ∀ C : Closeds X.left,
      NisnevichSplittingSequence q (openInclusion X C.compl) →
        NisnevichSplittingSequence q (𝟙 X) by
    refine h ⊤ (.empty _ ⟨fun x ↦ ?_⟩)
    exact x.property (Set.mem_univ _)
  intro C
  apply (wellFounded_lt (α := Closeds X.left)).induction C
  intro C ih hC
  let I := Scheme.IdealSheafData.vanishingIdeal C
  let z := I.subschemeι
  have hz : Set.range z = (C : Set X.left) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal C
  by_cases h : C = ⊥
  · let U : X.left.Opens := C.compl
    let i := openInclusion X U
    have hz' : Set.range z = (∅ : Set X.left) := by rw [hz, h]; rfl
    let : IsEmpty I.subscheme := ⟨fun t ↦ by
      have ht : z t ∈ Set.range z := ⟨t, rfl⟩
      rw [hz'] at ht
      exact ht⟩
    have hcomp : Set.range z = (Set.range i.left)ᶜ := by
      change Set.range z = (Set.range U.ι)ᶜ
      rw [Scheme.Opens.range_ι, hz]
      exact (compl_compl (C : Set X.left)).symm
    have hCi : NisnevichSplittingSequence q (i ≫ 𝟙 X) := by
      simpa only [Category.comp_id] using hC
    let initial := AlgebraicGeometry.isInitialOfIsEmpty (X := I.subscheme)
    exact .step (𝟙 X) i (inferInstanceAs (IsOpenImmersion U.ι)) hCi z
      inferInstance hcomp (initial.to Y.left) (initial.hom_ext _ _)
  · obtain ⟨D, hDC, s, hs⟩ := Nisnevich.exists_splittingStratum q.left hlift C h
    let hle : C.compl ≤ D.compl := fun _ hx hDx ↦ hx (hDC.le hDx)
    let i := (opensFunctor X).map (homOfLE hle)
    let p := openInclusion X D.compl
    have hip : i ≫ p = openInclusion X C.compl := by
      apply MorphismProperty.Over.Hom.ext
      exact Scheme.homOfLE_ι X.left hle
    have hi : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (X.left.homOfLE hle))
    have hCi : NisnevichSplittingSequence q (i ≫ p) := by rwa [hip]
    let z' := z ∣_ D.compl
    have hz' : IsClosedImmersion z' :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict z D.compl).flip inferInstance
    have hcomp : Set.range z' = (Set.range i.left)ᶜ :=
      range_restrict_closedComplement z C D hz hDC.le
    have hs' : s ≫ q.left = z' ≫ p.left := hs.trans (morphismRestrict_ι z D.compl).symm
    exact ih D hDC (.step p i hi hCi z' hz' hcomp s hs')

end AlgebraicGeometry.Scheme.SmoothSite
