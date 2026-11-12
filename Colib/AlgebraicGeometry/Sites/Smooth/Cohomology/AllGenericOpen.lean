/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Cohomology.LocalTriviality
public import Colib.AlgebraicGeometry.Sites.Smooth.Sections.GenericOpenLift
public import Colib.AlgebraicGeometry.Sites.Smooth.Injectives

/-! # Positive ordinary classes vanish on an open containing every generic point -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/Sheaf/AllGenericOpen.lean`, blob `c066afb03bd2dbea0f81adf12409192d4ac21b1c`.
The actual ordinary free-Yoneda Ext groups, signed boundary and original
restriction arrows are retained. No positive-cohomology sheaf gluing or
whole-cylinder generic-base vanishing is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w u
namespace AlgebraicGeometry.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Every positive ordinary class vanishes on an actual open containing all generic points.
No separatedness of the higher-cohomology presheaf is used. -/
theorem exists_all_generic_open_restriction_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite (Spec (.of k)))
    (e : (cohomologyPresheaf.{w, u + 1} F (n + 1)).obj (op X)) :
    ∃ O : X.left.Opens, genericPoints X.left ⊆ (O : Set X.left) ∧
      (cohomologyPresheaf.{w, u + 1}
        F (n + 1)).map (SmoothSite.openInclusion X O).op e = 0 := by
  let J := SmoothSite.nisnevichTopology (Spec (.of k))
  induction n generalizing F with
  | zero =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (((freeYoneda.{u + 1} J).obj X)) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨O, hO, l, hl⟩ := SmoothSite.exists_all_generic_open_section_lift E.g X
      (extSectionsAddEquiv.{w, u + 1} X E.X₃ y)
    refine ⟨O, hO, ?_⟩
    rw [← hy]
    exact boundary_restriction_eq_zero_of_imageSieve.{w, u + 1, u, u + 1} J hE y
      (SmoothSite.openInclusion X O) ⟨l, hl⟩
  | succ n ih =>
    let E := injectivePresentation.{u + 1, u, u + 1} J F
    let : Injective E.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hE := injectivePresentation_shortExact.{u + 1, u, u + 1} J F
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (((freeYoneda.{u + 1} J).obj X)) hE e (Ext.eq_zero_of_injective _) rfl
    obtain ⟨O, hO, hz⟩ := ih E.X₃ y
    let p := SmoothSite.openInclusion X O
    let Y := (SmoothSite.opensFunctor X).obj O
    refine ⟨O, hO, ?_⟩
    rw [← hy]
    change (Ext.mk₀ ((freeYoneda.{u + 1} J).map p)).comp
      (y.comp hE.extClass rfl) (zero_add (n + 1 + 1)) = 0
    rw [← Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl (by omega)]
    change ((cohomologyPresheaf.{w, u + 1} E.X₃ (n + 1)).map p.op y).comp hE.extClass rfl = 0
    rw [hz]
    exact Ext.zero_comp (((freeYoneda.{u + 1} J).obj Y)) (n + 1) hE.extClass _ rfl

end AlgebraicGeometry.SheafCohomology
