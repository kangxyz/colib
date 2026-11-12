/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PrincipalSupportReindex
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.OpenImmersion
public import StacksFrontier.RingTheory.Length.RingEquiv
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField

/-! # Full original principal support cuts under genuine open restriction -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual open immersion of the reduced original point closures. -/
def integralComponentOpenMap (z : U) :
    (integralComponentAt z).subscheme ⟶ (integralComponentAt (j z)).subscheme :=
  Scheme.IdealSheafData.subschemeMap _ _ j (by
    rw [← comap_integralComponentAt_of_isOpenImmersion j z]
    exact (integralComponentAt (j z)).le_map_comap j)

/-- This map retains the original ambient open immersion and both inclusions. -/
@[reassoc (attr := simp)]
theorem integralComponentOpenMap_inclusion (z : U) :
    integralComponentOpenMap j z ≫ (integralComponentAt (j z)).subschemeι =
      (integralComponentAt z).subschemeι ≫ j :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

instance (z : U) : IsOpenImmersion (integralComponentOpenMap j z) := by
  unfold integralComponentOpenMap
  generalize_proofs H
  generalize hI : integralComponentAt z = I at H ⊢
  have h : (integralComponentAt (j z)).comap j = I := by
    rw [← hI, comap_integralComponentAt_of_isOpenImmersion]
  clear hI
  subst I
  rw [← Scheme.IdealSheafData.comapIso_hom_snd]
  infer_instance

/-- An actual open stalk isomorphism preserves the full literal section cut. -/
theorem sectionCut_length_open (x : U) (s : Γ(X, ⊤)) :
    Module.length (X.presheaf.stalk (j x))
      (X.presheaf.stalk (j x) ⧸ Ideal.span {X.presheaf.germ ⊤ (j x) (by trivial) s}) =
    Module.length (U.presheaf.stalk x)
      (U.presheaf.stalk x ⧸ Ideal.span {U.presheaf.germ ⊤ x (by trivial) (j.appTop s)}) := by
  let e := (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
  have H := Module.quotient_length_eq_of_ringEquiv e
    (Ideal.span {X.presheaf.germ ⊤ (j x) (by trivial) s})
  have he : e.toRingHom (X.presheaf.germ ⊤ (j x) (by trivial) s) =
      U.presheaf.germ ⊤ x (by trivial) (j.appTop s) := by
    exact Scheme.Hom.germ_stalkMap_apply j ⊤ x (by trivial) s
  rw [Ideal.map_span, Set.image_singleton, he] at H
  exact H

/-- The full support cut can be evaluated at any actual point above the ambient
point; closed-immersion injectivity identifies it with the canonical choice. -/
theorem principalSupportCutLength_eq_at_point (x z : X) (h : z ⤳ x)
    (e : (integralComponentAt z).subscheme)
    (he : (integralComponentAt z).subschemeι e = x) (s : Γ(X, ⊤)) :
    principalSupportCutLength X x z s =
      ((Module.length ((integralComponentAt z).subscheme.presheaf.stalk e)
        ((integralComponentAt z).subscheme.presheaf.stalk e ⧸
          Ideal.span {((integralComponentAt z).subscheme.presheaf.germ ⊤ e (by trivial)
            ((integralComponentAt z).subschemeι.appTop s))})).toNat : ℤ) := by
  have hp : integralComponentPointOfSpecializes X x z h = e := by
    apply (integralComponentAt z).subschemeι.isEmbedding.injective
    exact (integralComponentPointOfSpecializes_inclusion X x z h).trans he.symm
  subst e
  simp only [principalSupportCutLength, dite_eq_left h]

/-- Genuine open restriction preserves each full original support cut, including
nonreduced quotients and supports not passing through the chosen point. -/
theorem principalSupportCutLength_open (x z : U) (s : Γ(X, ⊤)) :
    principalSupportCutLength U x z (j.appTop s) =
      principalSupportCutLength X (j x) (j z) s := by
  classical
  by_cases h : z ⤳ x
  · let e := integralComponentPointOfSpecializes U x z h
    let m := integralComponentOpenMap j z
    have he : (integralComponentAt z).subschemeι e = x :=
      integralComponentPointOfSpecializes_inclusion U x z h
    have hm : (integralComponentAt (j z)).subschemeι (m e) = j x := by
      change ((m ≫ (integralComponentAt (j z)).subschemeι) e) = _
      rw [integralComponentOpenMap_inclusion]
      change j ((integralComponentAt z).subschemeι e) = _
      rw [he]
    rw [principalSupportCutLength_eq_at_point x z h e he,
      principalSupportCutLength_eq_at_point (j x) (j z)
        (h.map j.continuous) (m e) hm]
    have H := sectionCut_length_open m e ((integralComponentAt (j z)).subschemeι.appTop s)
    have hs : m.appTop ((integralComponentAt (j z)).subschemeι.appTop s) =
        (integralComponentAt z).subschemeι.appTop (j.appTop s) := by
      have hmap := congrArg (fun f => f.appTop s) (integralComponentOpenMap_inclusion j z)
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hmap
    rw [hs] at H
    exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) H.symm
  · have hj : ¬ j z ⤳ j x := fun hj =>
      h (j.isEmbedding.isInducing.specializes_iff.mp hj)
    simp only [principalSupportCutLength, dite_eq_right h, dite_eq_right hj]

variable [IsIntegral U] [IsIntegral X] [IsLocallyNoetherian U] [IsLocallyNoetherian X]
    [IsDominant j]

/-- Genuine open restriction bijects the original nonzero principal supports
through the chosen point. Openness supplies every specializing original support. -/
theorem bijOn_open_principalSupportThrough (x : U) (F : X.functionField) :
    Set.BijOn j (principalSupportThrough U x (functionFieldEquiv_openImmersion j F))
      (principalSupportThrough X (j x) F) := by
  refine ⟨?_, j.isEmbedding.injective.injOn, ?_⟩
  · intro z hz
    refine ⟨?_, hz.2.map j.continuous⟩
    change (principalCycle X F) (j z) ≠ 0
    rw [← principalCycle_functionFieldEquiv_openImmersion_apply j F z]
    exact hz.1
  · intro y hy
    obtain ⟨z, hz⟩ := hy.2.mem_open j.isOpenEmbedding.isOpen_range ⟨x, rfl⟩
    subst y
    refine ⟨z, ⟨?_, j.isEmbedding.isInducing.specializes_iff.mp hy.2⟩, rfl⟩
    change (principalCycle U (functionFieldEquiv_openImmersion j F)) z ≠ 0
    rw [principalCycle_functionFieldEquiv_openImmersion_apply]
    exact hy.1

/-- The full signed original principal support-cut sum is unchanged by the actual
open chart. This is a literal coefficient sum, before rational equivalence. -/
theorem principalSupportCuts_open (x : U) (F : X.functionField) (s : Γ(X, ⊤)) :
    (∑ᶠ z ∈ principalSupportThrough U x (functionFieldEquiv_openImmersion j F),
      (principalCycle U (functionFieldEquiv_openImmersion j F)) z *
        principalSupportCutLength U x z (j.appTop s)) =
    ∑ᶠ z ∈ principalSupportThrough X (j x) F,
      (principalCycle X F) z * principalSupportCutLength X (j x) z s := by
  apply finsum_mem_eq_of_bijOn j (bijOn_open_principalSupportThrough j x F)
  intro z _
  rw [principalCycle_functionFieldEquiv_openImmersion_apply, principalSupportCutLength_open]

omit [IsLocallyNoetherian U] [IsLocallyNoetherian X] in
/-- The native open function-field equivalence is the original scheme morphism's
function-field map, with the same generic stalk transport. -/
theorem functionFieldEquiv_openImmersion_eq_schemeFunctionFieldMap (F : X.functionField) :
    functionFieldEquiv_openImmersion j F = j.functionFieldMap F := by
  rw [functionFieldEquiv_openImmersion_eq_dominantFunctionFieldMap]
  have h (x : U) {y : X} (he : j x = y) (hs : j x ⤳ y) :
      (he ▸ j.stalkMap x).hom =
        (X.presheaf.stalkSpecializes hs ≫ j.stalkMap x).hom := by
    cases he
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    simp
  exact congrArg (fun φ : X.functionField →+* U.functionField => φ F)
    (h (genericPoint U) (genericPoint_eq_of_isDominant j)
      (specializes_genericPoint_of_isDominant j))

end Stacks.Chow
