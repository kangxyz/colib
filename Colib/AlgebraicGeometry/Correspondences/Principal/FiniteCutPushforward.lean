/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# Finite pushforward of literal principal cuts

The native finite-fibre norm formula gives a coefficient identity before passage
to rational equivalence. Every point over the target is retained with its actual
residue degree. The finite map need not be flat. The generic factor is the
original residue degree at the generic point,
identified with the actual function-field degree. The correspondence-image
identification
is not part of this result.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- The finite norm identity for a pulled-back function, retaining every fibre
point and its residue degree, with no flatness assumption on the finite map. -/
theorem finsum_ord_pullback_mul_residueDegree (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    (F : Y.functionField) (hF : F ≠ 0) (y : Y) (hy : Order.coheight y = 1)
    (hfiber : ∀ x : X, g.base x = y → Order.coheight x = 1) :
    (∑ᶠ x ∈ g.base ⁻¹' {y},
      X.ord (dominantFunctionFieldMap g F) x * (g.residueDegree x : ℤ)) =
        (g.residueDegree (genericPoint X) : ℤ) * Y.ord F y := by
  let := (dominantFunctionFieldMap g).toAlgebra
  have hmap : dominantFunctionFieldMap g F ≠ 0 :=
    fun hz => hF ((dominantFunctionFieldMap g).injective (by simpa using hz))
  rw [finsum_ord_mul_residueDegree_of_isFinite g rfl _ hmap y hy hfiber]
  change Y.ord (Algebra.norm Y.functionField
    (algebraMap Y.functionField X.functionField F)) y = _
  rw [Algebra.norm_algebraMap, Y.ord_pow hF,
    finrank_functionField_eq_residueDegree g]

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
/-- The same native function-field map reads an actual pulled-back global section. -/
theorem dominantFunctionFieldMap_globalSection (g : X ⟶ Y) [IsDominant g]
    (s : Γ(Y, ⊤)) :
    dominantFunctionFieldMap g (Y.germToFunctionField ⊤ s) =
      X.germToFunctionField ⊤ (g.appTop s) := by
  have htop : g.appLE ⊤ ⊤ (by simp) = g.appTop := by
    unfold Scheme.Hom.appLE
    change g.appTop ≫ X.presheaf.map (𝟙 _) = g.appTop
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [htop] using dominantFunctionFieldMap_germToFunctionField_of_mem
    g (genericPoint X) ⊤ (by trivial) ⊤ (by trivial) (by simp) s

/-- A nonzero section has the full principal quotient length as its order.
The quotient is not replaced by its reduced support. -/
theorem ord_globalSection_eq_length (s : Γ(X, ⊤)) (hs : s ≠ 0)
    (x : X) (hx : Order.coheight x = 1) :
    X.ord (X.germToFunctionField ⊤ s) x =
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span {X.presheaf.germ ⊤ x (by trivial) s})).toNat : ℤ) := by
  have hsx : X.presheaf.germ ⊤ x (by trivial) s ≠ 0 :=
    fun hz => hs ((germ_injective_of_isIntegral X x (by trivial)) (by simpa using hz))
  have H := ord_div_algebraMap_eq_length_sub hx hsx (one_ne_zero
    (α := X.presheaf.stalk x))
  erw [X.algebraMap_germ_eq_germToFunctionField (by trivial) s] at H
  simpa using H

/-- The actual full principal cuts satisfy the finite projection formula.
Every source point over `y` contributes its original residue degree; coincident
images are summed, rather than chosen or discarded. -/
@[colib_tag "COL-1062", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/PrincipalDivisorPushforward.lean:106-114"
  "ingredient" "Finite pushforward of original orders with full residue degrees; the cut- \
    length specialization is proved here."]
theorem finsum_principalCutLength_mul_residueDegree (g : X ⟶ Y)
    [IsFinite g] [IsDominant g] (s : Γ(Y, ⊤)) (hs : s ≠ 0)
    (y : Y) (hy : Order.coheight y = 1)
    (hfiber : ∀ x : X, g.base x = y → Order.coheight x = 1) :
    (∑ᶠ x ∈ g.base ⁻¹' {y},
      ((Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ Ideal.span
          {X.presheaf.germ ⊤ x (by trivial) (g.appTop s)})).toNat : ℤ) *
            (g.residueDegree x : ℤ)) =
      (g.residueDegree (genericPoint X) : ℤ) *
        ((Module.length (Y.presheaf.stalk y)
          (Y.presheaf.stalk y ⧸ Ideal.span
            {Y.presheaf.germ ⊤ y (by trivial) s})).toNat : ℤ) := by
  let := (dominantFunctionFieldMap g).toAlgebra
  have hF : Y.germToFunctionField ⊤ s ≠ 0 :=
    fun hz => hs (Y.germToFunctionField_injective ⊤ (by simpa using hz))
  have happ : g.appTop s ≠ 0 := by
    intro hz
    have H := dominantFunctionFieldMap_globalSection g s
    rw [hz, map_zero] at H
    exact hF ((dominantFunctionFieldMap g).injective (by simpa using H))
  have H := finsum_ord_pullback_mul_residueDegree g _ hF y hy hfiber
  rw [dominantFunctionFieldMap_globalSection, ord_globalSection_eq_length s hs y hy] at H
  rw [← H]
  apply finsum_congr
  intro x
  apply finsum_congr
  intro hx
  rw [ord_globalSection_eq_length _ happ x (hfiber x hx)]

end Stacks.Chow
