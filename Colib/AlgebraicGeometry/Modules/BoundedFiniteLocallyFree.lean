/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.VectorBundle.Exact
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Actual bounded complexes of finite locally free scheme modules

The object property is the native `boundedFiniteLocallyFreeComplex`: global bounds on terms,
with finite local freeness in each degree. Its full subcategory retains actual chain maps.
This is the strict-perfect predicate used in the original Quillen development. It is not the
stronger `StrictlyPerfect.IsStrictlyPerfect`, whose terms are global finite-free retracts.

The extension theorem uses native local splitting of vector bundles on an arbitrary scheme.
No global projectivity, affine hypothesis or cohomological boundedness replacement is used.

Implementation provenance: `Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Strict.lean` at
`2c34f185fa859e862661f939cd216b07bcccfb26`, used by
`Quillen/AlgebraicGeometry/PerfectComplexes/Strict.lean` at `c561118b`.
The existing native Stacks predicate replaces the earlier property, without a compatibility
alias or a second complex model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry
open scoped ZeroObject

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

variable {X : Scheme.{u}}

/-- Native boundedness gives exactly global lower and upper bounds on terms. -/
theorem boundedFiniteLocallyFreeComplex_iff_termBounds (K : CochainComplex X.Modules ℤ) :
    boundedFiniteLocallyFreeComplex X K ↔
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
        ∀ n : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u} (K.X n) := by
  constructor
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hK⟩
    refine ⟨⟨a, b, fun n hn => ?_⟩, hK⟩
    exact hn.elim (fun h => K.isZero_of_isStrictlyGE a n h)
      (fun h => K.isZero_of_isStrictlyLE b n h)
  · rintro ⟨⟨a, b, hK⟩, hflf⟩
    exact ⟨⟨⟨a, (K.isStrictlyGE_iff a).2 fun n hn => hK n (Or.inl hn)⟩,
      ⟨b, (K.isStrictlyLE_iff b).2 fun n hn => hK n (Or.inr hn)⟩⟩, hflf⟩

/-- Every actual zero complex is bounded with finite locally free terms. -/
theorem boundedFiniteLocallyFreeComplex_of_isZero {K : CochainComplex X.Modules ℤ}
    (hK : IsZero K) : boundedFiniteLocallyFreeComplex X K := by
  have h (n : ℤ) : IsZero (K.X n) :=
    (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero hK
  exact (boundedFiniteLocallyFreeComplex_iff_termBounds K).2
    ⟨⟨0, 0, fun n _ => h n⟩, fun n => finiteLocallyFree_of_isZero X _ (h n)⟩

instance boundedFiniteLocallyFreeComplex_containsZero :
    (boundedFiniteLocallyFreeComplex X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, boundedFiniteLocallyFreeComplex_of_isZero (isZero_zero _)⟩

/-- Actual chain isomorphisms preserve the native bounded finite locally free property. -/
theorem boundedFiniteLocallyFreeComplex_of_iso {K L : CochainComplex X.Modules ℤ}
    (e : K ≅ L) (hK : boundedFiniteLocallyFreeComplex X K) :
    boundedFiniteLocallyFreeComplex X L := by
  obtain ⟨⟨a, b, hK⟩, hflf⟩ := (boundedFiniteLocallyFreeComplex_iff_termBounds K).1 hK
  let en (n : ℤ) := (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).mapIso e
  apply (boundedFiniteLocallyFreeComplex_iff_termBounds L).2
  refine ⟨⟨a, b, fun n hn => (hK n hn).of_iso (en n).symm⟩, fun n => ?_⟩
  exact SheafOfModules.IsFiniteLocallyFree.of_iso (h := hflf n) (en n)

instance boundedFiniteLocallyFreeComplex_closedUnderIsomorphisms :
    (boundedFiniteLocallyFreeComplex X).IsClosedUnderIsomorphisms where
  of_iso := boundedFiniteLocallyFreeComplex_of_iso

/-- A short exact extension of bounded finite locally free complexes has the same property. -/
@[colib_tag "COL-0313", stacks 01C6 "Definition of the termwise finite locally free input",
  colib_ref "aglib" "Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Strict.lean:79-100"
    "adaptation" "The original global term bounds and local extension closure on every scheme"]
theorem boundedFiniteLocallyFreeComplex_of_shortExact
    {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : boundedFiniteLocallyFreeComplex X S.X₁)
    (h₃ : boundedFiniteLocallyFreeComplex X S.X₃) :
    boundedFiniteLocallyFreeComplex X S.X₂ := by
  obtain ⟨⟨a, b, hb₁⟩, hv₁⟩ := (boundedFiniteLocallyFreeComplex_iff_termBounds S.X₁).1 h₁
  obtain ⟨⟨c, d, hb₃⟩, hv₃⟩ := (boundedFiniteLocallyFreeComplex_iff_termBounds S.X₃).1 h₃
  have hs (n : ℤ) := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
  apply (boundedFiniteLocallyFreeComplex_iff_termBounds S.X₂).2
  constructor
  · refine ⟨min a c, max b d, fun n hn => ?_⟩
    have h₁ : IsZero (S.X₁.X n) := hb₁ n (hn.elim
      (fun h => Or.inl (lt_of_lt_of_le h (min_le_left _ _)))
      (fun h => Or.inr (lt_of_le_of_lt (le_max_left _ _) h)))
    have h₃ : IsZero (S.X₃.X n) := hb₃ n (hn.elim
      (fun h => Or.inl (lt_of_lt_of_le h (min_le_right _ _)))
      (fun h => Or.inr (lt_of_le_of_lt (le_max_right _ _) h)))
    exact (hs n).exact.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  · intro n
    exact Stacks.FiniteLocallyFree.isFiniteLocallyFree_of_shortExact _ (hs n) (hv₁ n) (hv₃ n)

instance boundedFiniteLocallyFreeComplex_extensionClosed :
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed
      (boundedFiniteLocallyFreeComplex X) where
  prop_middle := boundedFiniteLocallyFreeComplex_of_shortExact

instance boundedFiniteLocallyFreeComplex_closedUnderFiniteProducts :
    (boundedFiniteLocallyFreeComplex X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts _

/-- Every integer shift retains global term bounds and finite local freeness. -/
theorem boundedFiniteLocallyFreeComplex_shift {K : CochainComplex X.Modules ℤ}
    (hK : boundedFiniteLocallyFreeComplex X K) (n : ℤ) :
    boundedFiniteLocallyFreeComplex X (K⟦n⟧) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hflf⟩ := hK
  exact ⟨⟨⟨a - n, K.isStrictlyGE_shift a n (a - n) (by omega)⟩,
    ⟨b - n, K.isStrictlyLE_shift b n (b - n) (by omega)⟩⟩, fun i => hflf (i + n)⟩

/-- A vector bundle placed in any single degree is bounded finite locally free. -/
theorem boundedFiniteLocallyFreeComplex_single_obj (M : X.Modules) (n : ℤ)
    (hM : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    boundedFiniteLocallyFreeComplex X
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) n).obj M) := by
  refine ⟨⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩, fun i => ?_⟩
  by_cases hi : i = n
  · subst i
    simpa only [HomologicalComplex.single_obj_X_self] using hM
  · exact finiteLocallyFree_of_isZero X _
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/-- The degree-zero vector-bundle inclusion keeps the native module and chain models. -/
def vectorBundleComplexInclusion (X : Scheme.{u}) :
    X.Vect ⥤ (boundedFiniteLocallyFreeComplex X).FullSubcategory :=
  (boundedFiniteLocallyFreeComplex X).lift
    (ObjectProperty.ι (fun M : X.Modules => SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) ⋙
      HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0)
    (fun M => boundedFiniteLocallyFreeComplex_single_obj M.obj 0 M.property)

end Stacks.Perfect.BoundedLocallyFreeComplexes
