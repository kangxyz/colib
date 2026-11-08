/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Subcategory

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.OppositeQuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Actual opposite properties of cochain complexes

Degree reversal and the opposite-cochain equivalence transport an original
replete, extension-closed property to actual complexes in the opposite abelian
category. The explicit shift isomorphism reverses the integer shift. Together
with the original degreewise split cone sequence, it proves genuine cone
closure from the original negative-shift closure.

Object and morphism universes remain independent. No new resolution or derived
equivalence is a hypothesis.
-/
/-! Implementation provenance:
`Quillen/Aglib/Algebra/Homology/CochainComplex/OppositeSubcategory.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual complexes, maps and independent universes are retained. -/

@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

instance cochainOpEquivalence_functor_additive : (CochainComplex.opEquivalence C).functor.Additive
  := by
  dsimp [CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence]
  infer_instance
instance cochainOpEquivalence_inverse_additive : (CochainComplex.opEquivalence C).inverse.Additive
  :=
  Equivalence.inverse_additive _

/-- Transport an object property of cochain complexes to complexes in the opposite category by
the inverse opposite-cochain equivalence, after taking the opposite property. -/
abbrev oppositeProperty (P : ObjectProperty (CochainComplex C ℤ)) :
    ObjectProperty (CochainComplex Cᵒᵖ ℤ) :=
  P.op.inverseImage (CochainComplex.opEquivalence C).inverse

variable (P : ObjectProperty (CochainComplex C ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]

instance oppositeProperty_extensionClosed :
    (abelianExactStructure (CochainComplex Cᵒᵖ ℤ)).IsExtensionClosed (oppositeProperty P) where
  prop_middle {S} hS h₁ h₃ := by
    have := hS.mono_f
    have := hS.epi_g
    have h : (S.map (CochainComplex.opEquivalence C).inverse).unop.ShortExact :=
      (hS.map (CochainComplex.opEquivalence C).inverse).unop
    exact CategoryTheory.ExactCategory.ExactStructure.IsExtensionClosed.prop_middle (E :=
      abelianExactStructure (CochainComplex C
      ℤ)) (P := P) h h₃ h₁

instance oppositeProperty_finiteProducts : (oppositeProperty P).IsClosedUnderFiniteProducts :=
  (abelianExactStructure _).extensionClosed_finiteProducts _

/-- Actual reversal of degrees interchanges the original opposite shift with
the negative shift, retaining the same terms up to their index equality. -/
def unopShiftIso (K : CochainComplex Cᵒᵖ ℤ) (n : ℤ) :
    ((CochainComplex.opEquivalence C).inverse.obj (K⟦n⟧)).unop ≅
      ((CochainComplex.opEquivalence C).inverse.obj K).unop⟦-n⟧ := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (K.XIsoOfEq (show -(i + -n) = -i + n by omega)).unop) ?_
  intro i j hij
  dsimp [CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence]
  simp only [Int.negOnePow_neg, Units.smul_def, unop_zsmul,
    HomologicalComplex.XIsoOfEq, eqToIso]
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  apply Quiver.Hom.op_inj
  simp only [op_comp]
  change K.d (-(j + -n)) (-(i + -n)) ≫
      (K.XIsoOfEq (show -(i + -n) = -i + n by omega)).hom =
    (K.XIsoOfEq (show -(j + -n) = -j + n by omega)).hom ≫ K.d (-j + n) (-i + n)
  simp

omit [P.ContainsZero] [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P] in
lemma oppositeProperty_shift
    (hshift : ∀ K, P K → P (K⟦(-1 : ℤ)⟧)) (K : CochainComplex Cᵒᵖ ℤ)
    (hK : oppositeProperty P K) : oppositeProperty P (K⟦(1 : ℤ)⟧) :=
  P.prop_of_iso (unopShiftIso K 1).symm (hshift _ hK)

omit [P.ContainsZero] in
lemma oppositeProperty_mappingCone
    (hshift : ∀ K, P K → P (K⟦(-1 : ℤ)⟧))
    {K L : CochainComplex Cᵒᵖ ℤ} (hK : oppositeProperty P K)
    (hL : oppositeProperty P L) (f : K ⟶ L) :
    oppositeProperty P (CochainComplex.mappingCone f) := by
  have hs : (CochainComplex.mappingCone.triangleRotateShortComplex f).ShortExact :=
    shortExact_of_degreewise_shortExact _
      (fun n => (CochainComplex.mappingCone.triangleRotateShortComplexSplitting f n).shortExact)
  exact CategoryTheory.ExactCategory.ExactStructure.IsExtensionClosed.prop_middle
    (E := abelianExactStructure (CochainComplex Cᵒᵖ ℤ)) (P := oppositeProperty P)
    hs hL (oppositeProperty_shift P hshift K hK)

end CochainComplex
