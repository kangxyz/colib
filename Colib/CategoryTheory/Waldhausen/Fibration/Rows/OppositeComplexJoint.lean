/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ComplexRelativeJoint

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Duality.ComplexSubcategory
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.EquivalenceJoint
public import Colib.Algebra.Homology.CochainComplex.OppositeQuasiIso

/-!
# Actual joint cocylinders through the opposite cochain equivalence

The displayed equivalence between the original opposite full subcategory and
actual opposite complexes is proved exact in both directions. The established
ambient complex cylinder then transports to genuine joint data on the original
opposite category, retaining its actual counit, endpoint maps, coproduct
universal property, factorization equation, and quasi-isomorphism projection.

The only extra closure assumption is the original negative shift; all cone
and exactness properties are discharged from the actual structures.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Fibration/Rows/OppositeComplexJoint.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual complexes, maps and independent universes are retained. -/

@[expose] public section

open CochainComplex


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : ObjectProperty (CochainComplex C ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex C ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The actual opposite full subcategory, with degree reversal, is equivalent
to the original full subcategory's literal opposite. -/
def oppositePropertyEquivalence : (oppositeProperty P).FullSubcategory ≌ P.FullSubcategoryᵒᵖ :=
  ((CochainComplex.opEquivalence C).symm.congrFullSubcategory
    (P := oppositeProperty P) (Q := P.op) rfl).trans P.opEquivalence

lemma oppositePropertyEquivalence_functor_exact : IsExact
    (complexSubcategory (oppositeProperty P)).cof (complexSubcategory (oppositeProperty P)).weq
    (oppositeComplexSubcategory P).cof (oppositeComplexSubcategory P).weq
    (oppositePropertyEquivalence P).functor where
  zero h := by
    let := (oppositePropertyEquivalence P).isEquivalence_functor
    exact (oppositePropertyEquivalence P).functor.map_isZero h
  cofibration {K L} f hf := by
    obtain ⟨Z, hZ, p, w, hs⟩ :=
      (ExactSubcategory.inflation_iff (abelianExactStructure _) (oppositeProperty P) f).mp hf
    apply (ExactSubcategory.deflation_iff (abelianExactStructure _) P _).mpr
    let S := ShortComplex.mk f.hom p w
    have hS : S.ShortExact := hs
    have := hS.mono_f
    have := hS.epi_g
    let T := (S.map (CochainComplex.opEquivalence C).inverse).unop
    have hT : T.ShortExact := (hS.map (CochainComplex.opEquivalence C).inverse).unop
    exact ⟨T.X₁, hZ, T.f, T.zero, hT⟩
  weak f hf := by
    have : QuasiIso f.hom := hf
    exact _root_.CochainComplex.quasiIso_cochain_opEquivalence_inverse_map f.hom
  pushout _ h := by
    let := (oppositePropertyEquivalence P).isEquivalence_functor
    exact h.map _

lemma oppositePropertyEquivalence_inverse_exact : IsExact
    (oppositeComplexSubcategory P).cof (oppositeComplexSubcategory P).weq
    (complexSubcategory (oppositeProperty P)).cof (complexSubcategory (oppositeProperty P)).weq
    (oppositePropertyEquivalence P).inverse where
  zero h := by
    let := (oppositePropertyEquivalence P).isEquivalence_inverse
    exact (oppositePropertyEquivalence P).inverse.map_isZero h
  cofibration {K L} f hf := by
    obtain ⟨Z, hZ, i, w, hs⟩ :=
      (ExactSubcategory.deflation_iff (abelianExactStructure _) P f.unop).mp hf
    apply (ExactSubcategory.inflation_iff (abelianExactStructure _) (oppositeProperty P) _).mpr
    let S := ShortComplex.mk i f.unop.hom w
    have hS : S.ShortExact := hs
    have := hS.mono_f
    have := hS.epi_g
    have hSO : S.op.ShortExact := hS.op
    have := hSO.mono_f
    have := hSO.epi_g
    let T := S.op.map (CochainComplex.opEquivalence C).functor
    have hT : T.ShortExact := hSO.map (CochainComplex.opEquivalence C).functor
    have hZ' : oppositeProperty P ((CochainComplex.opEquivalence C).functor.obj (op Z)) :=
      P.prop_of_iso ((CochainComplex.opEquivalence C).unitIso.app (op Z)).symm.unop hZ
    exact ⟨T.X₃, hZ', T.g, T.zero, hT⟩
  weak f hf := by
    have : QuasiIso f.unop.hom := hf
    exact quasiIso_cochain_opEquivalence_functor_map f.unop.hom
  pushout _ h := by
    let := (oppositePropertyEquivalence P).isEquivalence_inverse
    exact h.map _

/-- Both components use the same original ambient complex joint cylinder,
transported through the displayed exact opposite equivalence. -/
def oppositeComplexJointData
    (hshift : ∀ K, P K → P (K⟦(-1 : ℤ)⟧)) :
    Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl
      (oppositeComplexSubcategory P)) :=
  Fibration.RowFactorization.JointData.ofExactEquivalence
    (complexSubcategory (oppositeProperty P)) (oppositeComplexSubcategory P)
    (oppositePropertyEquivalence P) (oppositePropertyEquivalence_functor_exact P)
    (oppositePropertyEquivalence_inverse_exact P)
    (Fibration.complexJointDataOfNested (oppositeProperty P)
      (fun hK hL f => oppositeProperty_mappingCone P hshift hK hL f)
      (oppositeProperty_shift P hshift)
      (Fibration.NestedWeakEquivalences.refl (complexSubcategory (oppositeProperty P))))

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0311",
  colib_ref "quillen" "Quillen/Waldhausen/Fibration/Rows/OppositeComplexJoint.lean:50-122"
    "adaptation" "Actual exact opposite equivalence and transported original complex joint data"]
  CategoryTheory.Waldhausen.oppositePropertyEquivalence
  CategoryTheory.Waldhausen.oppositeComplexJointData
