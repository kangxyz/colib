/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.ComplexSubcategory

public import Colib.Algebra.Homology.CochainComplex.OppositeQuasiIso
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.OppositeSubcategory
public import Colib.CategoryTheory.Waldhausen.Duality.ExactCategory
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks

/-!
# Genuine opposite Waldhausen structures on complex subcategories

Actual admissible epimorphisms become cofibrations on the literal opposite
full subcategory. Quasi-isomorphisms remain the original chain maps detected
by homology. Pullback gluing is proved by the exact original full inclusion,
the actual degree-reversing opposite equivalence, and genuine abelian complex
gluing. The resulting structure is compatible with the original zero-corner
kernel/cokernel squares.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Duality/ComplexSubcategory.lean` at
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

/-- Genuine pullback gluing for the original quasi-isomorphisms and admissible epimorphisms. -/
theorem complexSubcategoryPullbackGluing : HasPullbackGluing
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex C ℤ)) P).deflation
    (complexSubcategory P).weq where
  gluing {A B D T A' B' D' T'} {i j f g i' j' f' g'} a b d p hf hf' h h' ei ej ef eg hb hd hp := by
    let I := ExactSubcategory.exactInclusion (abelianExactStructure (CochainComplex C ℤ)) P
    have hfA := I.map_deflation f hf
    have hfA' := I.map_deflation f' hf'
    have : Epi f.hom := (abelianExactStructure_deflation_iff _ _).mp hfA
    have : Epi f'.hom := (abelianExactStructure_deflation_iff _ _).mp hfA'
    have hA : IsPullback i.hom j.hom f.hom g.hom := (I.map_isPullback h.flip hf).flip
    have hA' : IsPullback i'.hom j'.hom f'.hom g'.hom := (I.map_isPullback h'.flip hf').flip
    let E := (CochainComplex.opEquivalence C).functor
    let : E.IsEquivalence := (CochainComplex.opEquivalence C).isEquivalence_functor
    have hb' : QuasiIso b.hom := hb
    have hd' : QuasiIso d.hom := hd
    have hp' : QuasiIso p.hom := hp
    have : QuasiIso (E.map b.hom.op) := quasiIso_cochain_opEquivalence_functor_map _
    have : QuasiIso (E.map d.hom.op) := quasiIso_cochain_opEquivalence_functor_map _
    have : QuasiIso (E.map p.hom.op) := quasiIso_cochain_opEquivalence_functor_map _
    have ha := quasiIso_gluing (hA'.op.flip.map E) (hA.op.flip.map E)
      (E.map p.hom.op) (E.map b.hom.op) (E.map d.hom.op) (E.map a.hom.op)
      (by simpa only [← E.map_comp, ← op_comp, ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun k => E.map k.hom.op) ef.symm)
      (by simpa only [← E.map_comp, ← op_comp, ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun k => E.map k.hom.op) eg.symm)
      (by simpa only [← E.map_comp, ← op_comp, ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun k => E.map k.hom.op) ei.symm)
      (by simpa only [← E.map_comp, ← op_comp, ObjectProperty.FullSubcategory.comp_hom] using
        congrArg (fun k => E.map k.hom.op) ej.symm)
    exact (quasiIso_cochain_opEquivalence_functor_map_iff a.hom).mp ha

/-- The original opposite complex subcategory has admissible epi cofibrations. -/
def oppositeComplexSubcategory : Structure P.FullSubcategoryᵒᵖ :=
  exactDualStructure
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex C ℤ)) P)
    (complexSubcategory P) (complexSubcategoryPullbackGluing P)

lemma oppositeComplexSubcategory_compatible :
    IsCompatibleDual (complexSubcategory P) (oppositeComplexSubcategory P) :=
  exactDualStructure_compatible _ _ _ rfl

end CategoryTheory.Waldhausen
