/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.DerivedCategory.MinusTermwiseInvertibility
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel
import Colib.CategoryTheory.Preadditive.AdditiveFunctorGrothendieck
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# Direct sums of single transfer complexes

Placing a coefficient in degree `n` preserves direct sums on the
original cochain complexes and their derived quotient. Every member
of the resulting derived cofan has the same upper bound.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

/-- The literal single complex placed in the native bounded-above
derived category. -/
def singleDerivedMinus (n : ℤ) :
    PresheafWithTransfers.{u + 1} k ⥤
      DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) where
  obj P := DerivedCategory.Minus.ofCochainComplex
    ((CochainComplex.singleFunctor _ n).obj P) n
  map f := ObjectProperty.homMk
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ n).map f))
  map_id P := by
    apply ObjectProperty.hom_ext
    change DerivedCategory.Q.map ((CochainComplex.singleFunctor _ n).map (𝟙 P)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    apply ObjectProperty.hom_ext
    change DerivedCategory.Q.map ((CochainComplex.singleFunctor _ n).map (f ≫ g)) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ n).map f) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor _ n).map g)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- The literal cofan on the singles of the original coefficients. -/
def singleDerivedMinusCofan {I : Type (u + 1)}
    (P : I → PresheafWithTransfers.{u + 1} k) [HasCoproduct P] (n : ℤ) :
    Cofan (fun i => (singleDerivedMinus k n).obj (P i)) :=
  Cofan.mk ((singleDerivedMinus k n).obj (∐ P))
    (fun i => (singleDerivedMinus k n).map (Sigma.ι P i))

/-- The original single cofan is a coproduct after the native
bounded-above inclusion into the full derived category. -/
@[no_expose]
def singleDerivedMinusCofanToDerivedIsColimit {I : Type (u + 1)}
    (P : I → PresheafWithTransfers.{u + 1} k) [HasCoproduct P] (n : ℤ) :
    IsColimit (DerivedCategory.Minus.ι.mapCocone (singleDerivedMinusCofan k P n)) := by
  let A := PresheafWithTransfers.{u + 1} k
  let S : A ⥤ CochainComplex A ℤ := CochainComplex.singleFunctor A n
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let V : DerivedCategory.Minus A ⥤ DerivedCategory A := DerivedCategory.Minus.ι
  let : PreservesColimitsOfShape (Discrete I) Q :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts A I
  let K := fun i => (singleDerivedMinus k n).obj (P i)
  let d : Discrete.functor K ⋙ V ≅ Discrete.functor (fun i => (S ⋙ Q).obj (P i)) :=
    Discrete.natIso (fun _ => Iso.refl _)
  let t := isColimitOfHasCoproductOfPreservesColimit (S ⋙ Q) P
  refine ((IsColimit.precomposeHomEquiv d _).symm t).ofIsoColimit ?_
  refine Cocone.ext (Iso.refl _) (fun i => ?_)
  change (𝟙 _ ≫ Q.map (S.map (Sigma.ι P i.as))) ≫ 𝟙 _ =
    Q.map (S.map (Sigma.ι P i.as))
  rw [Category.id_comp, Category.comp_id]

/-- The coprojections of the original coefficients remain coprojections
of their actual singles in the bounded-above derived category. -/
@[no_expose]
def singleDerivedMinusCofanIsColimit {I : Type (u + 1)}
    (P : I → PresheafWithTransfers.{u + 1} k) [HasCoproduct P] (n : ℤ) :
    IsColimit (Cofan.mk ((singleDerivedMinus k n).obj (∐ P))
      (fun i => (singleDerivedMinus k n).map (Sigma.ι P i))) := by
  let A := PresheafWithTransfers.{u + 1} k
  let V : DerivedCategory.Minus A ⥤ DerivedCategory A := DerivedCategory.Minus.ι
  let hV := ObjectProperty.fullyFaithfulι (DerivedCategory.TStructure.t (C := A)).minus
  let : V.Full := hV.full
  let : V.Faithful := hV.faithful
  let h : ReflectsColimitsOfShape (Discrete I) V :=
    (fullyFaithful_reflectsColimits V).reflectsColimitsOfShape
  exact isColimitOfReflects V (singleDerivedMinusCofanToDerivedIsColimit k P n)

end AlgebraicGeometry.PresheafWithTransfers
