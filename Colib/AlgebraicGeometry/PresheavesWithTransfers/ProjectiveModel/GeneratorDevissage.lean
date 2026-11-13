/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.SingleCoproduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveRepresentable
import Colib.CategoryTheory.Preadditive.AdditiveFunctorGrothendieck
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# Testing bounded-above comparisons on transfer representables

Each projective coefficient is a retract of the direct sum of the
actual signed representables indexed by its sections. The native
single cofan and the finite brutal truncation test carry the comparison
from those representables to every bounded-above projective complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits ComplexShape

universe u w w' u' v'

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

/-- If both functors carry the single cofan of representables to
coproducts, invertibility on the representables gives invertibility on
a projective transfer coefficient placed in that degree. -/
theorem isIso_app_singleDerivedMinus_of_isIso_representable
    {D : Type u'} [Category.{v'} D]
    {F G : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤ D}
    (η : F ⟶ G) (n : ℤ)
    (h : ∀ X : Cor k,
      IsIso (η.app ((singleDerivedMinus k n).obj ((representableLarge k).obj X))))
    (P : PresheafWithTransfers.{u + 1} k) [Projective P]
    [PreservesColimit (Discrete.functor fun i : Σ X : Cor k, sections P X =>
      (singleDerivedMinus k n).obj ((representableLarge k).obj i.1)) F]
    [PreservesColimit (Discrete.functor fun i : Σ X : Cor k, sections P X =>
      (singleDerivedMinus k n).obj ((representableLarge k).obj i.1)) G] :
    IsIso (η.app ((singleDerivedMinus k n).obj P)) := by
  let I : Type (u + 1) := Σ X : Cor k, sections P X
  let X (i : I) := (representableLarge k).obj i.1
  let S := singleDerivedMinus k n
  let r := (retractRepresentableLargeCoproduct P).map S
  let d : Cofan (fun i => S.obj (X i)) := Cofan.mk (S.obj (∐ X))
    (fun i => S.map (Sigma.ι X i))
  let hd : IsColimit d := singleDerivedMinusCofanIsColimit k X n
  have hSum : IsIso (η.app d.pt) :=
    Stacks.DerivedCategoryComparisons.isIso_app_of_isColimit F G η
      (isColimitOfPreserves F hd) (isColimitOfPreserves G hd) (fun i => h i.as.1)
  exact Stacks.DerivedCategoryComparisons.isIso_app_of_retract η r hSum

/-- A comparison on the native bounded-above derived transfer category
can be checked on projective representables, provided the two functors
preserve their single coproducts and the specified upper bounds. -/
theorem isIso_app_of_isIso_singleDerivedMinus_representable
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
    {F G : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤ DerivedCategory B}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (η : F ⟶ G)
    (h : ∀ (X : Cor k) (n : ℤ),
      IsIso (η.app ((singleDerivedMinus k n).obj ((representableLarge k).obj X))))
    (hFsum : ∀ (I : Type (u + 1)) (X : I → Cor k) (n : ℤ),
      PreservesColimit
        (Discrete.functor fun i => (singleDerivedMinus k n).obj ((representableLarge k).obj (X i)))
        F)
    (hGsum : ∀ (I : Type (u + 1)) (X : I → Cor k) (n : ℤ),
      PreservesColimit
        (Discrete.functor fun i => (singleDerivedMinus k n).obj ((representableLarge k).obj (X i)))
        G)
    (c : ℤ)
    (hF : ∀ (K : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) (b : ℤ),
      K.obj.IsLE b → (F.obj K).IsLE (b + c))
    (hG : ∀ (K : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) (b : ℤ),
      K.obj.IsLE b → (G.obj K).IsLE (b + c))
    (K : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) :
    IsIso (η.app K) := by
  let A := PresheafWithTransfers.{u + 1} k
  obtain ⟨P, b, hb, hP, _, ⟨e⟩⟩ := exists_projectiveRepresentative K
  let : P.IsStrictlyLE b := hb
  let M := DerivedCategory.Minus.ofCochainComplex P b
  let d : M ≅ K := ObjectProperty.isoMk (DerivedCategory.TStructure.t (C := A)).minus e
  apply (η.isIso_app_iff_of_iso d).1
  apply DerivedCategory.Minus.isIso_app_ofCochainComplex_of_isIso_app_singleFunctor_X η P b c
  · intro p n
    let : Projective (P.X p) := hP p
    let I : Type (u + 1) := Σ X : Cor k, sections (P.X p) X
    let X (i : I) := i.1
    let : PreservesColimit
        (Discrete.functor fun i => (singleDerivedMinus k n).obj ((representableLarge k).obj (X i)))
        F := hFsum I X n
    let : PreservesColimit
        (Discrete.functor fun i => (singleDerivedMinus k n).obj ((representableLarge k).obj (X i)))
        G := hGsum I X n
    exact isIso_app_singleDerivedMinus_of_isIso_representable k η n (fun X => h X n) (P.X p)
  · intro a
    let M := DerivedCategory.Minus.ofCochainComplex (P.stupidTrunc (embeddingUpIntLE a)) a
    exact hF M a (inferInstanceAs ((DerivedCategory.Q.obj
      (P.stupidTrunc (embeddingUpIntLE a))).IsLE a))
  · intro a
    let M := DerivedCategory.Minus.ofCochainComplex (P.stupidTrunc (embeddingUpIntLE a)) a
    exact hG M a (inferInstanceAs ((DerivedCategory.Q.obj
      (P.stupidTrunc (embeddingUpIntLE a))).IsLE a))

end AlgebraicGeometry.PresheafWithTransfers
