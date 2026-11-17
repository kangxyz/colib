/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.SpecifiedCompletion
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # Comparing a distinguished triangle with the triangle of a short complex -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasShift C ℤ]
  [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.CommShift ℤ]
  {R : ShortComplex C} {L : ShortComplex D} {Z : C}
  (g : R.X₂ ⟶ Z) (δ : Z ⟶ R.X₁⟦(1 : ℤ)⟧)
  (a : Z ⟶ R.X₃) (ha : g ≫ a = R.g)
  (ε : L.X₃ ⟶ L.X₁⟦(1 : ℤ)⟧)
  (hV : F.mapTriangle.obj (Triangle.mk R.f g δ) ∈ distTriang D)
  (hW : Triangle.mk L.f L.g ε ∈ distTriang D)
  (h0 : Subsingleton ((F.obj R.X₁)⟦(1 : ℤ)⟧ ⟶ L.X₃))
  (e : R.map F ≅ L)

include ha hV hW h0 e in
/-- Under the indicated vanishing, a short-complex comparison and a chosen augmentation
give an isomorphism of the two distinguished triangles. -/
def triangleIsoOfShortComplexComparison :
    F.mapTriangle.obj (Triangle.mk R.f g δ) ≅ Triangle.mk L.f L.g ε := by
  let V := F.mapTriangle.obj (Triangle.mk R.f g δ)
  let W := Triangle.mk L.f L.g ε
  let x := ShortComplex.π₁.mapIso e
  let y := ShortComplex.π₂.mapIso e
  let z := ShortComplex.π₃.mapIso e
  have h₁ : V.mor₁ ≫ y.hom = x.hom ≫ W.mor₁ := e.hom.comm₁₂.symm
  have h₂ : V.mor₂ ≫ F.map a ≫ z.hom = y.hom ≫ W.mor₂ := by
    exact ((F.map_comp_assoc g a z.hom).symm.trans
      (congrArg (fun f => F.map f ≫ z.hom) ha)).trans e.hom.comm₂₃.symm
  let f := triangleMorphismOfSubsingleton hV hW h0 x.hom y.hom (F.map a ≫ z.hom) h₁ h₂
  let : IsIso f.hom₁ := inferInstanceAs (IsIso x.hom)
  let : IsIso f.hom₂ := inferInstanceAs (IsIso y.hom)
  let : IsIso f.hom₃ := isIso₃_of_isIso₁₂ f hV hW inferInstance inferInstance
  let : IsIso f := Triangle.isIso_of_isIsos f inferInstance inferInstance inferInstance
  exact asIso f

/-- The first triangle component is the first short-complex component. -/
theorem triangleIsoOfShortComplexComparison_hom₁ :
    (triangleIsoOfShortComplexComparison F g δ a ha ε hV hW h0 e).hom.hom₁ = e.hom.τ₁ := rfl

/-- The second triangle component is the second short-complex component. -/
theorem triangleIsoOfShortComplexComparison_hom₂ :
    (triangleIsoOfShortComplexComparison F g δ a ha ε hV hW h0 e).hom.hom₂ = e.hom.τ₂ := rfl

/-- The third triangle component is the mapped augmentation followed by the third
short-complex component. -/
theorem triangleIsoOfShortComplexComparison_hom₃ :
    (triangleIsoOfShortComplexComparison F g δ a ha ε hV hW h0 e).hom.hom₃ =
      F.map a ≫ e.hom.τ₃ := rfl

end CategoryTheory.Pretriangulated
