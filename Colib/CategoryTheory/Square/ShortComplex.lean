/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Square

/-! # The signed short complex of a square -/

@[expose] public noncomputable section

namespace CategoryTheory.Square

open Limits

/-- The signed difference and sum construction on commutative squares. -/
def shortComplexFunctor (C : Type*) [Category* C] [Preadditive C] [HasBinaryBiproducts C] :
    Square C ⥤ ShortComplex C where
  obj A := A.commSq.shortComplex
  map {A B} f :=
    ShortComplex.homMk f.τ₁ (biprod.map f.τ₂ f.τ₃) f.τ₄ (by
      change f.τ₁ ≫ biprod.lift B.f₁₂ (-B.f₁₃) =
        biprod.lift A.f₁₂ (-A.f₁₃) ≫ biprod.map f.τ₂ f.τ₃
      apply biprod.hom_ext
      · simp
      · simpa only [Category.assoc, biprod.lift_snd_assoc, biprod.lift_snd, biprod.map_snd,
          Preadditive.comp_neg, Preadditive.neg_comp] using congrArg Neg.neg f.comm₁₃.symm)
      (by
        change biprod.map f.τ₂ f.τ₃ ≫ biprod.desc B.f₂₄ B.f₃₄ =
          biprod.desc A.f₂₄ A.f₃₄ ≫ f.τ₄
        apply biprod.hom_ext'
        · simp
        · simp)
  map_id A := by
    apply ShortComplex.hom_ext
    · rfl
    · change biprod.map (𝟙 A.X₂) (𝟙 A.X₃) = 𝟙 _
      apply biprod.hom_ext <;> simp
    · rfl
  map_comp f g := by
    apply ShortComplex.hom_ext
    · rfl
    · change biprod.map (f.τ₂ ≫ g.τ₂) (f.τ₃ ≫ g.τ₃) =
        biprod.map f.τ₂ f.τ₃ ≫ biprod.map g.τ₂ g.τ₃
      apply biprod.hom_ext <;> simp [Category.assoc]
    · rfl

section Comparison

variable {B N D : Type*} [Category* B] [Category* N] [Category* D]
  [Preadditive N] [HasBinaryBiproducts N] [HasZeroMorphisms D]
  (Q : B ⥤ N) (G : N ⥤ D) [G.PreservesZeroMorphisms]
  {A A' : Square B} {R : ShortComplex D}
  (p : R ≅ (A.map Q).commSq.shortComplex.map G) (h : A = A')

/-- Transport a signed row comparison along an equality of squares before applying
its coefficient and short-complex functors. -/
def compMapShortComplexIso : R ≅ (A'.map Q).commSq.shortComplex.map G :=
  p ≪≫ (Q.mapSquare ⋙ shortComplexFunctor N ⋙ G.mapShortComplex).mapIso (eqToIso h)

/-- The first component uses the transported first corner. -/
theorem compMapShortComplexIso_hom₁ :
    (compMapShortComplexIso Q G p h).hom.τ₁ =
      p.hom.τ₁ ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₁) h)) := by
  subst A'
  rfl

/-- The third component uses the transported fourth corner. -/
theorem compMapShortComplexIso_hom₃ :
    (compMapShortComplexIso Q G p h).hom.τ₃ =
      p.hom.τ₃ ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₄) h)) := by
  subst A'
  rfl

/-- The first projection of the middle component uses the transported second corner. -/
theorem compMapShortComplexIso_fst :
    (compMapShortComplexIso Q G p h).hom.τ₂ ≫
        G.map (biprod.fst : Q.obj A'.X₂ ⊞ Q.obj A'.X₃ ⟶ Q.obj A'.X₂) =
      (p.hom.τ₂ ≫ G.map (biprod.fst : Q.obj A.X₂ ⊞ Q.obj A.X₃ ⟶ Q.obj A.X₂)) ≫
        (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₂) h)) := by
  subst A'
  let f := (biprod.fst : Q.obj A.X₂ ⊞ Q.obj A.X₃ ⟶ Q.obj A.X₂)
  let m := biprod.map (Q.map (𝟙 A.X₂)) (Q.map (𝟙 A.X₃))
  change (p.hom.τ₂ ≫ G.map m) ≫ G.map f =
    (p.hom.τ₂ ≫ G.map f) ≫ G.map (Q.map (𝟙 A.X₂))
  have hm : m ≫ f = f ≫ Q.map (𝟙 A.X₂) := biprod.map_fst _ _
  calc
    _ = p.hom.τ₂ ≫ G.map (m ≫ f) :=
      (Category.assoc _ _ _).trans (congrArg (p.hom.τ₂ ≫ ·) (G.map_comp m f).symm)
    _ = p.hom.τ₂ ≫ G.map (f ≫ Q.map (𝟙 A.X₂)) := congrArg (fun g => p.hom.τ₂ ≫ G.map g) hm
    _ = _ := (congrArg (p.hom.τ₂ ≫ ·) (G.map_comp f _)).trans (Category.assoc _ _ _).symm

/-- The second projection of the middle component uses the transported third corner. -/
theorem compMapShortComplexIso_snd :
    (compMapShortComplexIso Q G p h).hom.τ₂ ≫
        G.map (biprod.snd : Q.obj A'.X₂ ⊞ Q.obj A'.X₃ ⟶ Q.obj A'.X₃) =
      (p.hom.τ₂ ≫ G.map (biprod.snd : Q.obj A.X₂ ⊞ Q.obj A.X₃ ⟶ Q.obj A.X₃)) ≫
        (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₃) h)) := by
  subst A'
  let f := (biprod.snd : Q.obj A.X₂ ⊞ Q.obj A.X₃ ⟶ Q.obj A.X₃)
  let m := biprod.map (Q.map (𝟙 A.X₂)) (Q.map (𝟙 A.X₃))
  change (p.hom.τ₂ ≫ G.map m) ≫ G.map f =
    (p.hom.τ₂ ≫ G.map f) ≫ G.map (Q.map (𝟙 A.X₃))
  have hm : m ≫ f = f ≫ Q.map (𝟙 A.X₃) := biprod.map_snd _ _
  calc
    _ = p.hom.τ₂ ≫ G.map (m ≫ f) :=
      (Category.assoc _ _ _).trans (congrArg (p.hom.τ₂ ≫ ·) (G.map_comp m f).symm)
    _ = p.hom.τ₂ ≫ G.map (f ≫ Q.map (𝟙 A.X₃)) := congrArg (fun g => p.hom.τ₂ ≫ G.map g) hm
    _ = _ := (congrArg (p.hom.τ₂ ≫ ·) (G.map_comp f _)).trans (Category.assoc _ _ _).symm

end Comparison

end CategoryTheory.Square
