/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.Cousin
public import Mathlib.CategoryTheory.Sites.Abelian

/-! # Sections of a sheafified Cousin complex -/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.ExactSupportTower

variable {C A : Type*} [Category* C] [Category* A] [Abelian A]
  (J : GrothendieckTopology C) [HasSheafify J A] (T : ExactSupportTower (Cᵒᵖ ⥤ A))

/-- If the diagonal layers of a support tower are sheaves, the positive
cohomology of sections of the sheafified Cousin complex is the corresponding
unrestricted stage evaluated at the same object. -/
@[no_expose]
def sheafifiedCousinSectionsHomologySuccIso
    (hSheaf : ∀ p : ℕ, Presheaf.IsSheaf J (T.layer p p)) (U : C) (n : ℕ) :
    (((sheafToPresheaf J A ⋙ (evaluation _ _).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (T.map (presheafToSheaf J A)).cochainComplex).homology (n + 1) ≅
        (T.stage 0 (n + 1)).obj (op U) := by
  let K := T.cochainComplex
  let a := presheafToSheaf J A
  let b := sheafToPresheaf J A
  let E := (evaluation Cᵒᵖ A).obj (op U)
  let S := b ⋙ E
  let shape := ComplexShape.up ℕ
  let unit := (sheafificationAdjunction J A).unit
  let eTerm (p : ℕ) : E.obj (K.X p) ≅ (a ⋙ S).obj (K.X p) := by
    let : IsIso (unit.app (K.X p)) := isIso_toSheafify J (hSheaf p)
    exact E.mapIso (asIso (unit.app (K.X p)))
  let eComplex : (E.mapHomologicalComplex shape).obj K ≅
      (S.mapHomologicalComplex shape).obj ((a.mapHomologicalComplex shape).obj K) :=
    HomologicalComplex.Hom.isoOfComponents eTerm fun i j _ ↦ by
      have he := (unit.naturality (K.d i j)).symm
      exact (E.map_comp _ _).symm.trans ((E.congr_map he).trans (E.map_comp _ _))
  let eSections := eComplex ≪≫ (S.mapHomologicalComplex shape).mapIso (T.mapCochainComplexIso a)
  exact HomologicalComplex.homologyMapIso eSections.symm (n + 1) ≪≫
    HomologicalComplex.homologyMapIso (T.mapCochainComplexIso E) (n + 1) ≪≫
    (T.map E).homologySuccIso n

end CategoryTheory.ExactSupportTower
