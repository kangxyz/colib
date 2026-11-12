/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCochainAdjunction
public import Colib.CategoryTheory.Sites.Simplicial.ReducedPresheafCochainsSheafification

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Sites.LeftExact
import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective.AdjointAndProducts

/-!
# Parameter cylinders on homotopy classes of sheaf cochains

The homotopy adjunction for ordinary sheafification identifies maps out of
the original reduced sheaf cochains with maps out of the original reduced
presheaf cochains. The actual cylinder projection corresponds to the
parameter fold. The K-injective adjoint criterion transfers the hypothesis
of invertible projection pullback to this comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)

section

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The sheafification adjunction on the original homotopy classes of reduced cochains. -/
@[no_expose]
def reducedCochainsHomotopyHomEquiv (I : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ)
    (X : PointedSimplicialPresheaf.{w} C) :
    let c := ComplexShape.up ℤ
    let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) c
    let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{w}) c
    (H.obj ((reducedCochains C J).obj X) ⟶ H.obj I) ≃
      (Q.obj ((reducedPresheafCochains C).obj X) ⟶
        Q.obj (((sheafToPresheaf J AddCommGrpCat.{w}).mapHomologicalComplex c).obj I)) := by
  let c := ComplexShape.up ℤ
  let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) c
  let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{w}) c
  let a := (sheafificationAdjunction J AddCommGrpCat.{w}).mapHomotopyCategoryAdjunction c
  exact ((H.mapIso ((reducedCochainsSheafificationIso C J).app X)).homCongr
    (Iso.refl (H.obj I))).trans (a.homEquiv (Q.obj ((reducedPresheafCochains C).obj X)) (H.obj I))

set_option backward.isDefEq.respectTransparency false in
/-- The sheafification comparison carries precomposition to the same pointed map. -/
theorem reducedCochainsHomotopyHomEquiv_precomp
    (I : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) {X Y : PointedSimplicialPresheaf.{w} C}
    (f : X ⟶ Y)
    (g : (HomotopyCategory.quotient _ (.up ℤ)).obj ((reducedCochains C J).obj Y) ⟶
      (HomotopyCategory.quotient _ (.up ℤ)).obj I) :
    reducedCochainsHomotopyHomEquiv C J I X
        ((HomotopyCategory.quotient _ (.up ℤ)).map ((reducedCochains C J).map f) ≫ g) =
      (HomotopyCategory.quotient _ (.up ℤ)).map ((reducedPresheafCochains C).map f) ≫
        reducedCochainsHomotopyHomEquiv C J I Y g := by
  let c := ComplexShape.up ℤ
  let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{w}) c
  let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{w}) c
  let F := presheafToSheaf J AddCommGrpCat.{w}
  let a := (sheafificationAdjunction J AddCommGrpCat.{w}).mapHomotopyCategoryAdjunction c
  let P := reducedPresheafCochains.{w} C
  let R := reducedCochains.{w} C J
  let e : R ≅ P ⋙ F.mapHomologicalComplex c := reducedCochainsSheafificationIso C J
  let eX := H.mapIso (e.app X)
  let eY := H.mapIso (e.app Y)
  have h : H.map (R.map f) ≫ eY.hom =
      eX.hom ≫ (F.mapHomotopyCategory c).map (Q.map (P.map f)) := by
    change H.map (R.map f) ≫ H.map (e.hom.app Y) =
      H.map (e.hom.app X) ≫ H.map ((F.mapHomologicalComplex c).map (P.map f))
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map (e.hom.naturality f)
  have h' : eX.inv ≫ H.map (R.map f) =
      (F.mapHomotopyCategory c).map (Q.map (P.map f)) ≫ eY.inv := by
    apply (cancel_mono eY.hom).mp
    simp only [Category.assoc, h, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [reducedCochainsHomotopyHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]
  change a.homEquiv _ _ (eX.inv ≫ H.map (R.map f) ≫ g) =
    Q.map (P.map f) ≫ a.homEquiv _ _ (eY.inv ≫ g)
  calc
    _ = a.homEquiv _ _ ((F.mapHomotopyCategory c).map (Q.map (P.map f)) ≫ (eY.inv ≫ g)) := by
      exact congrArg (fun t ↦ a.homEquiv _ _ t)
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t ↦ t ≫ g) h').trans (Category.assoc _ _ _)))
    _ = _ := a.homEquiv_naturality_left _ _

end

variable [HasBinaryProducts C] [HasSheafify J AddCommGrpCat.{max v w}] (V : C)

set_option backward.isDefEq.respectTransparency false in
/-- If the underlying coefficient complex has quasi-isomorphic projection pullback,
the actual pointed cylinder projection is bijective on homotopy classes into it. -/
theorem bijective_precomp_reducedCochains_cylinder
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) [I.IsKInjective]
    (hI : QuasiIso ((ParameterCoproduct.homologicalProjectionPullback V AddCommGrpCat.{max v w}
      (.up ℤ)).app (((sheafToPresheaf J AddCommGrpCat.{max v w}).mapHomologicalComplex
        (.up ℤ)).obj I)))
    (X : PointedSimplicialPresheaf.{max v w} C) :
    let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max v w}) (.up ℤ)
    Function.Bijective (fun g : H.obj ((reducedCochains C J).obj X) ⟶ H.obj I ↦
      H.map ((reducedCochains C J).map (cylinderProjection X (liftedRepresentableInterval V))) ≫
        g) := by
  let A := AddCommGrpCat.{max v w}
  let c := ComplexShape.up ℤ
  let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ A) c
  let H := HomotopyCategory.quotient (Sheaf J A) c
  let P := reducedPresheafCochains.{max v w} C
  let R := reducedCochains.{max v w} C J
  let U := sheafToPresheaf J A
  let L : CochainComplex (Cᵒᵖ ⥤ A) ℤ := (U.mapHomologicalComplex c).obj I
  have : L.IsKInjective := CochainComplex.isKInjective_mapHomologicalComplex_of_exact U
    (presheafToSheaf J A) (sheafificationAdjunction J A) I
  let Y := parameterizedCylinder X (liftedRepresentableInterval V)
  let p : Y ⟶ X := cylinderProjection X (liftedRepresentableInterval V)
  let e := reducedPresheafCochainsParameterCylinderIso V X
  let s := Q.mapIso e
  let η := (ParameterCoproduct.homologicalFold V A c).app (P.obj X)
  have hp : Q.map (P.map p) = s.hom ≫ Q.map η := by
    change Q.map (P.map p) = Q.map e.hom ≫ Q.map η
    rw [← Q.map_comp]
    exact congrArg Q.map (reducedPresheafCochainsParameterCylinderIso_hom_fold V X).symm
  have : AB4OfSize.{v} A := AB4OfSize_shrink.{v, w} A
  have hη := ParameterCoproduct.bijective_precomp_homologicalFold V A (P.obj X) L hI
  have hPre : Function.Bijective (fun g : Q.obj (P.obj X) ⟶ Q.obj L ↦ Q.map (P.map p) ≫ g) := by
    let a := s.symm.homCongr (Iso.refl (Q.obj L))
    let pre : (Q.obj (((ParameterCoproduct.functor V A).mapHomologicalComplex c).obj
        (P.obj X)) ⟶ Q.obj L) → (Q.obj (P.obj Y) ⟶ Q.obj L) := fun g ↦ s.hom ≫ g
    have hfa : pre = ⇑a := by
      funext g
      change s.hom ≫ g = s.hom ≫ g ≫ 𝟙 _
      rw [Category.comp_id]
    have hs : Function.Bijective pre := by rw [hfa]; exact a.bijective
    rw [hp]
    simpa only [pre, Function.comp_def, Category.assoc] using hs.comp hη
  let E (Z : PointedSimplicialPresheaf.{max v w} C) := reducedCochainsHomotopyHomEquiv C J I Z
  have he : (fun g : H.obj (R.obj X) ⟶ H.obj I ↦ H.map (R.map p) ≫ g) =
      (E Y).symm ∘ (fun k ↦ Q.map (P.map p) ≫ k) ∘ (E X) := by
    funext g
    apply (E Y).injective
    change E Y (H.map (R.map p) ≫ g) = E Y ((E Y).symm (Q.map (P.map p) ≫ E X g))
    rw [Equiv.apply_symm_apply]
    exact reducedCochainsHomotopyHomEquiv_precomp C J I p g
  change Function.Bijective (fun g : H.obj (R.obj X) ⟶ H.obj I ↦ H.map (R.map p) ≫ g)
  rw [he]
  exact (E Y).symm.bijective.comp (hPre.comp (E X).bijective)

end CategoryTheory.PointedSimplicialPresheaf
