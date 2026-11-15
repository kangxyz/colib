/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Coefficients
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.SingleCoproduct
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveCoefficientMap

/-! # Projective singles and termwise maps of coefficient functors -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

set_option quotPrecheck false in
local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ
local notation "S(" K ")" => CochainComplex.singleFunctor PST(K) (0 : ℤ)

variable [HasDerivedCategory.{w} PST(k)]

/-- Place a projective coefficient in a single degree of the native projective model. -/
def singleProjective (A : PST(k)) [Projective A] (n : ℤ) :
    BoundedAboveProjectiveHomotopy k :=
  ⟨(HomotopyCategory.quotient PST(k) c).obj ((CochainComplex.singleFunctor PST(k) n).obj A), n,
    inferInstanceAs (CochainComplex.IsStrictlyLE ((CochainComplex.singleFunctor PST(k) n).obj A) n),
    fun i => by
      by_cases hi : i = n
      · subst i
        exact Projective.of_iso (singleObjXSelf c n A).symm inferInstance
      · exact (isZero_single_obj_X c n A i hi).projective⟩

/-- The chosen projective model of a projective single is its original single complex. -/
def singleProjectiveComparison (A : PST(k)) [Projective A] (n : ℤ) :
    (boundedAboveProjectiveEquivalence k).inverse.obj ((singleDerivedMinus k n).obj A) ≅
      singleProjective A n := by
  let E := boundedAboveProjectiveEquivalence k
  let P := singleProjective A n
  let K := (CochainComplex.singleFunctor PST(k) n).obj A
  let a : E.functor.obj P ≅ (singleDerivedMinus k n).obj A :=
    ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso PST(k)).app K)
  exact E.inverse.mapIso a.symm ≪≫ (E.unitIso.app P).symm

/-- A projective coefficient in degree zero is sent to the image coefficient in degree zero. -/
def projectiveDerivedMinusFunctorSingleIso (G : PST(k) ⥤ PST(k)) [G.Additive]
    (A : PST(k)) [Projective A] :
    (projectiveDerivedMinusFunctor k G).obj ((singleDerivedMinus k 0).obj A) ≅
      (singleDerivedMinus k 0).obj (G.obj A) := by
  let K' := (G.mapHomologicalComplex c).obj ((S(k)).obj A)
  refine (projectiveHomotopyMapToDerivedMinus k G).mapIso (singleProjectiveComparison A 0) ≪≫
    ObjectProperty.isoMk _ ?_
  exact ((DerivedCategory.quotientCompQhIso PST(k)).app K') ≪≫
    DerivedCategory.Q.mapIso ((singleMapHomologicalComplex G c 0).app A)

/-- The original map of coefficients acts on the projective model by its literal single map. -/
theorem singleProjectiveComparison_naturality {A B : PST(k)} [Projective A] [Projective B]
    (f : A ⟶ B) (n : ℤ) :
    (boundedAboveProjectiveEquivalence k).inverse.map ((singleDerivedMinus k n).map f) ≫
        (singleProjectiveComparison B n).hom =
      (singleProjectiveComparison A n).hom ≫
        ObjectProperty.homMk ((HomotopyCategory.quotient PST(k) c).map
          ((CochainComplex.singleFunctor PST(k) n).map f)) := by
  let E := boundedAboveProjectiveEquivalence k
  let Q := HomotopyCategory.quotient PST(k) c
  let g := (CochainComplex.singleFunctor PST(k) n).map f
  let gP : singleProjective A n ⟶ singleProjective B n := ObjectProperty.homMk (Q.map g)
  let hA : E.functor.obj (singleProjective A n) ≅ (singleDerivedMinus k n).obj A :=
    ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso PST(k)).app _)
  let hB : E.functor.obj (singleProjective B n) ≅ (singleDerivedMinus k n).obj B :=
    ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso PST(k)).app _)
  have h : (singleDerivedMinus k n).map f ≫ hB.inv = hA.inv ≫ E.functor.map gP := by
    apply ObjectProperty.hom_ext
    change DerivedCategory.Q.map g ≫ (DerivedCategory.quotientCompQhIso PST(k)).inv.app _ =
      (DerivedCategory.quotientCompQhIso PST(k)).inv.app _ ≫ DerivedCategory.Qh.map (Q.map g)
    exact (DerivedCategory.quotientCompQhIso PST(k)).inv.naturality g
  change E.inverse.map ((singleDerivedMinus k n).map f) ≫
      E.inverse.map hB.inv ≫ E.unitIso.inv.app _ =
    (E.inverse.map hA.inv ≫ E.unitIso.inv.app _) ≫ gP
  have h' : E.inverse.map (E.functor.map gP) ≫ E.unitIso.inv.app (singleProjective B n) =
      E.unitIso.inv.app (singleProjective A n) ≫ gP := E.unitIso.inv.naturality gP
  rw [← E.inverse.map_comp_assoc, h, E.inverse.map_comp, Category.assoc, h', ← Category.assoc]

/-- Applying an additive coefficient functor to a projective single preserves
the original coefficient map. -/
theorem projectiveDerivedMinusFunctorSingleIso_naturality
    (G : PST(k) ⥤ PST(k)) [G.Additive] {A B : PST(k)} [Projective A] [Projective B]
    (f : A ⟶ B) :
    (projectiveDerivedMinusFunctor k G).map ((singleDerivedMinus k 0).map f) ≫
        (projectiveDerivedMinusFunctorSingleIso G B).hom =
      (projectiveDerivedMinusFunctorSingleIso G A).hom ≫
        (singleDerivedMinus k 0).map (G.map f) := by
  let I := projectiveHomotopyMapToDerivedMinus k G
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let q := HomotopyCategory.quotient PST(k) c
  let Q := DerivedCategory.Q (C := PST(k))
  let Qh := DerivedCategory.Qh (C := PST(k))
  let H := G.mapHomologicalComplex c
  let T := G.mapHomotopyCategory c
  let e := DerivedCategory.quotientCompQhIso PST(k)
  let a := singleProjectiveComparison A 0
  let b := singleProjectiveComparison B 0
  let g := (S(k)).map f
  let g₀ : singleProjective A 0 ⟶ singleProjective B 0 := ObjectProperty.homMk (q.map g)
  let h := singleMapHomologicalComplex G c 0
  let N := (boundedAboveProjectiveEquivalence k).inverse
  have h₁ : I.map (N.map ((singleDerivedMinus k 0).map f)) ≫ I.map b.hom =
      I.map a.hom ≫ I.map g₀ :=
    (I.map_comp _ _).symm.trans
      ((I.congr_map (singleProjectiveComparison_naturality f 0)).trans (I.map_comp _ _))
  apply V.map_injective
  simp only [projectiveDerivedMinusFunctorSingleIso, Iso.trans_hom, Functor.mapIso_hom, V.map_comp]
  change V.map (I.map (N.map ((singleDerivedMinus k 0).map f))) ≫
      (V.map (I.map b.hom) ≫ e.hom.app (H.obj ((S(k)).obj B)) ≫ Q.map (h.hom.app B)) =
    (V.map (I.map a.hom) ≫ e.hom.app (H.obj ((S(k)).obj A)) ≫ Q.map (h.hom.app A)) ≫
      Q.map ((S(k)).map (G.map f))
  rw [← Category.assoc (V.map (I.map (N.map ((singleDerivedMinus k 0).map f)))),
    ← V.map_comp, h₁, V.map_comp, Category.assoc]
  have h₂ : V.map (I.map g₀) = Qh.map (q.map (H.map g)) := by
    change Qh.map (T.map (q.map g)) = _
    rfl
  have h₃ := e.hom.naturality_assoc (H.map g) (Q.map (h.hom.app B))
  change Qh.map (q.map (H.map g)) ≫ e.hom.app (H.obj ((S(k)).obj B)) ≫
      Q.map (h.hom.app B) =
    e.hom.app (H.obj ((S(k)).obj A)) ≫ Q.map (H.map g) ≫ Q.map (h.hom.app B) at h₃
  have h₄ : Q.map (H.map g) ≫ Q.map (h.hom.app B) =
      Q.map (h.hom.app A) ≫ Q.map ((S(k)).map (G.map f)) := by
    rw [← Q.map_comp, ← Q.map_comp]
    exact Q.congr_map (h.hom.naturality f)
  simpa only [Category.assoc, h₂, h₃] using
    congrArg (fun m => V.map (I.map a.hom) ≫
      e.hom.app (H.obj ((S(k)).obj A)) ≫ m) h₄

/-- A natural transformation of coefficient functors induces its actual single map. -/
theorem projectiveDerivedMinusFunctorSingleIso_coefficientMap
    {G H : PST(k) ⥤ PST(k)} [G.Additive] [H.Additive] (f : G ⟶ H)
    (A : PST(k)) [Projective A] :
    (projectiveDerivedMinusFunctorMap f).app ((singleDerivedMinus k 0).obj A) ≫
        (projectiveDerivedMinusFunctorSingleIso H A).hom =
      (projectiveDerivedMinusFunctorSingleIso G A).hom ≫
        (singleDerivedMinus k 0).map (f.app A) := by
  let Q := DerivedCategory.Q (C := PST(k))
  let Qh := DerivedCategory.Qh (C := PST(k))
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let q := HomotopyCategory.quotient PST(k) c
  let K₀ := (S(k)).obj A
  let J := (boundedAboveProjectiveEquivalence k).inverse.obj ((singleDerivedMinus k 0).obj A)
  let z := (singleProjectiveComparison A 0).hom.hom
  let UG := G.mapHomotopyCategory c
  let UH := H.mapHomotopyCategory c
  let t := f.mapHomotopyCategory c
  let g := (f.mapHomologicalComplex c).app K₀
  let e := DerivedCategory.quotientCompQhIso PST(k)
  let u := (singleMapHomologicalComplex G c 0).hom.app A
  let v := (singleMapHomologicalComplex H c 0).hom.app A
  have h₁ : t.app J.obj ≫ UH.map z = UG.map z ≫ q.map g :=
    (t.naturality z).symm
  have h₂ : Qh.map (q.map g) ≫ e.hom.app ((H.mapHomologicalComplex c).obj K₀) ≫ Q.map v =
      e.hom.app ((G.mapHomologicalComplex c).obj K₀) ≫ Q.map g ≫ Q.map v :=
    e.hom.naturality_assoc g (Q.map v)
  have h₃ : Q.map g ≫ Q.map v = Q.map u ≫ Q.map ((S(k)).map (f.app A)) := by
    rw [← Q.map_comp, ← Q.map_comp]
    apply Q.congr_map
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      change f.app (K₀.X 0) ≫ v.f 0 = u.f 0 ≫ ((S(k)).map (f.app A)).f 0
      rw [singleMapHomologicalComplex_hom_app_self, singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc,
        ← f.naturality_assoc]
    · exact (G.map_isZero (HomologicalComplex.isZero_single_obj_X c 0 A i hi)).eq_of_src _ _
  apply V.map_injective
  rw [V.map_comp, V.map_comp, projectiveDerivedMinusFunctorMap_map_app]
  change Qh.map (t.app J.obj) ≫
      (Qh.map (UH.map z) ≫ e.hom.app ((H.mapHomologicalComplex c).obj K₀) ≫ Q.map v) =
    (Qh.map (UG.map z) ≫ e.hom.app ((G.mapHomologicalComplex c).obj K₀) ≫ Q.map u) ≫
      Q.map ((S(k)).map (f.app A))
  rw [← Qh.map_comp_assoc, h₁, Qh.map_comp, Category.assoc]
  calc
    _ = Qh.map (UG.map z) ≫ e.hom.app ((G.mapHomologicalComplex c).obj K₀) ≫
          Q.map g ≫ Q.map v := congrArg (Qh.map (UG.map z) ≫ ·) h₂
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun m => Qh.map (UG.map z) ≫
          e.hom.app ((G.mapHomologicalComplex c).obj K₀) ≫ m) h₃

end AlgebraicGeometry.PresheafWithTransfers
