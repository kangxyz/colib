/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.OrdinaryShiftComparison
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.ParameterProduct
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Continuity
public import Colib.CategoryTheory.Sites.SheafifyContinuous

/-!
# The parameter product on the ordinary motivic complex

The parameter product of reduced torus chains extends through the actual
Nisnevich sheafification unit. Ordinary motivic placement shifts the target
in the next weight by one, using the signed cochain shift.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicSimplex

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

section Evaluation

variable {C : Type*} [Category* C] [Preadditive C]
variable {F : C ⥤ C} [F.Additive] (ε : F ⟶ 𝟭 C)
variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

private def termwiseEvaluation (c : ComplexShape ι) : F.mapHomologicalComplex c ⟶ 𝟭 _ :=
  ε.mapHomologicalComplex c ≫ (Functor.mapHomologicalComplexIdIso C c).hom

private theorem termwiseEvaluation_app_f (N : HomologicalComplex C c) (i : ι) :
    ((termwiseEvaluation ε c).app N).f i = ε.app (N.X i) := by
  change ε.app (N.X i) ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem termwiseEvaluation_extend [HasZeroObject C] (e : c.Embedding c')
    (N : HomologicalComplex C c) :
    (Stacks.DerivedIndexing.mapExtendIso F e N).hom ≫ (termwiseEvaluation ε c').app (N.extend e) =
      (e.extendFunctor C).map ((termwiseEvaluation ε c).app N) := by
  let j := Functor.mapHomologicalComplexIdIso C c
  let j' := Functor.mapHomologicalComplexIdIso C c'
  have hId : (Stacks.DerivedIndexing.mapExtendIso (𝟭 C) e N).hom ≫ j'.hom.app (N.extend e) =
      (e.extendFunctor C).map (j.hom.app N) := by
    have h (i : Option ι) :
        (Stacks.DerivedIndexing.mapExtendXIso (𝟭 C) N i).hom ≫ 𝟙 _ =
          HomologicalComplex.extend.mapX (j.hom.app N) i := by
      cases i with
      | none => exact (HomologicalComplex.extend.isZero_X _ rfl).eq_of_src _ _
      | some n => exact Category.id_comp _
    ext i : 1
    exact h (e.r i)
  change (Stacks.DerivedIndexing.mapExtendIso F e N).hom ≫
      ((ε.mapHomologicalComplex c').app (N.extend e) ≫ j'.hom.app (N.extend e)) =
    (e.extendFunctor C).map ((ε.mapHomologicalComplex c).app N ≫ j.hom.app N)
  rw [← Category.assoc, ← Stacks.DerivedIndexing.mapExtendIso_hom_natTrans ε e N,
    Category.assoc, hId, ← Functor.map_comp]

private theorem termwiseEvaluation_shift (N : CochainComplex C ℤ) (s : ℤ) :
    ((F.mapCochainComplexShiftIso s).app N).inv ≫ (termwiseEvaluation ε (.up ℤ)).app (N⟦s⟧) =
      (shiftFunctor _ s).map ((termwiseEvaluation ε (.up ℤ)).app N) := by
  ext i : 1
  change 𝟙 _ ≫ ((termwiseEvaluation ε (.up ℤ)).app (N⟦s⟧)).f i =
    ((termwiseEvaluation ε (.up ℤ)).app N).f (i + s)
  rw [Category.id_comp, termwiseEvaluation_app_f, termwiseEvaluation_app_f]
  rfl

private theorem shiftedMap_comp_evaluation {A M N Z : CochainComplex C ℤ} (s : ℤ)
    (a : A ⟶ M⟦s⟧) (f : M ⟶ (F.mapHomologicalComplex (.up ℤ)).obj N)
    (hf : f ≫ (termwiseEvaluation ε (.up ℤ)).app N = 0) (b : N⟦s⟧ ⟶ Z) :
    (a ≫ (shiftFunctor _ s).map f ≫ ((F.mapCochainComplexShiftIso s).app N).inv ≫
      (F.mapHomologicalComplex (.up ℤ)).map b) ≫ (termwiseEvaluation ε (.up ℤ)).app Z = 0 := by
  have hNat : (F.mapHomologicalComplex (.up ℤ)).map b ≫ (termwiseEvaluation ε (.up ℤ)).app Z =
      (termwiseEvaluation ε (.up ℤ)).app (N⟦s⟧) ≫ b :=
    (termwiseEvaluation ε (.up ℤ)).naturality b
  have hShift : (shiftFunctor _ s).map f ≫ ((F.mapCochainComplexShiftIso s).app N).inv ≫
      (termwiseEvaluation ε (.up ℤ)).app (N⟦s⟧) = 0 := by
    rw [termwiseEvaluation_shift, ← (shiftFunctor _ s).map_comp, hf, Functor.map_zero]
  have h := congrArg (fun t ↦ a ≫ t ≫ b) hShift
  simpa only [Category.assoc, hNat, zero_comp, comp_zero] using h

private theorem extendedShiftedMap_comp_evaluation [HasZeroObject C] (e : c.Embedding (.up ℤ))
    {M N : HomologicalComplex C c} (s : ℤ) {A Z : CochainComplex C ℤ}
    (a : A ⟶ (M.extend e)⟦s⟧) (f : M ⟶ (F.mapHomologicalComplex c).obj N)
    (hf : f ≫ (termwiseEvaluation ε c).app N = 0) (b : (N.extend e)⟦s⟧ ⟶ Z) :
    (a ≫ (shiftFunctor _ s).map
      ((e.extendFunctor C).map f ≫ (Stacks.DerivedIndexing.mapExtendIso F e N).hom) ≫
      ((F.mapCochainComplexShiftIso s).app (N.extend e)).inv ≫
      (F.mapHomologicalComplex (.up ℤ)).map b) ≫ (termwiseEvaluation ε (.up ℤ)).app Z = 0 := by
  apply shiftedMap_comp_evaluation
  rw [Category.assoc, termwiseEvaluation_extend, ← (e.extendFunctor C).map_comp,
    hf, Functor.map_zero]

end Evaluation

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "T" =>
  SmoothSite.Contraction.parameterProduct (SmoothSite.multiplicativeGroupObject Sₖ)
local notation "P₀" q:max => Functor.obj (toPresheaf k) (reducedTorus k q)
local notation "K" q:max => Functor.obj (singularChainsFunctor k) (P₀ q)
local notation "L" q:max => Functor.obj (sheafifiedSingularChainsFunctor k Jₖ) (P₀ q)

/-- Evaluate Nisnevich sheaves on the actual product with the multiplicative group. -/
abbrev torusParameterSheafFunctor :
    Sheaf Jₖ AddCommGrpCat.{u + 1} ⥤ Sheaf Jₖ AddCommGrpCat.{u + 1} :=
  (T).sheafPushforwardContinuous _ Jₖ Jₖ

local notation "B" => torusParameterSheafFunctor k

/-- The sheaf map evaluating at the original unit section of the parameter. -/
def torusParameterSheafUnit : B ⟶ 𝟭 (Sheaf Jₖ AddCommGrpCat.{u + 1}) where
  app P := ⟨SmoothSite.Contraction.unit P.obj⟩
  naturality P Q f := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    exact (f.hom.naturality (SmoothSite.Contraction.unitSection.app U.unop).op).symm

/-- Evaluation at parameter one, applied to each term of the actual complex. -/
def torusParameterSheafComplexUnit {ι : Type*} (c : ComplexShape ι) :
    (B).mapHomologicalComplex c ⟶ 𝟭 _ :=
  (torusParameterSheafUnit k).mapHomologicalComplex c ≫ (Functor.mapHomologicalComplexIdIso _ c).hom

/-- The complex restriction has the original unit-section restriction in each degree. -/
theorem torusParameterSheafComplexUnit_app_f {ι : Type*} {c : ComplexShape ι}
    (N : HomologicalComplex (Sheaf Jₖ AddCommGrpCat.{u + 1}) c) (i : ι) :
    ((torusParameterSheafComplexUnit k c).app N).f i = (torusParameterSheafUnit k).app (N.X i) :=
  termwiseEvaluation_app_f (torusParameterSheafUnit k) c N i

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))
  AddCommGrpCat.{u + 1}]

/-- The actual ordinary parameter product on Nisnevich-sheafified reduced torus chains. -/
def sheafifiedReducedTorusSingularParameterProduct (q : ℕ) :
    L q ⟶ ((B).mapHomologicalComplex (.down ℕ)).obj (L (q + 1)) :=
  (T).sheafifyReindexComplexMap Jₖ Jₖ _ (.down ℕ) (reducedTorusSingularParameterProduct k q)

/-- The lift extends the original parameter product followed by sheafification on the
literal parameter product in each degree. -/
@[reassoc]
theorem toSheafify_sheafifiedReducedTorusSingularParameterProduct_f (q n : ℕ) :
    toSheafify Jₖ ((K q).X n) ≫ ((sheafifiedReducedTorusSingularParameterProduct k q).f n).hom =
      (reducedTorusSingularParameterProduct k q).f n ≫
        Functor.whiskerLeft (T).op (toSheafify Jₖ ((K (q + 1)).X n)) :=
  (T).toSheafify_sheafifyReindexComplexMap_f Jₖ Jₖ _ (.down ℕ)
    (reducedTorusSingularParameterProduct k q) n

/-- The sheafified chain map still vanishes at parameter one in every degree. -/
theorem sheafifiedReducedTorusSingularParameterProduct_f_unit (q n : ℕ) :
    (sheafifiedReducedTorusSingularParameterProduct k q).f n ≫
      (torusParameterSheafUnit k).app ((L (q + 1)).X n) = 0 := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext Jₖ _ _ ((L (q + 1)).X n).property
  let η := toSheafify Jₖ ((K (q + 1)).X n)
  have hη : Functor.whiskerLeft (T).op η ≫ SmoothSite.Contraction.unit ((L (q + 1)).X n).obj =
      SmoothSite.Contraction.unit ((K (q + 1)).X n) ≫ η := by
    apply NatTrans.ext
    funext U
    exact (η.naturality (SmoothSite.Contraction.unitSection.app U.unop).op).symm
  change toSheafify Jₖ ((K q).X n) ≫
        (((sheafifiedReducedTorusSingularParameterProduct k q).f n).hom ≫
          SmoothSite.Contraction.unit ((L (q + 1)).X n).obj) =
    toSheafify Jₖ ((K q).X n) ≫ 0
  rw [toSheafify_sheafifiedReducedTorusSingularParameterProduct_f_assoc, hη,
    ← Category.assoc, reducedTorusSingularParameterProduct_f_unit, zero_comp, comp_zero]

variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]

/-- The actual parameter product in ordinary motivic placement, with the next
weight shifted by one. -/
@[colib_tag "COL-1037", colib_ref "Voevodsky2003ReducedPowers"
  "Section 2, immediately before (2.1), p. 3" "ingredient"
  "External product of finite correspondences for integral motivic multiplication"]
def motivicSheafParameterProduct (q : ℕ) :
    motivicSheafComplex k q ⟶
      ((B).mapHomologicalComplex (.up ℤ)).obj ((motivicSheafComplex k (q + 1))⟦(1 : ℤ)⟧) := by
  let F := B
  let H := F.mapHomologicalComplex (.up ℤ)
  let e := ComplexShape.embeddingUpIntLE 0
  let M := L q
  let N := L (q + 1)
  let s : ℤ := -(q : ℤ)
  have hs : -((q + 1 : ℕ) : ℤ) + 1 = s := by
    dsimp [s]
    omega
  let f : M.extend e ⟶ H.obj (N.extend e) :=
    (e.extendFunctor _).map (sheafifiedReducedTorusSingularParameterProduct k q) ≫
      (Stacks.DerivedIndexing.mapExtendIso F e N).hom
  exact (motivicSheafComplexOrdinaryShiftIso k q).hom ≫ (shiftFunctor _ s).map f ≫
    ((F.mapCochainComplexShiftIso s).app (N.extend e)).inv ≫
    H.map (((shiftFunctorAdd' _ (-((q + 1 : ℕ) : ℤ)) 1 s hs).app (N.extend e)).hom ≫
      (shiftFunctor _ (1 : ℤ)).map (motivicSheafComplexOrdinaryShiftIso k (q + 1)).inv)

/-- The signed motivic parameter map has zero composite with the actual unit-section restriction. -/
@[colib_tag "COL-1037"]
theorem motivicSheafParameterProduct_unit (q : ℕ) :
    motivicSheafParameterProduct k q ≫
      (torusParameterSheafComplexUnit k (.up ℤ)).app ((motivicSheafComplex k (q + 1))⟦(1 : ℤ)⟧) =
        0 := by
  change _ ≫ (termwiseEvaluation (torusParameterSheafUnit k) (.up ℤ)).app _ = 0
  unfold motivicSheafParameterProduct
  dsimp only
  apply extendedShiftedMap_comp_evaluation
  ext n : 1
  rw [HomologicalComplex.comp_f, termwiseEvaluation_app_f, HomologicalComplex.zero_f]
  exact sheafifiedReducedTorusSingularParameterProduct_f_unit k q n

omit [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))
  AddCommGrpCat.{u + 1}] in
/-- The shifted target differential has the negative sign of the native cochain shift. -/
@[colib_tag "COL-1037"]
theorem motivicSheafParameterProduct_target_d (q : ℕ) (i j : ℤ) :
    (((B).mapHomologicalComplex (.up ℤ)).obj
      ((motivicSheafComplex k (q + 1))⟦(1 : ℤ)⟧)).d i j =
      -((B).map ((motivicSheafComplex k (q + 1)).d (i + 1) (j + 1))) := by
  change (B).map ((1 : ℤ).negOnePow • (motivicSheafComplex k (q + 1)).d (i + 1) (j + 1)) = _
  rw [Int.negOnePow_one, Units.neg_smul, one_smul, Functor.map_neg]

end AlgebraicGeometry.PresheafWithTransfers
