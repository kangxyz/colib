/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.DerivedDetection
public import Colib.AlgebraicGeometry.SheavesWithTransfers.UnderlyingExactness
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CohomologyComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
import Colib.Algebra.Homology.DerivedCategory.KInjectiveAdjunction
import StacksFrontier.Homology.Ext.CorepresentedHomotopyComparison

/-!
# Detection of derived cohomology on the small Nisnevich site

Shifted Hom from the actual transfer representables on the étale
neighborhoods computes pointwise homology in a K-injective model.
Ordinary sheafification on that site recovers the restricted homology
sheaf and identifies the original map on it.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open Stacks.Cohomology.Corepresented

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k] [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

local notation "S" => Spec (CommRingCat.of k)

/-- Restrict the actual underlying ordinary sheaf to the actual small
Nisnevich site of the smooth scheme. -/
abbrev smallUnderlyingSheaf (X : SmoothSite S) :
    SheafWithTransfers.{u + 1} k ⥤
      Sheaf (EtaleSeparatedFiniteType.nisnevichTopology X.left) AddCommGrpCat.{u + 1} :=
  toSheaf k ⋙ EtaleSeparatedFiniteType.restrict X AddCommGrpCat.{u + 1}

omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] in
/-- Vanishing on every actual small Nisnevich site detects a zero
transfer coefficient. -/
theorem isZero_of_isZero_smallUnderlyingSheaf (F : SheafWithTransfers.{u + 1} k)
    (h : ∀ X : SmoothSite S, IsZero ((smallUnderlyingSheaf k X).obj F)) :
    IsZero F := by
  let J := SmoothSite.nisnevichTopology S
  let A := AddCommGrpCat.{u + 1}
  let U := toSheaf k ⋙ sheafToPresheaf J A
  have hF : IsZero (U.obj F) := (Functor.isZero_iff _).2 (by
    intro V
    let X := V.unop
    let x := EtaleSeparatedFiniteType.identityObject X
    let K := EtaleSeparatedFiniteType.nisnevichTopology X.left
    let E := (sheafSections K A).obj (op x)
    let e := EtaleSeparatedFiniteType.identityImageIso X
    exact (E.map_isZero (h X)).of_iso (((U.obj F).mapIso e.op)).symm)
  apply (IsZero.iff_id_eq_zero _).2
  apply U.map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 hF

private def smallSiteEvaluation (X : SmoothSite S)
    (V : EtaleSeparatedFiniteType X.left) :
    SheafWithTransfers.{u + 1} k ⥤ AddCommGrpCat.{u + 1} :=
  smallUnderlyingSheaf k X ⋙ sheafToPresheaf _ AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op V)

private instance (X : SmoothSite S) (V : EtaleSeparatedFiniteType X.left) :
    (smallSiteEvaluation k X V).Additive := by
  unfold smallSiteEvaluation
  infer_instance

private def smallSiteEvaluationRepresentedIso (X : SmoothSite S)
    (V : EtaleSeparatedFiniteType X.left) :
    preadditiveCoyoneda.obj (op ((transferRepresentable k).obj
      (Cor.mk ((EtaleSeparatedFiniteType.toSmoothSite X).obj V)))) ≅
      smallSiteEvaluation k X V :=
  let Y := Cor.mk ((EtaleSeparatedFiniteType.toSmoothSite X).obj V)
  NatIso.ofComponents (fun F => (transferSectionsEquiv k Y F).toAddCommGrpIso)
    (fun f => by
      ext a
      exact transferSectionsEquiv_comp k Y a f)

private def smallSiteEvaluationHomologyAddEquiv (X : SmoothSite S)
    (V : EtaleSeparatedFiniteType X.left)
    (I : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) [I.IsKInjective] (p : ℤ) :
    (((smallSiteEvaluation k X V).mapHomologicalComplex (.up ℤ)).obj I).homology p ≃+
      ((DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj
        (Cor.mk ((EtaleSeparatedFiniteType.toSmoothSite X).obj V))) ⟶
          (DerivedCategory.Q.obj I)⟦p⟧) :=
  let F := smallSiteEvaluation k X V
  let Y := (transferRepresentable k).obj (Cor.mk ((EtaleSeparatedFiniteType.toSmoothSite X).obj V))
  let e := (shiftFunctor (DerivedCategory (SheafWithTransfers.{u + 1} k)) p).mapIso
    ((DerivedCategory.quotientCompQhIso (SheafWithTransfers.{u + 1} k)).app I)
  let b := Preadditive.rightComp ((DerivedCategory.singleFunctor _ 0).obj Y) e.hom
  (corepresentedHomologyHomotopyAddEquiv F Y (smallSiteEvaluationRepresentedIso k X V) I p).trans
    ((AddEquiv.ofBijective (qhHomMap Y p I) (bijective_qhHomMap Y p I)).trans
      (AddEquiv.ofBijective b e.homToEquiv.bijective))

private theorem smallSiteEvaluationHomologyAddEquiv_naturality (X : SmoothSite S)
    (V : EtaleSeparatedFiniteType X.left)
    {I I' : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ} [I.IsKInjective] [I'.IsKInjective]
    (f : I ⟶ I') (p : ℤ)
    (x : (((smallSiteEvaluation k X V).mapHomologicalComplex (.up ℤ)).obj I).homology p) :
    smallSiteEvaluationHomologyAddEquiv k X V I' p
        (HomologicalComplex.homologyMap
          (((smallSiteEvaluation k X V).mapHomologicalComplex (.up ℤ)).map f) p x) =
      smallSiteEvaluationHomologyAddEquiv k X V I p x ≫ (DerivedCategory.Q.map f)⟦p⟧' := by
  let F := smallSiteEvaluation k X V
  let Y := (transferRepresentable k).obj (Cor.mk ((EtaleSeparatedFiniteType.toSmoothSite X).obj V))
  let U := HomotopyCategory.quotient (SheafWithTransfers.{u + 1} k) (.up ℤ)
  let e := smallSiteEvaluationRepresentedIso k X V
  let a := corepresentedHomologyHomotopyAddEquiv F Y e I p x
  let b := (DerivedCategory.quotientCompQhIso (SheafWithTransfers.{u + 1} k)).hom
  have h₀ := ConcreteCategory.congr_hom
    (corepresentedHomologyHomotopyIso_hom_naturality F Y e f p) x
  change corepresentedHomologyHomotopyAddEquiv F Y e I' p
        (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) p x) =
      a ≫ U.map (f⟦p⟧') at h₀
  have h₁ := qhHomMap_naturality Y p f a
  let R := shiftFunctor (DerivedCategory (SheafWithTransfers.{u + 1} k)) p
  simp only [smallSiteEvaluationHomologyAddEquiv, AddEquiv.trans_apply, AddEquiv.ofBijective_apply]
  change qhHomMap Y p I'
        (corepresentedHomologyHomotopyAddEquiv F Y e I' p
          (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) p x)) ≫
      R.map (b.app I') =
    (qhHomMap Y p I a ≫ R.map (b.app I)) ≫ R.map (DerivedCategory.Q.map f)
  have hb : DerivedCategory.Qh.map (U.map f) ≫ b.app I' = b.app I ≫ DerivedCategory.Q.map f :=
    b.naturality f
  rw [h₀, h₁, Category.assoc, ← R.map_comp, hb, R.map_comp, Category.assoc]

private theorem isIso_homologyMap_smallUnderlyingSheaf_of_kInjective
    (X : SmoothSite S) (p : ℤ)
    {I I' : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ} [I.IsKInjective] [I'.IsKInjective]
    (f : I ⟶ I')
    (h : ∀ V : EtaleSeparatedFiniteType X.left, Function.Bijective (fun a :
      (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj
        (Cor.mk ((EtaleSeparatedFiniteType.toSmoothSite X).obj V))) ⟶
          (DerivedCategory.Q.obj I)⟦p⟧ => a ≫ (DerivedCategory.Q.map f)⟦p⟧')) :
    IsIso ((smallUnderlyingSheaf k X).map (HomologicalComplex.homologyMap f p)) := by
  let J := EtaleSeparatedFiniteType.nisnevichTopology X.left
  let A := AddCommGrpCat.{u + 1}
  let G := smallUnderlyingSheaf k X
  let U := sheafToPresheaf J A
  let C := ((G ⋙ U).mapHomologicalComplex (.up ℤ))
  let f₀ := C.map f
  let μ := HomologicalComplex.homologyMap f₀ p
  let (V : (EtaleSeparatedFiniteType X.left)ᵒᵖ) : IsIso (μ.app V) := by
    let E := (CategoryTheory.evaluation _ A).obj V
    let e₀ := (((C.obj I).sc p).mapHomologyIso E)
    let e₁ := (((C.obj I').sc p).mapHomologyIso E)
    let F := smallSiteEvaluation k X V.unop
    let a := smallSiteEvaluationHomologyAddEquiv k X V.unop I p
    let b := smallSiteEvaluationHomologyAddEquiv k X V.unop I' p
    let g := HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) p
    have hg : IsIso g := (ConcreteCategory.isIso_iff_bijective _).2 (by
      have hh : b ∘ g = (fun y => y ≫ (DerivedCategory.Q.map f)⟦p⟧') ∘ a :=
        funext (smallSiteEvaluationHomologyAddEquiv_naturality k X V.unop f p)
      apply (Function.Bijective.of_comp_iff' b.bijective _).1
      rw [hh]
      exact (h V.unop).comp a.bijective)
    have hh : g ≫ e₁.hom = e₀.hom ≫ μ.app V :=
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) p).map f₀) E
    let : IsIso (e₀.hom ≫ μ.app V) := hh ▸ IsIso.comp_isIso' hg e₁.isIso_hom
    exact IsIso.of_isIso_comp_left e₀.hom (μ.app V)
  let : IsIso μ := NatIso.isIso_of_isIso_app μ
  let B := presheafToSheaf J A
  let ε := asIso (sheafificationAdjunction J A).counit
  let K := (G.mapHomologicalComplex (.up ℤ)).obj I
  let L := (G.mapHomologicalComplex (.up ℤ)).obj I'
  let f₁ := (G.mapHomologicalComplex (.up ℤ)).map f
  let h₀ := ((C.obj I).sc p).mapHomologyIso B
  let h₁ := ((C.obj I').sc p).mapHomologyIso B
  let d₀ := (NatIso.mapHomologicalComplex ε (.up ℤ)).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app K
  let d₁ := (NatIso.mapHomologicalComplex ε (.up ℤ)).app L ≪≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app L
  let e₀ := h₀.symm ≪≫ (HomologicalComplex.homologyFunctor _ (.up ℤ) p).mapIso d₀
  let e₁ := h₁.symm ≪≫ (HomologicalComplex.homologyFunctor _ (.up ℤ) p).mapIso d₁
  let H := HomologicalComplex.homologyFunctor (Sheaf J A) (.up ℤ) p
  let f₂ := ((U ⋙ B).mapHomologicalComplex (.up ℤ)).map f₁
  have h : B.map μ ≫ h₁.inv = h₀.inv ≫ H.map f₂ :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) p).map f₀) B
  have hd : f₂ ≫ d₁.hom = d₀.hom ≫ f₁ := by
    let d := NatIso.mapHomologicalComplex ε (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    exact d.hom.naturality f₁
  have hB : B.map μ ≫ e₁.hom = e₀.hom ≫ HomologicalComplex.homologyMap f₁ p := by
    change B.map μ ≫ (h₁.inv ≫ H.map d₁.hom) = (h₀.inv ≫ H.map d₀.hom) ≫ H.map f₁
    calc
      _ = (B.map μ ≫ h₁.inv) ≫ H.map d₁.hom := (Category.assoc _ _ _).symm
      _ = (h₀.inv ≫ H.map f₂) ≫ H.map d₁.hom := congrArg (· ≫ H.map d₁.hom) h
      _ = h₀.inv ≫ H.map (f₂ ≫ d₁.hom) :=
        (Category.assoc _ _ _).trans (congrArg (h₀.inv ≫ ·) (H.map_comp _ _).symm)
      _ = h₀.inv ≫ H.map (d₀.hom ≫ f₁) := congrArg (fun z => h₀.inv ≫ H.map z) hd
      _ = _ := (congrArg (h₀.inv ≫ ·) (H.map_comp _ _)).trans (Category.assoc _ _ _).symm
  let : IsIso (e₀.hom ≫ HomologicalComplex.homologyMap f₁ p) :=
    hB ▸ (inferInstance : IsIso (B.map μ ≫ e₁.hom))
  let : IsIso (HomologicalComplex.homologyMap f₁ p) :=
    IsIso.of_isIso_comp_left e₀.hom _
  apply (NatIso.isIso_map_iff (G.mapHomologicalComplexHomologyIso (.up ℤ) p) f).1
  change IsIso (HomologicalComplex.homologyMap f₁ p)
  infer_instance

/-- A bijection on the actual shifted Hom at all étale neighborhoods
makes the restricted cohomology map an isomorphism. -/
theorem isIso_smallUnderlyingSheaf_homologyMap_of_bijective_hom
    (X : SmoothSite S) (p : ℤ) {K L : DerivedCategory (SheafWithTransfers.{u + 1} k)}
    (f : K ⟶ L)
    (h : ∀ V : EtaleSeparatedFiniteType X.left, Function.Bijective (fun a :
      (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj
        (Cor.mk ((EtaleSeparatedFiniteType.toSmoothSite X).obj V))) ⟶ K⟦p⟧ =>
      a ≫ f⟦p⟧')) :
    IsIso ((smallUnderlyingSheaf k X).map ((DerivedCategory.homologyFunctor _ p).map f)) := by
  let A := SheafWithTransfers.{u + 1} k
  let P := DerivedCategory.Q.objPreimage K
  let P' := DerivedCategory.Q.objPreimage L
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor A).obj P
  let I' := (Stacks.Injectives.kInjectiveResolutionFunctor A).obj P'
  let e : DerivedCategory.Q.obj I ≅ K :=
    (asIso (DerivedCategory.Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion A).app P))).symm
      ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let e' : DerivedCategory.Q.obj I' ≅ L :=
    (asIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion A).app P'))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso L
  obtain ⟨g, hg⟩ := CochainComplex.IsKInjective.Q_map_surjective I I'
    (e.hom ≫ f ≫ e'.inv)
  have hI (V : EtaleSeparatedFiniteType X.left) :
      Function.Bijective (fun a :
        (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj
          (Cor.mk ((EtaleSeparatedFiniteType.toSmoothSite X).obj V))) ⟶
            (DerivedCategory.Q.obj I)⟦p⟧ => a ≫ (DerivedCategory.Q.map g)⟦p⟧') := by
    let S₀ := (DerivedCategory.singleFunctor _ 0).obj ((transferRepresentable k).obj
      (Cor.mk ((EtaleSeparatedFiniteType.toSmoothSite X).obj V)))
    let R := shiftFunctor (DerivedCategory (SheafWithTransfers.{u + 1} k)) p
    let a : (S₀ ⟶ R.obj (DerivedCategory.Q.obj I)) → (S₀ ⟶ R.obj K) :=
      ((R.mapIso e).homToEquiv : _ ≃ _)
    let b : (S₀ ⟶ R.obj L) → (S₀ ⟶ R.obj (DerivedCategory.Q.obj I')) :=
      ((R.mapIso e'.symm).homToEquiv : _ ≃ _)
    let c (x : S₀ ⟶ R.obj K) := x ≫ R.map f
    have hab : Function.Bijective (b ∘ c ∘ a) :=
      (R.mapIso e'.symm).homToEquiv.bijective.comp ((h V).comp (R.mapIso e).homToEquiv.bijective)
    have he : (fun x : S₀ ⟶ R.obj (DerivedCategory.Q.obj I) =>
        x ≫ R.map (DerivedCategory.Q.map g)) = b ∘ c ∘ a := by
      funext x
      change x ≫ R.map (DerivedCategory.Q.map g) =
        ((x ≫ R.map e.hom) ≫ R.map f) ≫ R.map e'.inv
      rw [hg, R.map_comp, R.map_comp]
      simp only [Category.assoc]
    exact he.symm ▸ hab
  let F := smallUnderlyingSheaf k X
  let H := DerivedCategory.homologyFunctor A p ⋙ F
  let : IsIso (F.map (HomologicalComplex.homologyMap g p)) :=
    isIso_homologyMap_smallUnderlyingSheaf_of_kInjective k X p g hI
  let : IsIso (H.map (DerivedCategory.Q.map g)) := by
    apply (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors A p) F) g).2
    change IsIso (F.map (HomologicalComplex.homologyMap g p))
    infer_instance
  have hgf : f = e.inv ≫ DerivedCategory.Q.map g ≫ e'.hom := by
    rw [hg]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change IsIso (H.map f)
  rw [hgf, Functor.map_comp, Functor.map_comp]
  infer_instance

end AlgebraicGeometry.SheafWithTransfers
