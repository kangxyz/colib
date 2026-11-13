/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.LiteralSingleReflection
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusAdjunction
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusRightRepresentable
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.RepresentableTranspose

/-!
# The actual reduced torus unit on smooth motives

On a degree-zero projective representable, the effective tensor is the
singular motive of the original target-unit quotient. Under this comparison
the effective adjunction unit is the original cancellation map into the
reduced torus sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w₁ w₂ w₃

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₃} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "V" => DerivedCategory.Minus.ι (C := NST)
local notation "J" => effectiveMotivesMinusToDerived k
local notation "I" => effectiveMotivesMinusInclusion k
local notation "M" => effectiveReflection k
local notation "L" => effectiveReducedTorusTensorFunctor k
local notation "R" => effectiveReducedTorusSectionsFunctor k
local notation "Q" => singularEffectiveMotiveFunctor k
local notation "A" => nisnevichSheafify k
local notation "a" => derivedNisnevichSheafification k
local notation "F" => forgetDerivedFunctor k
set_option quotPrecheck false in
local notation "η" => (effectiveReflectionAdjunction k).unit
local notation "sₚ" => CochainComplex.singleFunctor PST 0

private def projectiveEffectiveTorusRepresentableIso (Y : Cor k) :
    (projectiveEffectiveTorus k).obj (singleTransferRepresentable k Y) ≅
      (Q).obj (torusCancellationCoefficients k Y) :=
  (M).mapIso (projectiveReducedTorusRepresentableSingleIso k Y) ≪≫
    singleSheafReflectionIso k (torusCancellationCoefficients k Y)

/-- The actual reduced effective tensor of a smooth motive is the singular
motive of the original target-unit quotient. -/
@[no_expose]
def effectiveReducedTorusTensorRepresentableIso (Y : Cor k) :
    (L).obj ((effectiveMotive k).obj Y) ≅ (Q).obj (torusCancellationCoefficients k Y) :=
  ((L).mapIso (singleEffectiveReflectionIso k ((representableLarge k).obj Y))).symm ≪≫
    (projectiveEffectiveTorusComparison k (singleTransferRepresentable k Y)).symm ≪≫
    projectiveEffectiveTorusRepresentableIso k Y

/-- The effective comparison uses the literal reflected source and target
and the original quotient on the projective representative. -/
theorem effectiveReducedTorusTensorRepresentableIso_hom (Y : Cor k) :
    (effectiveReducedTorusTensorRepresentableIso k Y).hom =
      (L).map (singleEffectiveReflectionIso k ((representableLarge k).obj Y)).inv ≫
        (projectiveEffectiveTorusComparison k (singleTransferRepresentable k Y)).inv ≫
        (M).map (projectiveReducedTorusRepresentableSingleIso k Y).hom ≫
        (singleSheafReflectionIso k (torusCancellationCoefficients k Y)).hom := by
  unfold effectiveReducedTorusTensorRepresentableIso projectiveEffectiveTorusRepresentableIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Functor.mapIso_hom]

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
private theorem projectiveEffectiveTorusRepresentableIso_unit (Y : Cor k) :
    (V).map ((effectiveReflectionAdjunction k).homEquiv _
      ((Q).obj (torusCancellationCoefficients k Y))
        (projectiveEffectiveTorusRepresentableIso k Y).hom) =
      (projectiveReducedTorusRepresentableSingleIso k Y).hom.hom ≫
        DerivedCategory.Q.map (torusTensorRepresentableTargetAugmentation k Y) := by
  let e := projectiveReducedTorusRepresentableSingleIso k Y
  let X := (projectiveReducedTorusTensorToDerivedMinus k).obj (singleTransferRepresentable k Y)
  let K := singleTorusCancellationSheaf k Y
  let C := torusCancellationCoefficients k Y
  let f := singleSheafReflectionIso k C
  let h := (M).map e.hom
  let Qₛ := DerivedCategory.Q (C := NST)
  let m := torusTensorRepresentableTargetAugmentation k Y
  have hn := (V).congr_map ((η).naturality e.hom)
  change (V).map (e.hom ≫ (η).app K) =
    (V).map ((η).app X ≫ (I).map ((M).map e.hom)) at hn
  rw [Functor.map_comp, Functor.map_comp] at hn
  change (V).map e.hom ≫ (V).map ((η).app K) = (V).map ((η).app X) ≫ (J).map h at hn
  have hu : (V).map ((η).app K) ≫ (J).map f.hom = Qₛ.map m :=
    singleSheafReflectionIso_unit k C
  rw [Adjunction.homEquiv_unit]
  change (V).map ((η).app X ≫ (I).map (h ≫ f.hom)) = (V).map e.hom ≫ Qₛ.map m
  calc
    _ = ((V).map ((η).app X) ≫ (J).map h) ≫ (J).map f.hom :=
      ((V).map_comp _ _).trans
        ((congrArg ((V).map ((η).app X) ≫ ·) ((J).map_comp _ _)).trans
          (Category.assoc _ _ _).symm)
    _ = ((V).map e.hom ≫ (V).map ((η).app K)) ≫ (J).map f.hom :=
      congrArg (· ≫ (J).map f.hom) hn.symm
    _ = _ := (Category.assoc _ _ _).trans (congrArg ((V).map e.hom ≫ ·) hu)

private theorem projectiveEffectiveTorusRepresentableTranspose (Y : Cor k) :
    let P := singleTransferRepresentable k Y
    let K := (Q).obj (torusCancellationCoefficients k Y)
    let e := singleEffectiveReflectionIso k ((representableLarge k).obj Y)
    projectiveEffectiveTorusHomEquiv k P K (projectiveEffectiveTorusRepresentableIso k Y).hom =
      (η).app ((a).obj P) ≫ (I).map (e.hom ≫ (effectiveMotiveReducedTorusIso k Y).hom) := by
  intro P K e
  let A' := nisnevichDerivedAdjunction k
  let C := effectiveMotiveReducedTorusIso k Y
  let t := (effectiveReducedTorusSectionsToDerivedIso k).app K
  let j := (effectiveReducedTorusSectionsInclusion k).app K
  let E := (torusSectionsDerivedForgetIso k).app ((J).obj K)
  let f := projectiveEffectiveTorusRepresentableIso k Y
  let g := (V).map ((effectiveReflectionAdjunction k).homEquiv _ K f.hom)
  let H := A'.homEquiv P.obj ((J).obj ((R).obj K))
  let d := (Functor.FullyFaithful.ofFullyFaithful V).homEquiv
    (X := (a).obj P) (Y := (I).obj ((R).obj K))
  let ι := (reducedTorusSectionsDerivedInclusion k).app ((J).obj K)
  let π := (reducedTorusSectionsDerivedProjection k).app ((J).obj K)
  have hj : j = t.hom ≫ ι := rfl
  have hi : ι ≫ π = 𝟙 _ :=
    reducedTorusSectionsDerivedInclusion_projection k ((J).obj K)
  have hjπ : (F).map j ≫ ((F).map π ≫ (F).map t.inv) = 𝟙 _ := by
    have h : j ≫ (π ≫ t.inv) = 𝟙 _ := by
      calc
        _ = (t.hom ≫ (ι ≫ π)) ≫ t.inv := by
          rw [hj]
          simp only [Category.assoc]
        _ = t.hom ≫ t.inv := congrArg (· ≫ t.inv)
          ((congrArg (t.hom ≫ ·) hi).trans (Category.comp_id _))
        _ = _ := t.hom_inv_id
    have hπ : (F).map π ≫ (F).map t.inv = (F).map (π ≫ t.inv) :=
      ((F).map_comp π t.inv).symm
    exact (congrArg ((F).map j ≫ ·) hπ).trans
      (((F).map_comp _ _).symm.trans (((F).congr_map h).trans ((F).map_id _)))
  let E₀ : (P.obj ⟶ (F).obj ((torusSectionsDerivedFunctor k).obj ((J).obj K))) ≃
      (P.obj ⟶ (torusTensorDerivedRight k).obj ((J).obj K)) := E.homToEquiv
  let tr : (P.obj ⟶ (F).obj ((J).obj ((R).obj K))) →
      (P.obj ⟶ (torusTensorDerivedRight k).obj ((J).obj K)) :=
    fun h => (h ≫ (F).map j) ≫ E.hom
  have hinj : Function.Injective tr := by
    intro x y h
    have h₁ : x ≫ (F).map j = y ≫ (F).map j := E₀.injective h
    let p := (F).map π ≫ (F).map t.inv
    have he (z : P.obj ⟶ (F).obj ((J).obj ((R).obj K))) :
        (z ≫ (F).map j) ≫ p = z :=
      (Category.assoc _ _ _).trans
        ((congrArg (z ≫ ·) hjπ).trans (Category.comp_id z))
    exact (he x).symm.trans ((congrArg (· ≫ p) h₁).trans (he y))
  have hj' : (F).map t.inv ≫ (F).map j = (F).map ι :=
    ((F).map_comp _ _).symm.trans
      ((F).congr_map ((congrArg (t.inv ≫ ·) hj).trans (t.inv_hom_id_assoc _)))
  let Hᵣ := projectiveReducedTorusTensorDerivedHomEquiv k P ((J).obj K)
  let H₀ := projectiveTorusTensorDerivedHomEquiv k P ((J).obj K)
  let q := (V).map ((projectiveReducedTorusTensorQuotient k).app P)
  have hL :
      ((Hᵣ g ≫ (F).map t.inv) ≫ (F).map j) ≫ E.hom = H₀ (q ≫ g) := by
    calc
      _ = (Hᵣ g ≫ ((F).map t.inv ≫ (F).map j)) ≫ E.hom :=
        congrArg (· ≫ E.hom) (Category.assoc _ _ _)
      _ = Hᵣ g ≫ (F).map ι ≫ E.hom :=
        (congrArg (fun z => (Hᵣ g ≫ z) ≫ E.hom) hj').trans (Category.assoc _ _ _)
      _ = _ := projectiveReducedTorusTensorDerivedHomEquiv_inclusion k P ((J).obj K) g
  let m := (V).map ((η).app ((a).obj P) ≫ (I).map (e.hom ≫ C.hom))
  let K' := (torusSectionsDerivedFunctor k).obj ((J).obj K)
  let H' := A'.homEquiv P.obj K'
  let P₀ := (representableLarge k).obj Y
  let d₀ := (A).mapDerivedCategoryFactors.hom.app ((sₚ).obj P₀)
  let a₀ := DerivedCategory.Q.map (((A).mapHomologicalComplex (.up ℤ)).map
    (singularCochainUnitApp P₀))
  let c₀ := cancellationRepresentableDerivedMap k Y
  have hR : (V).map ((η).app ((a).obj P) ≫ (I).map (e.hom ≫ C.hom)) ≫ j =
      d₀ ≫ a₀ ≫ c₀ := by
    let u := (V).map ((η).app ((a).obj P))
    let b := (J).map e.hom
    have hu : u ≫ b = d₀ ≫ a₀ := singleEffectiveReflectionIso_unit k P₀
    have hc : (J).map C.hom ≫ j = c₀ := effectiveMotiveReducedTorusIso_hom_inclusion k Y
    simp only [Functor.map_comp, Category.assoc]
    change u ≫ b ≫ (J).map C.hom ≫ j = _
    exact (congrArg (u ≫ b ≫ ·) hc).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ c₀) hu).trans (Category.assoc _ _ _)))
  let p := (projectiveReducedTorusRepresentableSingleIso k Y).hom.hom
  let Qₛ := DerivedCategory.Q (C := NST)
  let x := (Qₛ).map (torusTensorRepresentableSingleQuotient k Y)
  let y := (Qₛ).map (torusTensorRepresentableTargetAugmentation k Y)
  let z := (projectiveTorusRepresentableSingleModelIso k Y).hom
  have hg : g = p ≫ y := projectiveEffectiveTorusRepresentableIso_unit k Y
  have hq : q ≫ p = z ≫ x := projectiveReducedTorusRepresentableSingleIso_quotient k Y
  have hM : q ≫ g = z ≫ x ≫ y :=
    (congrArg (q ≫ ·) hg).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ y) hq).trans (Category.assoc _ _ _)))
  have hF : H ((V).map (projectiveEffectiveTorusHomEquiv k P K f.hom)) =
      Hᵣ g ≫ (F).map t.inv := projectiveEffectiveTorusHomEquiv_map k P K f.hom
  have hn : H' (m ≫ j) = H m ≫ (F).map j := A'.homEquiv_naturality_right m j
  apply (d.trans H).injective
  apply hinj
  change (H ((V).map (projectiveEffectiveTorusHomEquiv k P K f.hom)) ≫ (F).map j) ≫
    E.hom = (H m ≫ (F).map j) ≫ E.hom
  calc
    _ = ((Hᵣ g ≫ (F).map t.inv) ≫ (F).map j) ≫ E.hom :=
      congrArg (fun z => (z ≫ (F).map j) ≫ E.hom) hF
    _ = H₀ (q ≫ g) := hL
    _ = H₀ (z ≫ x ≫ y) := congrArg H₀ hM
    _ = H' (d₀ ≫ a₀ ≫ c₀) ≫ E.hom := projectiveTorusRepresentableCancellationTranspose k Y
    _ = _ := (congrArg (fun z => H' z ≫ E.hom) hR.symm).trans (congrArg (· ≫ E.hom) hn)

/-- The unit transported through the actual tensor comparison is the
original representable cancellation isomorphism. -/
theorem effectiveReducedTorusTensorAdjunction_unit_app_representable (Y : Cor k) :
    (effectiveReducedTorusTensorAdjunction k).unit.app ((effectiveMotive k).obj Y) ≫
        (R).map (effectiveReducedTorusTensorRepresentableIso k Y).hom =
      (effectiveMotiveReducedTorusIso k Y).hom := by
  let P := singleTransferRepresentable k Y
  let X := (M).obj ((a).obj P)
  let Z := (effectiveMotive k).obj Y
  let K := (Q).obj (torusCancellationCoefficients k Y)
  let e := singleEffectiveReflectionIso k ((representableLarge k).obj Y)
  let C := effectiveMotiveReducedTorusIso k Y
  let f := projectiveEffectiveTorusRepresentableIso k Y
  let p := projectiveEffectiveTorusComparison k P
  let U := (effectiveReducedTorusTensorAdjunction k).unit
  let A' := effectiveReflectionAdjunction k
  let a₀ := A'.homEquiv ((a).obj P) ((R).obj K)
  let b := p.inv ≫ f.hom
  let u := (η).app ((a).obj P)
  have hf : f.hom = p.hom ≫ (p.inv ≫ f.hom) := (p.hom_inv_id_assoc _).symm
  have hp : projectiveEffectiveTorusHomEquiv k P ((L).obj X) p.hom = u ≫ (I).map (U.app X) :=
    projectiveEffectiveTorusComparison_hom_unit k P
  have ht : projectiveEffectiveTorusHomEquiv k P K f.hom = u ≫ (I).map (e.hom ≫ C.hom) :=
    projectiveEffectiveTorusRepresentableTranspose k Y
  have h : u ≫ (I).map (U.app X ≫ (R).map b) = u ≫ (I).map (e.hom ≫ C.hom) := by
    calc
      _ = (u ≫ (I).map (U.app X)) ≫ (I).map ((R).map b) :=
        (congrArg (u ≫ ·) ((I).map_comp _ _)).trans (Category.assoc _ _ _).symm
      _ = projectiveEffectiveTorusHomEquiv k P ((L).obj X) p.hom ≫ (I).map ((R).map b) :=
        congrArg (· ≫ (I).map ((R).map b)) hp.symm
      _ = projectiveEffectiveTorusHomEquiv k P K (p.hom ≫ b) :=
        (projectiveEffectiveTorusHomEquiv_postcompose k P b p.hom).symm
      _ = _ := (congrArg (projectiveEffectiveTorusHomEquiv k P K) hf.symm).trans ht
  have h' : U.app X ≫ (R).map b = e.hom ≫ C.hom :=
    a₀.injective ((A'.homEquiv_unit _ _ _).trans (h.trans (A'.homEquiv_unit _ _ _).symm))
  have he : U.app Z ≫ (R).map ((L).map e.inv) = e.inv ≫ U.app X :=
    (U.naturality e.inv).symm
  have hs : (effectiveReducedTorusTensorRepresentableIso k Y).hom = (L).map e.inv ≫ b := by
    unfold effectiveReducedTorusTensorRepresentableIso
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
    rfl
  calc
    _ = (U.app Z ≫ (R).map ((L).map e.inv)) ≫ (R).map b :=
      (congrArg (fun z => U.app Z ≫ (R).map z) hs).trans
        ((congrArg (U.app Z ≫ ·) ((R).map_comp _ _)).trans (Category.assoc _ _ _).symm)
    _ = e.inv ≫ U.app X ≫ (R).map b :=
      (congrArg (· ≫ (R).map b) he).trans (Category.assoc _ _ _)
    _ = _ := (congrArg (e.inv ≫ ·) h').trans (e.inv_hom_id_assoc _)

/-- Cancellation makes the actual effective torus tensor adjunction unit
invertible on each smooth representable motive. -/
theorem isIso_effectiveReducedTorusTensorAdjunction_unit_app_representable (Y : Cor k) :
    IsIso ((effectiveReducedTorusTensorAdjunction k).unit.app ((effectiveMotive k).obj Y)) := by
  let e := effectiveReducedTorusTensorRepresentableIso k Y
  have h : IsIso ((effectiveReducedTorusTensorAdjunction k).unit.app
      ((effectiveMotive k).obj Y) ≫ (R).map e.hom) := by
    rw [effectiveReducedTorusTensorAdjunction_unit_app_representable]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((R).map e.hom)

end AlgebraicGeometry.MotivicHomotopy
