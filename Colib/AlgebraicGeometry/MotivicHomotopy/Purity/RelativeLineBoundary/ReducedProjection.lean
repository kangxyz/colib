/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineBoundary
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineBoundary.ConeComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReducedTorusObject

/-!
# The original reduced Laurent projection on open pairs

The ambient quotient commutes with the actual reduced Laurent projection.
The two augmented projective models are compared on the same right inclusion
of the graph cone. The resulting square preserves the forward projection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

private theorem map_ambient_quotient {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B V W : C} {X : D}
    (f : A ⟶ B) (g : B ⟶ W) (a : A ⟶ V) (q : V ⟶ W) (e : F.obj V ≅ X)
    (h : f ≫ g = a ≫ q) :
    F.map f ≫ F.map g = (F.map a ≫ e.hom) ≫ (e.inv ≫ F.map q) := by
  rw [← F.map_comp, h, F.map_comp, Category.assoc, e.hom_inv_id_assoc]

private theorem compare_augmentation {C D V : Type*} [Category* C] [Category* D] [Category* V]
    {P : C ⥤ V} (F : C ⥤ D) (T : D ⥤ V) (e : P ≅ F ⋙ T)
    {A B : C} {X Y : D} (f : A ⟶ B) (g : F.obj B ⟶ Y)
    (a : F.obj A ⟶ X) (q : X ⟶ Y) (h : F.map f ≫ g = a ≫ q) :
    P.map f ≫ e.hom.app B ≫ T.map g = (e.hom.app A ≫ T.map a) ≫ T.map q := by
  have hn : P.map f ≫ e.hom.app B = e.hom.app A ≫ T.map (F.map f) :=
    e.hom.naturality f
  rw [← Category.assoc, hn, Category.assoc, ← T.map_comp, h, T.map_comp, Category.assoc]

private theorem cancel_comparisons {C : Type*} [Category* C] {A B X Y : C}
    (e : A ≅ B) (d : B ≅ X) (f : A ⟶ Y) :
    (e.hom ≫ d.hom) ≫ d.inv ≫ e.inv ≫ f = f := by
  simp only [Category.assoc, d.hom_inv_id_assoc, e.hom_inv_id_assoc]

private theorem commute_reduced_quotient {C : Type*} [Category* C]
    {A₀ A₁ B₀ B₁ X₀ X₁ Y₀ Y₁ : C}
    (u : A₀ ⟶ A₁) (v : B₀ ⟶ B₁) (e₀ : A₀ ≅ X₀) (e₁ : A₁ ≅ X₁)
    (b₀ : B₀ ≅ Y₀) (b₁ : B₁ ≅ Y₁) (p₀ : A₀ ⟶ B₀) (p₁ : A₁ ⟶ B₁)
    (q₀ : X₀ ⟶ X₁) (q₁ : Y₀ ⟶ Y₁) (r₀ : X₀ ⟶ Y₀) (r₁ : X₁ ⟶ Y₁)
    (hu : u ≫ e₁.hom = e₀.hom ≫ q₀) (hv : v ≫ b₁.hom = b₀.hom ≫ q₁)
    (hp : u ≫ p₁ = p₀ ≫ v) (hr₀ : e₀.hom ≫ r₀ = p₀ ≫ b₀.hom)
    (hr₁ : r₁ = e₁.inv ≫ p₁ ≫ b₁.hom) :
    q₀ ≫ r₁ = r₀ ≫ q₁ := by
  have he : q₀ ≫ e₁.inv = e₀.inv ≫ u := by
    have h := congrArg (fun f => e₀.inv ≫ f ≫ e₁.inv) hu.symm
    simpa only [Category.assoc, e₀.inv_hom_id_assoc, e₁.hom_inv_id, Category.comp_id] using h
  calc
    _ = (q₀ ≫ e₁.inv) ≫ p₁ ≫ b₁.hom := by rw [hr₁, Category.assoc]
    _ = e₀.inv ≫ (u ≫ p₁) ≫ b₁.hom := by rw [he, Category.assoc, Category.assoc]
    _ = e₀.inv ≫ p₀ ≫ (v ≫ b₁.hom) := by simp only [hp, Category.assoc]
    _ = e₀.inv ≫ (p₀ ≫ b₀.hom) ≫ q₁ := by rw [hv, Category.assoc]
    _ = _ := by
      rw [← hr₀, Category.assoc, ← Category.assoc e₀.inv, e₀.inv_hom_id, Category.id_comp]

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "NST(" K ")" => LargeSheaves K
local notation "G(" K ")" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of K))
local notation "A(" K ")" => nisnevichSheafify K
local notation "a(" K ")" => derivedNisnevichSheafification K
local notation "M(" K ")" => effectiveReflection K
local notation "T(" K ")" => effectiveReducedTorusTensorFunctor K
local notation "Q(" K ")" => singularEffectiveMotiveFunctor K
local notation "E(" K ")" => effectiveSmoothMotive K
local notation "S(" K ")" => singleTransferSheafMinus K
local notation "d(" K ")" => projectiveReducedTorusTensorQuotient K
local notation "e(" K ")" => smoothTransferRepresentableEffectiveIso K

/-- The transfer-sheaf abelian structure for the reduced Laurent projection. -/
local instance instAbelianReducedLaurentProjection : Abelian (NST(k)) :=
  SheafWithTransfers.abelian k

private def ambientLaurentMotiveIso (X : Sm(k)) :
    ((projectiveTorusTensorToDerivedMinus k ⋙ M(k)).obj
      (singleTransferRepresentable k (Cor.mk X))) ≅
      (E(k)).obj (torusCylinder.obj X) :=
  (M(k)).mapIso (projectiveAmbientLaurentIso k X) ≪≫ (e(k)).app (torusCylinder.obj X)

private def ambientReducedLaurentMotiveIso (X : Sm(k)) :
    (projectiveEffectiveTorus k).obj (singleTransferRepresentable k (Cor.mk X)) ≅
      (T(k)).obj ((E(k)).obj X) :=
  (projectiveEffectiveTorusNatIso k).app (singleTransferRepresentable k (Cor.mk X)) ≪≫
    (T(k)).mapIso (singleEffectiveReflectionIso k ((representableLarge k).obj (Cor.mk X)))

set_option maxHeartbeats 850000 in
-- Align the two original degree-zero reflection comparisons.
omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
private theorem projectiveAmbientSingleSheafIso_reflect (X : Sm(k)) :
    (M(k)).map (projectiveAmbientSingleSheafIso k X).hom ≫ ((e(k)).app X).hom =
      (singleEffectiveReflectionIso k ((representableLarge k).obj (Cor.mk X))).hom := by
  let P := (representableLarge k).obj (Cor.mk X)
  let a₀ := projectiveAmbientSingleSheafIso k X
  let F := M(k)
  let s := singleEffectiveReflectionIso k P
  let V := DerivedCategory.Minus.ι (C := NST(k))
  let V₀ := Functor.FullyFaithful.ofFullyFaithful V
  let Qs := DerivedCategory.Q (C := NST(k))
  let d := (A(k)).mapDerivedCategoryFactors.app ((projectiveSmoothSingle k).obj X) ≪≫
    Qs.mapIso (sheafifiedPairEndpoints k X)
  let a₁ : (a(k)).obj (singleTransferRepresentable k (Cor.mk X)) ≅
      (S(k)).obj ((smoothTransferRepresentable k).obj X) := V₀.preimageIso d
  have ha : a₁.hom = a₀.hom := by
    apply V.map_injective
    have hm := V₀.map_preimage
      (X := (a(k)).obj (singleTransferRepresentable k (Cor.mk X)))
      (Y := (S(k)).obj ((smoothTransferRepresentable k).obj X)) d.hom
    exact hm.trans (projectiveAmbientSingleSheafIso_hom_hom k X).symm
  have h : ((e(k)).app X).hom = F.map a₁.inv ≫ s.hom := by
    change (singleSheafReflectionIso k P).hom = _
    unfold singleSheafReflectionIso
    rfl
  rw [h, ← ha, ← Category.assoc, ← F.map_comp, a₁.hom_inv_id, F.map_id, Category.id_comp]

set_option maxHeartbeats 900000 in
-- The positive coefficient quotient is the original Laurent endpoint map followed by quotient.
omit [PerfectField k] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})] in
private theorem projectiveAmbientLaurentIso_cancel (X : Sm(k)) :
    (d(k)).app (singleTransferRepresentable k (Cor.mk X)) ≫
        (projectiveReducedTorusRepresentableSingleIso k (Cor.mk X)).hom =
      (projectiveAmbientLaurentIso k X).hom ≫
        (S(k)).map ((A(k)).map (toTorusCancellationCoefficients k (Cor.mk X))) := by
  apply ObjectProperty.hom_ext
  let Y := Cor.mk X
  let A := A(k)
  let F := parameterTensorFunctor G(k) ⋙ A
  let s := CochainComplex.singleFunctor (NST(k)) 0
  let H := DerivedCategory.Q (C := NST(k))
  let P := (representableLarge k).obj Y
  let g := (parameterTensorRepresentableIso G(k) Y).hom
  let q := toTorusCancellationCoefficients k Y
  let b := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) (0 : ℤ)).hom.app P
  let l := (projectiveTorusRepresentableSingleModelIso k Y).hom
  have h : torusTensorRepresentableSingleQuotient k Y =
      (laurentCochainEndpointIso k X).hom ≫ s.map (A.map q) := by
    change b ≫ s.map (A.map (g ≫ q)) = (b ≫ s.map (A.map g)) ≫ s.map (A.map q)
    rw [A.map_comp, s.map_comp, Category.assoc]
  have he : (projectiveAmbientLaurentIso k X).hom.hom =
      l ≫ H.map (laurentCochainEndpointIso k X).hom := projectiveAmbientLaurentIso_hom_hom k X
  change _ = (projectiveAmbientLaurentIso k X).hom.hom ≫ H.map (s.map (A.map q))
  rw [he]
  calc
    _ = l ≫ H.map (torusTensorRepresentableSingleQuotient k Y) :=
      projectiveReducedTorusRepresentableSingleIso_quotient k Y
    _ = l ≫ H.map ((laurentCochainEndpointIso k X).hom ≫ s.map (A.map q)) :=
      congrArg (fun m => l ≫ H.map m) h
    _ = _ := by rw [H.map_comp, Category.assoc]

set_option maxHeartbeats 950000 in
-- Read the original representable projection under the same comparison as for pairs.
private theorem ambientLaurentMotiveIso_reducedProjection (X : Sm(k)) :
    (ambientLaurentMotiveIso k X).hom ≫
        (effectiveReducedTorusTensorRepresentableRetract k (Cor.mk X)).r =
      (M(k)).map ((d(k)).app (singleTransferRepresentable k (Cor.mk X))) ≫
        (ambientReducedLaurentMotiveIso k X).hom := by
  let Y := Cor.mk X
  let q := toTorusCancellationCoefficients k Y
  let F := M(k)
  let T := T(k)
  let K := singleTransferRepresentable k Y
  let a₀ := projectiveAmbientLaurentIso k X
  let a := ambientLaurentMotiveIso k X
  let b := ambientReducedLaurentMotiveIso k X
  let r := (effectiveReducedTorusTensorRepresentableRetract k Y).r
  let s := (e(k)).app (torusCylinder.obj X)
  let σ := projectiveReducedTorusRepresentableSingleIso k Y
  let d := effectiveReducedTorusTensorRepresentableIso k Y
  let h := (projectiveEffectiveTorusNatIso k).app K
  let v := singleEffectiveReflectionIso k ((representableLarge k).obj Y)
  let z := singleSheafReflectionIso k (torusCancellationCoefficients k Y)
  let g := (S(k)).map ((A(k)).map q)
  let p := (d(k)).app K
  have hd : d.hom = T.map v.inv ≫ h.inv ≫ F.map σ.hom ≫ z.hom :=
    effectiveReducedTorusTensorRepresentableIso_hom k Y
  have hbd : b.hom ≫ d.hom = F.map σ.hom ≫ z.hom := by
    let tv := T.mapIso v
    change (h.hom ≫ tv.hom) ≫ d.hom = _
    rw [hd]
    exact cancel_comparisons h tv (F.map σ.hom ≫ z.hom)
  have hr : r ≫ d.hom = (Q(k)).map q := by
    change ((Q(k)).map q ≫ d.inv) ≫ d.hom = _
    rw [Category.assoc, d.inv_hom_id, Category.comp_id]
  have hnat : F.map g ≫ z.hom = s.hom ≫ (Q(k)).map q :=
    singleSheafReflectionIso_naturality k q
  have hp : p ≫ σ.hom = a₀.hom ≫ g := projectiveAmbientLaurentIso_cancel k X
  apply (cancel_mono d.hom).mp
  change (a.hom ≫ r) ≫ d.hom = (F.map p ≫ b.hom) ≫ d.hom
  calc
    _ = F.map a₀.hom ≫ s.hom ≫ (Q(k)).map q := by
      rw [Category.assoc, hr]
      exact Category.assoc _ _ _
    _ = F.map a₀.hom ≫ F.map g ≫ z.hom := congrArg (F.map a₀.hom ≫ ·) hnat.symm
    _ = F.map p ≫ F.map σ.hom ≫ z.hom := by
      rw [← F.map_comp_assoc, ← hp, F.map_comp, Category.assoc]
    _ = _ := by rw [Category.assoc, hbd]

variable {U X : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ X)
variable [IsOpenImmersion j.left] [IsOpenImmersion (torusCylinder.map j).left]

set_option Elab.async false in
set_option maxHeartbeats 2200000 in
-- The absolute Laurent square comes from the original derived augmentation square.
omit [HasDerivedCategory AddCommGrpCat.{u + 1}] [IsOpenImmersion j.left] in
private theorem ambientLaurentMotiveIso_pair :
    ((projectiveTorusTensorToDerivedMinus k ⋙ M(k)).map
        (projectivePairAmbientMap k (Arrow.mk j))) ≫
        ((M(k)).mapIso (projectiveLaurentPairComparison k j)).hom =
      (ambientLaurentMotiveIso k X).hom ≫
        effectivePairMotiveQuotient k (torusCylinder.map j) := by
  let F := M(k)
  let t := (projectiveTorusTensorToDerivedMinus k).map (projectivePairAmbientMap k (Arrow.mk j))
  let p := (projectiveLaurentPairComparison k j).hom
  let a := (projectiveAmbientLaurentIso k X).hom
  let q := projectiveAmbientLaurentQuotient k j
  let e := (e(k)).app (torusCylinder.obj X)
  have h : t ≫ p = a ≫ q := projectiveLaurentPairComparison_ambient k j
  exact map_ambient_quotient F t p a q e h

set_option Elab.async false in
set_option maxHeartbeats 2200000 in
-- Naturality of the reduced comparison on the original inclusion of projective complexes.
omit [IsOpenImmersion (torusCylinder.map j).left] in
private theorem ambientReducedLaurentMotiveIso_pair :
    (projectiveEffectiveTorus k).map (projectivePairAmbientMap k (Arrow.mk j)) ≫
        (projectiveReducedLaurentPairComparison k j).hom =
      (ambientReducedLaurentMotiveIso k X).hom ≫ (T(k)).map (effectivePairMotiveQuotient k j) := by
  let a := projectivePairAmbientMap k (Arrow.mk j)
  let c := projectiveEffectiveTorusNatIso k
  let T := T(k)
  let F := M(k)
  let b := projectivePairDerivedAugmentation k (Arrow.mk j)
  let p := (S(k)).map ((transferPairProjection k).app (Arrow.mk j))
  let s := projectiveAmbientSingleSheafIso k X
  let v := singleEffectiveReflectionIso k ((representableLarge k).obj (Cor.mk X))
  let e := (e(k)).app X
  let q := effectivePairMotiveQuotient k j
  have hs : (a(k)).map a ≫ b = s.hom ≫ p := projectivePairDerivedAugmentation_ambient k _
  have he : F.map s.hom ≫ e.hom = v.hom := projectiveAmbientSingleSheafIso_reflect k X
  have hv : F.map ((a(k)).map a) ≫ F.map b = v.hom ≫ q :=
    (map_ambient_quotient F ((a(k)).map a) b s.hom p e hs).trans
      (congrArg (· ≫ q) he)
  have h := compare_augmentation (a(k) ⋙ F) T c a (F.map b) v.hom q hv
  have hc : (projectiveReducedLaurentPairComparison k j).hom =
      c.hom.app ((projectivePairDerived k).obj (Arrow.mk j)) ≫ T.map (F.map b) :=
    projectiveReducedLaurentPairComparison_hom k j
  exact (congrArg ((projectiveEffectiveTorus k).map a ≫ ·) hc).trans h

set_option maxHeartbeats 1250000 in
-- Transport naturality of the actual reduced quotient through both augmentation squares.
/-- The ambient quotient of the Laurent pair commutes with the original
reduced projection, using the original ambient quotient on the base. -/
theorem effectivePairMotiveQuotient_comp_reducedLaurentProjection :
    effectivePairMotiveQuotient k (torusCylinder.map j) ≫ (effectiveRelativeLaurentRetract k j).r =
      (effectiveReducedTorusTensorRepresentableRetract k (Cor.mk X)).r ≫
        (T(k)).map (effectivePairMotiveQuotient k j) := by
  let F := M(k)
  let a := projectivePairAmbientMap k (Arrow.mk j)
  let u := (projectiveTorusTensorToDerivedMinus k ⋙ F).map a
  let v := (projectiveEffectiveTorus k).map a
  let e₀ := ambientLaurentMotiveIso k X
  let e₁ := F.mapIso (projectiveLaurentPairComparison k j)
  let b₀ := ambientReducedLaurentMotiveIso k X
  let b₁ := projectiveReducedLaurentPairComparison k j
  let p₀ := F.map ((d(k)).app (singleTransferRepresentable k (Cor.mk X)))
  let p₁ := F.map ((d(k)).app ((projectivePairDerived k).obj (Arrow.mk j)))
  let q₀ := effectivePairMotiveQuotient k (torusCylinder.map j)
  let q₁ := (T(k)).map (effectivePairMotiveQuotient k j)
  let r₀ := (effectiveReducedTorusTensorRepresentableRetract k (Cor.mk X)).r
  let r₁ := (effectiveRelativeLaurentRetract k j).r
  have hu : u ≫ e₁.hom = e₀.hom ≫ q₀ := ambientLaurentMotiveIso_pair k j
  have hv : v ≫ b₁.hom = b₀.hom ≫ q₁ := ambientReducedLaurentMotiveIso_pair k j
  have hp : u ≫ p₁ = p₀ ≫ v :=
    (F.map_comp _ _).symm.trans ((F.congr_map ((d(k)).naturality a)).trans (F.map_comp _ _))
  have hr₀ : e₀.hom ≫ r₀ = p₀ ≫ b₀.hom := ambientLaurentMotiveIso_reducedProjection k X
  have hr₁ : r₁ = e₁.inv ≫ p₁ ≫ b₁.hom := effectiveRelativeLaurentRetract_r k j
  exact commute_reduced_quotient u v e₀ e₁ b₀ b₁ p₀ p₁ q₀ q₁ r₀ r₁ hu hv hp hr₀ hr₁

end AlgebraicGeometry.MotivicHomotopy
