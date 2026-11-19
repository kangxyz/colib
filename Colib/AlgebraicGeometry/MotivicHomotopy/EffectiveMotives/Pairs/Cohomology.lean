/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Cohomology.Absolute
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Cohomology.Transfer
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Triangle
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Ordinary Nisnevich cohomology of effective open pairs

Reflection transposes maps from the actual transfer quotient to derived maps.
The ordinary comparison identifies these maps with the relative Ext groups.
The connecting morphism is the original triangle morphism, with the degree
sign of the ordinary signed boundary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme Opposite Stacks.Cohomology.FreeYonedaUnivLE

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Nis" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))
local notation "NST" => LargeSheaves k
local notation "E" => EffectiveMotivesMinus k
local notation "S" => singleTransferSheafMinus k
local notation "D" => DerivedCategory.singleFunctor NST 0
local notation "M" => effectiveSmoothMotive k
local notation "L" => effectiveReflection k
local notation "I" => effectiveMotivesMinusInclusion k
local notation "J" => effectiveMotivesMinusToDerived k
set_option quotPrecheck false in
local notation "V" => DerivedCategory.Minus.ι (C := NST)
local notation "a" => effectiveReflectionAdjunction k
local notation "e" => smoothTransferRepresentableEffectiveIso k
local notation "R" => smoothTransferRepresentable k

/-- Use the canonical additive sheafification for the ordinary pair comparisons. -/
local instance pairHasSheafify : HasSheafify Nis AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1} Nis

/-- Use the same abelian transfer category for Ext and the effective reflection. -/
local instance pairCohomologyAbelian : Abelian NST := SheafWithTransfers.abelian k

/-- Use the Ext groups of the chosen transfer derived category. -/
local instance pairCohomologyHasExt : HasExt.{w'} NST := hasExt_of_hasDerivedCategory NST

private def reflectedShiftedHomEquiv (B : DerivedCategory.Minus NST) (K : E) (n : ℤ) :
    ShiftedHom ((L).obj B) K n ≃+ ShiftedHom ((V).obj B) ((J).obj K) n := by
  let v := Functor.FullyFaithful.ofFullyFaithful V
  refine AddEquiv.mk' (((a).homEquiv B (K⟦n⟧)).trans
    (v.homEquiv.trans (((J).commShiftIso n).app K).homToEquiv)) ?_
  intro x y
  change (V).map ((a).homEquiv B (K⟦n⟧) (x + y)) ≫ ((J).commShiftIso n).hom.app K =
    ((V).map ((a).homEquiv B (K⟦n⟧) x) ≫ ((J).commShiftIso n).hom.app K) +
      ((V).map ((a).homEquiv B (K⟦n⟧) y) ≫ ((J).commShiftIso n).hom.app K)
  simp only [Adjunction.homEquiv_unit, Preadditive.comp_add, Functor.map_add, Preadditive.add_comp]

private theorem reflectedShiftedHomEquiv_apply_unit {B : DerivedCategory.Minus NST}
    {K : E} {n : ℤ} (x : ShiftedHom ((L).obj B) K n) :
    reflectedShiftedHomEquiv k B K n x = (V).map ((a).unit.app B) ≫ x.map (J) := by
  change (V).map ((a).homEquiv B (K⟦n⟧) x) ≫ ((J).commShiftIso n).hom.app K = _
  simp only [ShiftedHom.map, Adjunction.homEquiv_unit, Functor.comp_map,
    Functor.map_comp, Category.assoc]

private theorem reflectedShiftedHomEquiv_apply {B : DerivedCategory.Minus NST} {K : E} {n : ℤ}
    (x : ShiftedHom ((L).obj B) K n) :
    reflectedShiftedHomEquiv k B K n x = ShiftedHom.map ((a).unit.app B ≫ x.map (I)) (V) := by
  rw [reflectedShiftedHomEquiv_apply_unit]
  change (V).map ((a).unit.app B) ≫ x.map ((I) ⋙ (V)) = _
  simp only [ShiftedHom.map, Functor.commShiftIso_comp_hom_app, Functor.comp_map,
    Functor.map_comp, Category.assoc]

private theorem reflectedShiftedHomEquiv_comp_left {A B : DerivedCategory.Minus NST}
    {K : E} {p q t : ℤ} (r : ShiftedHom A B p) (x : ShiftedHom ((L).obj B) K q)
    (h : q + p = t) :
    reflectedShiftedHomEquiv k A K t ((r.map L).comp x h) =
      (r.map V).comp (reflectedShiftedHomEquiv k B K q x) h := by
  rw [reflectedShiftedHomEquiv_apply, reflectedShiftedHomEquiv_apply, ← ShiftedHom.map_comp]
  apply congrArg (fun z : ShiftedHom A ((I).obj K) t => z.map V)
  have hu := ShiftedHom.map_naturality r (a).unit
  simp only [ShiftedHom.id_map, ShiftedHom.comp_map, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀] at hu
  rw [ShiftedHom.map_comp]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc, ← reassoc_of% hu]

private theorem reflectedShiftedHomEquiv_precomp {A B : DerivedCategory.Minus NST}
    {K : E} {n : ℤ} (r : A ⟶ B) (x : ShiftedHom ((L).obj B) K n) :
    reflectedShiftedHomEquiv k A K n ((L).map r ≫ x) =
      (V).map r ≫ reflectedShiftedHomEquiv k B K n x := by
  simpa only [ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp] using
    reflectedShiftedHomEquiv_comp_left k (ShiftedHom.mk₀ (0 : ℤ) rfl r) x (add_zero n)

private theorem reflectedShiftedHomEquiv_postcomp {A : DerivedCategory.Minus NST}
    {K K' : E} {n : ℤ} (f : K ⟶ K') (x : ShiftedHom ((L).obj A) K n) :
    reflectedShiftedHomEquiv k A K' n (x ≫ f⟦n⟧') =
      reflectedShiftedHomEquiv k A K n x ≫ ((J).map f)⟦n⟧' := by
  rw [reflectedShiftedHomEquiv_apply_unit, reflectedShiftedHomEquiv_apply_unit]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality]

private def effectiveTransferSheafExtEquiv (A F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ) :
    ((effectiveTransferSheaf k).obj A ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) ≃+
      Ext.{w'} A F n :=
  (reflectedShiftedHomEquiv k ((S).obj A) (effectiveHICoefficient k F hF) n).trans
    Ext.homAddEquiv.symm

private theorem effectiveTransferSheafExtEquiv_hom (A F : NST) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (x : (effectiveTransferSheaf k).obj A ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    (effectiveTransferSheafExtEquiv k A F hF n x).hom =
      reflectedShiftedHomEquiv k ((S).obj A) (effectiveHICoefficient k F hF) n x :=
  Ext.homAddEquiv.apply_symm_apply _

private theorem effectiveTransferSheafExtEquiv_precomp {A B : NST} (r : A ⟶ B)
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : (effectiveTransferSheaf k).obj B ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveTransferSheafExtEquiv k A F hF n ((effectiveTransferSheaf k).map r ≫ x) =
      (Ext.mk₀ r).comp (effectiveTransferSheafExtEquiv k B F hF n x) (zero_add n) := by
  apply Ext.ext
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    effectiveTransferSheafExtEquiv_hom, effectiveTransferSheafExtEquiv_hom]
  exact reflectedShiftedHomEquiv_precomp k ((S).map r) x

set_option maxHeartbeats 600000 in
-- Identify the two presentations of the shifted coefficient map.
private theorem effectiveTransferSheafExtEquiv_postcomp (A : NST) {F G : NST}
    (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant) (f : F ⟶ G) (n : ℕ)
    (x : (effectiveTransferSheaf k).obj A ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveTransferSheafExtEquiv k A G hG n
      (x ≫ (effectiveHICoefficientMap k hF hG f)⟦(n : ℤ)⟧') =
      (effectiveTransferSheafExtEquiv k A F hF n x).comp (Ext.mk₀ f) (add_zero n) := by
  apply Ext.ext
  let b := effectiveHICoefficientMap k hF hG f
  let y := effectiveTransferSheafExtEquiv k A F hF n x
  let B := shiftFunctor (DerivedCategory NST) (n : ℤ)
  let r := B.map ((J).map b)
  have hStart := effectiveTransferSheafExtEquiv_hom k A G hG n (x ≫ b⟦(n : ℤ)⟧')
  have hNat := reflectedShiftedHomEquiv_postcomp k b x
  have hY := effectiveTransferSheafExtEquiv_hom k A F hF n x
  have hMiddle := congrArg (· ≫ r) hY.symm
  have hShift := B.congr_map (effectiveHICoefficientMap_toDerived k hF hG f)
  have hMap := congrArg (y.hom ≫ ·) hShift
  have hExt := Ext.hom_comp_singleFunctor_map_shift y f
  have hFinal := hStart.trans (hNat.trans (hMiddle.trans (hMap.trans hExt)))
  exact hFinal

set_option maxHeartbeats 850000 in
-- Compare the native single representative used in each smooth Ext realization.
private theorem effectiveSmoothExtEquiv_apply (X : SmoothSite (Spec (.of k)))
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : (M).obj X ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveSmoothExtEquiv k X F hF n x =
      effectiveTransferSheafExtEquiv k ((R).obj X) F hF n (((e).app X).hom ≫ x) := by
  apply Ext.ext
  let K := effectiveHICoefficient k F hF
  let A := (S).obj ((R).obj X)
  let d := (DerivedCategory.singleFunctorIsoCompQ NST 0).app ((R).obj X)
  let b := ((J).commShiftIso (n : ℤ)).hom.app K
  let s := ((e).app X).hom ≫ x
  let q := (V).map ((a).homEquiv A (K⟦(n : ℤ)⟧) s)
  have hStart := effectiveSmoothExtEquiv_hom k X F hF n x
  have hEnd := effectiveTransferSheafExtEquiv_hom k ((R).obj X) F hF n s
  have h₀ : effectiveMotiveDerivedHomEquiv k (Cor.mk X) (K⟦(n : ℤ)⟧) x =
      d.hom ≫ q := rfl
  have h₁ : reflectedShiftedHomEquiv k A K n s = q ≫ b := rfl
  have hd : d.hom = 𝟙 _ := rfl
  have hId := (congrArg (· ≫ q) hd).trans (Category.id_comp q)
  have hShift := congrArg (· ≫ b) (h₀.trans hId)
  have hFinal := (hStart.trans hShift).trans (hEnd.trans h₁).symm
  exact hFinal

variable {U X : SmoothSite (Spec (.of k))}
variable (j : U ⟶ X) [IsOpenImmersion j.left]

/-- Ordinary relative cohomology is represented by the actual effective pair motive. -/
@[no_expose]
def effectivePairCohomologyEquiv (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ) :
    (effectivePairMotive k j ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) ≃+
      relativeH.{u + 1, u + 1} Nis j ((toSheaf k).obj F) n :=
  (effectiveTransferSheafExtEquiv k (transferPairCokernel k j) F hF n).trans
    (transferPairExtEquiv k j F n)

private theorem effectivePairCohomologyEquiv_apply (F : NST) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (x : effectivePairMotive k j ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectivePairCohomologyEquiv k j F hF n x =
      transferPairExtComparison k j F n
        (effectiveTransferSheafExtEquiv k (transferPairCokernel k j) F hF n x) := rfl

set_option maxHeartbeats 800000 in
-- Compose the native quotient action with the ordinary relative Ext action.
/-- The relative comparison acts by the original restriction on pairs. -/
theorem effectivePairCohomologyEquiv_precomp {U' X' : SmoothSite (Spec (.of k))} {j' : U' ⟶ X'}
    [IsOpenImmersion j'.left] (f : Arrow.mk j ⟶ Arrow.mk j')
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : effectivePairMotive k j' ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectivePairCohomologyEquiv k j F hF n ((effectivePairMotiveFunctor k).map f ≫ x) =
      ((relativeCohomologyFunctor.{u + 1, u + 1} Nis n).obj ((toSheaf k).obj F)).map f.op
        (effectivePairCohomologyEquiv k j' F hF n x) := by
  let r := (transferPairCokernelFunctor k).map f
  let z := effectiveTransferSheafExtEquiv k (transferPairCokernel k j') F hF n x
  let p := ((relativeCohomologyFunctor.{u + 1, u + 1} Nis n).obj ((toSheaf k).obj F)).map f.op
  have hStart := effectivePairCohomologyEquiv_apply k j F hF n
    ((effectiveTransferSheaf k).map r ≫ x)
  have hReflect := effectiveTransferSheafExtEquiv_precomp k r F hF n x
  have hMap := congrArg (fun t => transferPairExtComparison k j F n t) hReflect
  have hOrd := transferPairExtComparison_precomp k j f F n z
  have hEnd := effectivePairCohomologyEquiv_apply k j' F hF n x
  have hRes := congrArg (fun t => p t) hEnd.symm
  have hFinal := hStart.trans (hMap.trans (hOrd.symm.trans hRes))
  exact hFinal

/-- The relative comparison acts by the original coefficient map. -/
theorem effectivePairCohomologyEquiv_postcomp {F G : NST}
    (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant) (f : F ⟶ G) (n : ℕ)
    (x : effectivePairMotive k j ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectivePairCohomologyEquiv k j G hG n (x ≫ (effectiveHICoefficientMap k hF hG f)⟦(n : ℤ)⟧') =
      relativeCoefficientMap.{u + 1, u + 1} Nis j ((toSheaf k).map f) n
        (effectivePairCohomologyEquiv k j F hF n x) := by
  change transferPairExtComparison k j G n (effectiveTransferSheafExtEquiv k _ G hG n
      (x ≫ (effectiveHICoefficientMap k hF hG f)⟦(n : ℤ)⟧')) = _
  rw [effectiveTransferSheafExtEquiv_postcomp]
  exact (transferPairExtComparison_postcomp k j f n _).symm

private theorem iso_precomp_inverse_composition {C : Type*} [Category C]
    {A B D₁ D₂ : C} (e₀ : A ≅ B) (f : A ⟶ D₁) (g : D₁ ⟶ D₂) :
    e₀.hom ≫ (e₀.inv ≫ f) ≫ g = f ≫ g :=
  (Category.assoc e₀.hom (e₀.inv ≫ f) g).symm.trans
    (congrArg (· ≫ g) (Iso.hom_inv_id_assoc e₀ f))

set_option maxHeartbeats 850000 in
-- Identify the literal ambient and relative transfer Ext sources.
omit [IsOpenImmersion j.left] in
private theorem effectiveSmoothExtEquiv_pairQuotient (F : NST) (hF : F.obj.IsA1Invariant)
    (n : ℕ) (x : effectivePairMotive k j ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveSmoothExtEquiv k X F hF n (effectivePairMotiveQuotient k j ≫ x) =
      (Ext.mk₀ ((transferPairProjection k).app (Arrow.mk j))).comp
        (effectiveTransferSheafExtEquiv k (transferPairCokernel k j) F hF n x)
        (zero_add n) := by
  let iX := (e).app X
  let r : (R).obj X ⟶ transferPairCokernel k j := (transferPairProjection k).app (Arrow.mk j)
  let q := (effectiveTransferSheaf k).map r
  let y := (iX.inv ≫ q) ≫ x
  let A := effectiveTransferSheafExtEquiv k ((R).obj X) F hF n
  have hStart := effectiveSmoothExtEquiv_apply k X F hF n y
  have hGraph := congrArg (fun t => A t) (iso_precomp_inverse_composition iX q x)
  have hExt := effectiveTransferSheafExtEquiv_precomp k r F hF n x
  have hFinal := hStart.trans (hGraph.trans hExt)
  exact hFinal

set_option maxHeartbeats 750000 in
-- Match the ordinary ambient group to the composite with the original Ext realization.
/-- The motivic quotient realizes forgetting the support condition. -/
theorem effectivePairCohomologyEquiv_forget (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : effectivePairMotive k j ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveSmoothCohomologyEquiv k X F hF n (effectivePairMotiveQuotient k j ≫ x) =
      relativeForget.{u + 1, u + 1} Nis j ((toSheaf k).obj F) n
        (effectivePairCohomologyEquiv k j F hF n x) := by
  let y := effectivePairMotiveQuotient k j ≫ x
  let C := transferExtComparison.{w', u + 1, u} k X F n
  let z := effectiveTransferSheafExtEquiv k (transferPairCokernel k j) F hF n x
  have hStart : effectiveSmoothCohomologyEquiv k X F hF n y =
      C (effectiveSmoothExtEquiv k X F hF n y) := rfl
  have hQuot := effectiveSmoothExtEquiv_pairQuotient k j F hF n x
  have hExt := congrArg (fun t => C t) hQuot
  have hOrd := transferPairExtComparison_forget k j F n z
  have hEnd := effectivePairCohomologyEquiv_apply k j F hF n x
  have hForget := congrArg (fun t => relativeForget.{u + 1, u + 1} Nis j ((toSheaf k).obj F) n t)
    hEnd.symm
  have hFinal := hStart.trans (hExt.trans (hOrd.symm.trans hForget))
  exact hFinal

/-- An open immersion gives a monomorphism in the original smooth site. -/
local instance cohomologyBoundaryOpenMono : Mono j :=
  (SmoothSite.forgetScheme _).mono_of_mono_map (IsOpenImmersion.mono j.left)

/-- The raw connecting map is postcomposition of the third triangle arrow with the shifted class. -/
abbrev effectivePairCohomologyConnecting (K : E) (n : ℤ) (x : (M).obj U ⟶ K⟦n⟧) :
    effectivePairMotive k j ⟶ K⟦n + 1⟧ :=
  ShiftedHom.comp (effectivePairTriangle k j).mor₃ x (show n + 1 = n + 1 from rfl)

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem singleTransferSheafTriangle_boundary_toDerived {Q : ShortComplex NST}
    (h : Q.ShortExact) : ShiftedHom.map (singleTransferSheafTriangle k h).mor₃ (V) = h.singleδ := by
  let b := ((V).commShiftIso (1 : ℤ)).app ((S).obj Q.X₁)
  let d := h.singleδ
  have hId := congrArg (d ≫ ·) b.inv_hom_id
  have hFinal := (Category.assoc d b.inv b.hom).trans (hId.trans (Category.comp_id d))
  exact hFinal

private theorem shiftedComp_precompose_plain {C : Type*} [Category C] [HasShift C ℤ]
    {A B B' C' : C} {p q t : ℤ} (d : ShiftedHom A B p) (f : B ⟶ B')
    (x : ShiftedHom B' C' q) (h : q + p = t) :
    d.comp (f ≫ x) h = (show ShiftedHom A B' p from d ≫ f⟦p⟧').comp x h := by
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]

set_option maxHeartbeats 1200000 in
-- Identify the native transfer boundary in both the effective and ordinary derived categories.
private theorem effectiveTransferSheafExtEquiv_connecting
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : (M).obj U ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectiveTransferSheafExtEquiv k _ F hF (n + 1)
        (effectivePairCohomologyConnecting k j (effectiveHICoefficient k F hF) n x) =
      (transferPairSequence_shortExact k j).extClass.comp (effectiveSmoothExtEquiv k U F hF n x)
        (Nat.add_comm 1 n) := by
  apply Ext.ext
  let K := effectiveHICoefficient k F hF
  let h := transferPairSequence_shortExact k j
  let A := transferPairCokernel k j
  let B := (R).obj U
  let d : ShiftedHom ((S).obj A) ((S).obj B) (1 : ℤ) := (singleTransferSheafTriangle k h).mor₃
  let f := ((e).app U).hom
  let y := f ≫ x
  let v := effectiveTransferSheafExtEquiv k B F hF n y
  let q := reflectedShiftedHomEquiv k ((S).obj B) K (n : ℤ) y
  let ξ : Ext.{w'} A B 1 := h.extClass
  let deg : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  let z := (d.map L).comp y deg
  have hPair := shiftedComp_precompose_plain (d.map L) f x deg
  let C := effectiveTransferSheafExtEquiv k A F hF (n + 1)
  have hStart := congrArg (fun t => (C t).hom) hPair.symm
  have hLift := effectiveTransferSheafExtEquiv_hom k A F hF (n + 1) z
  have hNat := reflectedShiftedHomEquiv_comp_left k d y deg
  have hd := singleTransferSheafTriangle_boundary_toDerived k h
  have hξ : ξ.hom = h.singleδ := h.extClass_hom
  have hDelta := congrArg (fun δ => δ.comp q deg) (hd.trans hξ.symm)
  have hv := effectiveTransferSheafExtEquiv_hom k B F hF n y
  have hVal := congrArg (fun b => ξ.hom.comp b deg) hv.symm
  have hProd := Ext.comp_hom ξ v (Nat.add_comm 1 n)
  have hSmooth := effectiveSmoothExtEquiv_apply k U F hF n x
  have hEnd := congrArg (fun t => (ξ.comp t (Nat.add_comm 1 n)).hom) hSmooth.symm
  have hLeft := hStart.trans (hLift.trans hNat)
  have hRight := hDelta.trans (hVal.trans (hProd.symm.trans hEnd))
  have hFinal := hLeft.trans hRight
  exact hFinal

/-- The raw effective triangle connecting map agrees with ordinary Yoneda precomposition. -/
theorem effectivePairCohomologyEquiv_connecting (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : (M).obj U ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectivePairCohomologyEquiv k j F hF (n + 1)
        (effectivePairCohomologyConnecting k j (effectiveHICoefficient k F hF) n x) =
      relativeConnecting.{u + 1, u + 1} Nis j ((toSheaf k).obj F) n
        (effectiveSmoothCohomologyEquiv k U F hF n x) := by
  let z := effectivePairCohomologyConnecting k j (effectiveHICoefficient k F hF) n x
  let y := effectiveSmoothExtEquiv k U F hF n x
  have hStart := effectivePairCohomologyEquiv_apply k j F hF (n + 1) z
  have hBoundary := effectiveTransferSheafExtEquiv_connecting k j F hF n x
  have hCompare := congrArg (fun t => transferPairExtComparison k j F (n + 1) t) hBoundary
  have hOrd := transferPairExtComparison_connecting k j F n y
  have hFinal := hStart.trans (hCompare.trans hOrd.symm)
  exact hFinal

/-- The signed ordinary boundary uses the degree-`n + 1` sign of the raw effective composite. -/
theorem effectivePairCohomologyEquiv_boundary (F : NST) (hF : F.obj.IsA1Invariant) (n : ℕ)
    (x : (M).obj U ⟶ (effectiveHICoefficient k F hF)⟦(n : ℤ)⟧) :
    effectivePairCohomologyEquiv k j F hF (n + 1)
        (Int.negOnePow (n + 1) •
          effectivePairCohomologyConnecting k j (effectiveHICoefficient k F hF) n x) =
      relativeBoundary.{u + 1, u + 1} Nis j ((toSheaf k).obj F) n
        (effectiveSmoothCohomologyEquiv k U F hF n x) := by
  simp only [relativeBoundary_apply, Units.smul_def, map_zsmul,
    effectivePairCohomologyEquiv_connecting]

end AlgebraicGeometry.MotivicHomotopy
