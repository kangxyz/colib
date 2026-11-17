/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleOrientationCompatibility

/-!
# Descent of the supported normal-bundle class

Each marked affine chart gives the normalized affine-space orientation.
Its equality on two frames comes from the universal determinant open.
Compatible local classes then give a unique class on the original pair.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private def transportCoverThomClass {O C : Type*} [Category* O] [Category* C]
    (F : O ⥤ C) {V W : O} {B T : C} (e : F.obj W ≅ B) (g : W ⟶ V)
    (τ : F.obj V ⟶ T) : B ⟶ T :=
  e.inv ≫ F.map g ≫ τ

private theorem transportCoverThomClass_restrict {O C : Type*} [Category* O] [Category* C]
    (F : O ⥤ C) {U V W : O} {B T : C} (e : F.obj W ≅ B) (g : W ⟶ V)
    (τ : F.obj V ⟶ T)
    (f : U ⟶ W) (a : U ⟶ V) (s : F.obj U ⟶ T) (ha : f ≫ g = a)
    (hs : F.map a ≫ τ = s) :
    F.map f ≫ e.hom ≫ transportCoverThomClass F e g τ = s := by
  unfold transportCoverThomClass
  rw [e.hom_inv_id_assoc, ← F.map_comp_assoc, ha, hs]

variable (k : Type u) [baseField : Field k]

local notation "Base" => Spec (CommRingCat.of k)
local notation "M" => effectiveSmoothMotive k

variable {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
  [closedImmersion : IsClosedImmersion i.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

local notation "E₀" => (Stacks.Conormal.conormalSheafDegreeOne i.left : Z.left.Modules)
local notation "p" => normalBundleProjection i hX hZ
local notation "z" => normalBundleZeroSection i hX hZ
set_option quotPrecheck false in
local notation "jₙ" => closedPairOpenInclusion (z).left

variable [perfectField : PerfectField k]
  [presheafDerived : HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [sheafDerived : HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [groupDerived : HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [nisnevichExt :
    HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The canonical abelian structure on sheaves with transfers. -/
local instance normalBundleOrientationDescentAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

local notation "Q" => relativeOpenRestrictionMotive k (p) jₙ
local notation "L" => Stabilization.iterate (effectiveLefschetzTwistFunctor k) (n - m)
set_option quotPrecheck false in
local notation "K" => (L).obj ((M).obj (base Base))

section Descent

variable {J : Type*} (V : J → Z.left.affineOpens) (ts : Finset J)

set_option maxHeartbeats 700000 in
-- Use the actual effective category for the original restriction triangles.
/-- The original relative Mayer–Vietoris maps determine the global
orientation from agreeing chart classes. -/
theorem existsUnique_normalBundleThomClass
    (b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(E₀, (V x).1))
    (hzero : ∀ U, Subsingleton (((Q).obj U)⟦(1 : ℤ)⟧ ⟶ K))
    (hcomp : ∀ x y, (Q).map (homOfLE (inf_le_left :
        (V x).1 ⊓ (V y).1 ≤ (V x).1)) ≫ normalBundleBasisThomClass k i hX hZ (V x) (b x) =
      (Q).map (homOfLE (inf_le_right :
        (V x).1 ⊓ (V y).1 ≤ (V y).1)) ≫ normalBundleBasisThomClass k i hX hZ (V y) (b y)) :
    ∃! τ : (Q).obj (ts.sup (fun x => (V x).1)) ⟶ K,
      ∀ x (hx : x ∈ ts), (Q).map (homOfLE (Finset.le_sup hx)) ≫ τ =
        normalBundleBasisThomClass k i hX hZ (V x) (b x) :=
  existsUnique_glue_finset (C := EffectiveMotivesMinus k) (P := Q) (A := K)
    (fun x => (V x).1) ts
    (relativeOpenRestrictionTriangle k (p) jₙ)
    ⟨fun f g => (isZero_relativeOpenRestrictionMotive_bot k (p) jₙ).eq_of_src f g⟩ hzero
    (fun x => normalBundleBasisThomClass k i hX hZ (V x) (b x)) hcomp

section WholeBase

attribute [local irreducible] normalBundleOfSmooth normalBundleProjection
  relativeOpenRestrictionPair effectivePairMotiveFunctor

set_option maxHeartbeats 1200000 in
-- Transport a witness of the finite-cover theorem together with its restrictions.
private theorem exists_normalBundleThomClassOfCharts
    (b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(E₀, (V x).1))
    (hc : ts.sup (fun x => (V x).1) = ⊤)
    (hzero : ∀ U, Subsingleton (((Q).obj U)⟦(1 : ℤ)⟧ ⟶ K))
    (hcomp : ∀ x y, (Q).map (homOfLE (inf_le_left :
        (V x).1 ⊓ (V y).1 ≤ (V x).1)) ≫ normalBundleBasisThomClass k i hX hZ (V x) (b x) =
      (Q).map (homOfLE (inf_le_right :
        (V x).1 ⊓ (V y).1 ≤ (V y).1)) ≫ normalBundleBasisThomClass k i hX hZ (V y) (b y)) :
    ∃ t : effectiveMotiveWithSupport k (z) ⟶ K,
      (∃ τ : (Q).obj (ts.sup (fun x => (V x).1)) ⟶ K,
        (∀ x (hx : x ∈ ts), (Q).map (homOfLE (Finset.le_sup hx)) ≫ τ =
          normalBundleBasisThomClass k i hX hZ (V x) (b x)) ∧
        t = (relativeOpenRestrictionTopIso k (p) jₙ).inv ≫ (Q).map (eqToHom hc.symm) ≫ τ) ∧
      ∀ x (_hx : x ∈ ts),
        (Q).map (homOfLE (le_top : (V x).1 ≤ ⊤)) ≫ (relativeOpenRestrictionTopIso k (p) jₙ).hom ≫
          t = normalBundleBasisThomClass k i hX hZ (V x) (b x) := by
  let F : Z.left.Opens ⥤ EffectiveMotivesMinus k := Q
  let e : F.obj ⊤ ≅ effectiveMotiveWithSupport k (z) :=
    relativeOpenRestrictionTopIso k (Y := Z) (V := normalBundleOfSmooth i) (p) jₙ
  let W := ts.sup (fun x => (V x).1)
  let g : (⊤ : Z.left.Opens) ⟶ W := eqToHom hc.symm
  obtain ⟨τ, hτ⟩ := (existsUnique_normalBundleThomClass k i hX hZ V ts b hzero hcomp).exists
  let t : effectiveMotiveWithSupport k (z) ⟶ K :=
    transportCoverThomClass F (V := W) (W := (⊤ : Z.left.Opens)) (T := K) e g τ
  refine ⟨t, ⟨τ, hτ, rfl⟩, ?_⟩
  intro x hx
  let f : (V x).1 ⟶ (⊤ : Z.left.Opens) := homOfLE le_top
  let a : (V x).1 ⟶ W := homOfLE (Finset.le_sup (f := fun y => (V y).1) hx)
  let s := normalBundleBasisThomClass k i hX hZ (V x) (b x)
  have hfg : f ≫ g = a := Subsingleton.elim _ _
  have hr : F.map a ≫ τ = s := hτ x hx
  exact transportCoverThomClass_restrict F (U := (V x).1) (V := W) (W := (⊤ : Z.left.Opens))
    e g τ f a s hfg hr

set_option maxHeartbeats 850000 in
-- Choose the compatible class with its whole-base transport formula.
/-- The compatible orientation lies on the original global supported motive. -/
@[no_expose]
def normalBundleThomClassOfCharts
    (b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(E₀, (V x).1))
    (hc : ts.sup (fun x => (V x).1) = ⊤)
    (hzero : ∀ U, Subsingleton (((Q).obj U)⟦(1 : ℤ)⟧ ⟶ K))
    (hcomp : ∀ x y, (Q).map (homOfLE (inf_le_left :
        (V x).1 ⊓ (V y).1 ≤ (V x).1)) ≫ normalBundleBasisThomClass k i hX hZ (V x) (b x) =
      (Q).map (homOfLE (inf_le_right :
        (V x).1 ⊓ (V y).1 ≤ (V y).1)) ≫ normalBundleBasisThomClass k i hX hZ (V y) (b y)) :
    effectiveMotiveWithSupport k (z) ⟶ K :=
  (exists_normalBundleThomClassOfCharts k i hX hZ V ts b hc hzero hcomp).choose

set_option maxHeartbeats 1000000 in
-- Uniqueness on the join identifies its chosen class with the transported witness.
/-- The global class is the transport of the unique class on the finite join of the charts. -/
theorem normalBundleThomClassOfCharts_eq_transport
    (b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(E₀, (V x).1))
    (hc : ts.sup (fun x => (V x).1) = ⊤)
    (hzero : ∀ U, Subsingleton (((Q).obj U)⟦(1 : ℤ)⟧ ⟶ K))
    (hcomp : ∀ x y, (Q).map (homOfLE (inf_le_left :
        (V x).1 ⊓ (V y).1 ≤ (V x).1)) ≫ normalBundleBasisThomClass k i hX hZ (V x) (b x) =
      (Q).map (homOfLE (inf_le_right :
        (V x).1 ⊓ (V y).1 ≤ (V y).1)) ≫ normalBundleBasisThomClass k i hX hZ (V y) (b y)) :
    normalBundleThomClassOfCharts k i hX hZ V ts b hc hzero hcomp =
      (relativeOpenRestrictionTopIso k (p) jₙ).inv ≫ (Q).map (eqToHom hc.symm) ≫
        (existsUnique_normalBundleThomClass k i hX hZ V ts b hzero hcomp).exists.choose := by
  let η := existsUnique_normalBundleThomClass k i hX hZ V ts b hzero hcomp
  let h := exists_normalBundleThomClassOfCharts k i hX hZ V ts b hc hzero hcomp
  let e := relativeOpenRestrictionTopIso k (Y := Z) (V := normalBundleOfSmooth i) (p) jₙ
  let g : (⊤ : Z.left.Opens) ⟶ ts.sup (fun x => (V x).1) := eqToHom hc.symm
  obtain ⟨τ, hτ, ht⟩ := h.choose_spec.1
  have hu : τ = η.exists.choose := η.unique hτ η.exists.choose_spec
  exact ht.trans (congrArg (fun r => e.inv ≫ (Q).map g ≫ r) hu)

set_option maxHeartbeats 850000 in
-- Recover the chart value from the defining restriction property.
/-- The global class restricts to the original normalized class along every selected chart. -/
theorem normalBundleThomClassOfCharts_restrict
    (b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(E₀, (V x).1))
    (hc : ts.sup (fun x => (V x).1) = ⊤)
    (hzero : ∀ U, Subsingleton (((Q).obj U)⟦(1 : ℤ)⟧ ⟶ K))
    (hcomp : ∀ x y, (Q).map (homOfLE (inf_le_left :
        (V x).1 ⊓ (V y).1 ≤ (V x).1)) ≫ normalBundleBasisThomClass k i hX hZ (V x) (b x) =
      (Q).map (homOfLE (inf_le_right :
        (V x).1 ⊓ (V y).1 ≤ (V y).1)) ≫ normalBundleBasisThomClass k i hX hZ (V y) (b y))
    (x : J) (hx : x ∈ ts) :
    (Q).map (homOfLE (le_top : (V x).1 ≤ ⊤)) ≫ (relativeOpenRestrictionTopIso k (p) jₙ).hom ≫
      normalBundleThomClassOfCharts k i hX hZ V ts b hc hzero hcomp =
        normalBundleBasisThomClass k i hX hZ (V x) (b x) :=
  (exists_normalBundleThomClassOfCharts k i hX hZ V ts b hc hzero hcomp).choose_spec.2 x hx

set_option maxHeartbeats 850000 in
-- Keep the underlying lattice arrows fixed when composing the original restrictions.
/-- The chart formula holds for every affine open subordinate to a selected frame. -/
theorem normalBundleThomClassOfCharts_restrict_subopen
    (b : ∀ x, Module.Basis (Fin (n - m)) Γ(Z.left, (V x).1) Γ(E₀, (V x).1))
    (hc : ts.sup (fun x => (V x).1) = ⊤)
    (hzero : ∀ U, Subsingleton (((Q).obj U)⟦(1 : ℤ)⟧ ⟶ K))
    (hcomp : ∀ x y, (Q).map (homOfLE (inf_le_left :
        (V x).1 ⊓ (V y).1 ≤ (V x).1)) ≫ normalBundleBasisThomClass k i hX hZ (V x) (b x) =
      (Q).map (homOfLE (inf_le_right :
        (V x).1 ⊓ (V y).1 ≤ (V y).1)) ≫ normalBundleBasisThomClass k i hX hZ (V y) (b y))
    (x : J) (hx : x ∈ ts) (W : Z.left.affineOpens) (h : W.1 ≤ (V x).1) :
    (Q).map (homOfLE (le_top : W.1 ≤ ⊤)) ≫ (relativeOpenRestrictionTopIso k (p) jₙ).hom ≫
      normalBundleThomClassOfCharts k i hX hZ V ts b hc hzero hcomp =
        normalBundleBasisThomClass k i hX hZ W
          (Scheme.Modules.vectorBundleBasisRestrict E₀ (b x) h) := by
  let f : W.1 ⟶ (V x).1 := homOfLE h
  let g : (V x).1 ⟶ (⊤ : Z.left.Opens) := homOfLE le_top
  let a : W.1 ⟶ (⊤ : Z.left.Opens) := homOfLE le_top
  let t := (relativeOpenRestrictionTopIso k (p) jₙ).hom ≫
    normalBundleThomClassOfCharts k i hX hZ V ts b hc hzero hcomp
  have hfg : f ≫ g = a := Subsingleton.elim _ _
  have hg : (Q).map a = (Q).map f ≫ (Q).map g :=
    ((Q).congr_map hfg.symm).trans ((Q).map_comp f g)
  have ht : (Q).map g ≫ t = normalBundleBasisThomClass k i hX hZ (V x) (b x) :=
    normalBundleThomClassOfCharts_restrict k i hX hZ V ts b hc hzero hcomp x hx
  have hW : (Q).map f ≫ normalBundleBasisThomClass k i hX hZ (V x) (b x) =
      normalBundleBasisThomClass k i hX hZ W
        (Scheme.Modules.vectorBundleBasisRestrict E₀ (b x) h) :=
    normalBundleBasisThomClass_restrict k i hX hZ (V x) (b x) W h
  exact (congrArg (· ≫ t) hg).trans ((Category.assoc _ _ _).trans
    ((congrArg ((Q).map f ≫ ·) ht).trans hW))

end WholeBase

end Descent

end AlgebraicGeometry.MotivicHomotopy
