/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.DoubleTorus
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor.Exterior
public import Colib.AlgebraicGeometry.Correspondences.Graph.Isomorphism
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Parameters
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureRelativeClosure

/-!
# The actual inner exterior support of a prime

The two native torus swaps carry the exterior prime to the same closed
support, with the old torus last. This comparison retains the old base,
old torus and new parameter coordinates.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

universe u

attribute [local instance] Classical.propDecidable

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X T
local notation "F" => Cor.parameterProduct T
local notation "γ" => CategoryTheory.Functor.map (Cor.graphFunctor k)

/-- Adjoin the identity on the inner torus by the original two swaps. -/
abbrev torusInnerExtension {X Y : Cor k} (a : (F).obj X ⟶ (F).obj Y) :
    (F).obj ((F).obj X) ⟶ (F).obj ((F).obj Y) :=
  torusDoubleSwap k X ≫ (F).map a ≫ torusDoubleSwap k Y

variable (X Y : SmoothSite (Spec (.of k)))
  (w : pullback (C := Scheme)
    (product X (multiplicativeGroupObject (Spec (.of k)))).hom
    (product Y (multiplicativeGroupObject (Spec (.of k)))).hom)
  (hw : IsFiniteCorrespondencePoint
    (product X (multiplicativeGroupObject (Spec (.of k)))).hom
    (product Y (multiplicativeGroupObject (Spec (.of k)))).hom w)

local notation3 (prettyPrint := false) "g" => (G(X)).hom
local notation3 (prettyPrint := false) "h" => (G(Y)).hom
local notation3 (prettyPrint := false) "g'" => (G(G(X))).hom
local notation3 (prettyPrint := false) "h'" => (G(G(Y))).hom
local notation3 (prettyPrint := false) "z" => nativeExteriorPoint (G(X)) (G(Y)) T w hw
local notation3 (prettyPrint := false) "hz" => nativeExteriorPoint_admissible (G(X)) (G(Y)) T w hw
local notation3 (prettyPrint := false) "a₁" =>
  (SmoothSite.productMap (productSwapLastIso X T T).inv (𝟙 (G(G(Y))))).left
local notation3 (prettyPrint := false) "a₂" =>
  (SmoothSite.productMap (𝟙 (G(G(X)))) (productSwapLastIso Y T T).hom).left

/-- The actual prime point in the inner exterior coordinates. -/
def torusInnerExtensionPrimePoint : pullback (C := Scheme) g' h' :=
  a₂ (a₁ z)

local notation3 (prettyPrint := false) "w'" => torusInnerExtensionPrimePoint k X Y w hw

/-- The inner exterior of a coefficient-one prime is the actual
coefficient-one prime at its permuted point. -/
theorem torusInnerExtensionPrime_val :
    (torusInnerExtension k (singleFiniteCorrespondence g h w hw 1)).val = single w' (1 : ℤ) := by
  let eX := productSwapLastIso X T T
  let eY := productSwapLastIso Y T T
  let pre := γ eX.hom ≫ (singleFiniteCorrespondence g' h' z hz 1 :
    Cor.mk (G(G(X))) ⟶ Cor.mk (G(G(Y))))
  have hpre : pre.val = single (a₁ z) (1 : ℤ) := Cor.graph_iso_comp_single_val eX z hz
  have h₁ : IsFiniteCorrespondencePoint g' h' (a₁ z) := by
    apply pre.property.2
    rw [hpre, single_apply, ite_eq_left (rfl : a₁ z = a₁ z)]
    exact one_ne_zero
  have he : pre = singleFiniteCorrespondence g' h' (a₁ z) h₁ 1 := Subtype.ext hpre
  change (γ eX.hom ≫ nativeExterior (G(X)) (G(Y)) T
    (singleFiniteCorrespondence g h w hw 1) ≫ γ eY.hom).val = _
  rw [nativeExterior_single, one_smul, nativeExteriorPrime_eq_single, ← Category.assoc]
  change (pre ≫ γ eY.hom).val = _
  rw [he]
  exact Cor.single_comp_graph_iso_val eY (a₁ z) h₁

/-- The actual permuted support point is admissible. -/
theorem torusInnerExtensionPrimePoint_admissible : IsFiniteCorrespondencePoint g' h' w' := by
  let a := torusInnerExtension k (singleFiniteCorrespondence g h w hw 1)
  have ha : a.val = single w' (1 : ℤ) := torusInnerExtensionPrime_val k X Y w hw
  apply a.property.2
  rw [ha, single_apply, ite_eq_left (rfl : w' = w')]
  exact one_ne_zero

local notation3 (prettyPrint := false) "P" => (integralComponentAt w).subscheme
local notation3 (prettyPrint := false) "j" => (integralComponentAt w).subschemeι
local notation3 (prettyPrint := false) "p₀" => j ≫ pullback.fst g h
local notation3 (prettyPrint := false) "p" => Cor.torusSupportBaseProjection k p₀
local notation3 (prettyPrint := false) "q" =>
  Cor.torusSupportBaseProjection k (j ≫ pullback.snd g h)
local notation3 (prettyPrint := false) "b" => p ≫ X.hom
local notation3 (prettyPrint := false) "π" => pullback.fst b (T).hom

/-- The support product with its structure map reassociated over the original base. -/
abbrev originalSupportProductIso :
    pullback b (T).hom ≅ exteriorIdentitySupport (G(X)) (G(Y)) T (integralComponentAt w) :=
  pullback.congrHom (Category.assoc p₀ (productFst X T).left X.hom) (rfl : (T).hom = (T).hom)

local notation3 (prettyPrint := false) "e₀" => originalSupportProductIso k X Y w

private theorem originalSupportProductIso_fst :
    (e₀).hom ≫ pullback.fst (p₀ ≫ g) (T).hom = π :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem originalSupportProductIso_snd :
    (e₀).hom ≫ pullback.snd (p₀ ≫ g) (T).hom = pullback.snd b (T).hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

set_option maxHeartbeats 800000 in
-- The closed component isomorphism compares the actual image of two product maps.
/-- The actual product of the original support and the inner parameter
is the native support at the permuted point. -/
def torusInnerExtensionSupportIso : pullback b (T).hom ≅ (integralComponentAt w').subscheme := by
  let : IsIso a₁ := Cor.productMap_left_isIso (productSwapLastIso X T T).inv (𝟙 (G(G(Y))))
  let : IsIso a₂ := Cor.productMap_left_isIso (𝟙 (G(G(X)))) (productSwapLastIso Y T T).hom
  let : IsIso (a₁ ≫ a₂) := inferInstance
  let e' : (integralComponentAt z).subscheme ≅ (integralComponentAt w').subscheme :=
    integralComponentIso (a₁ ≫ a₂) z
  exact e₀ ≪≫ nativeExteriorSupportIso (G(X)) (G(Y)) T w hw ≪≫ e'

local notation3 (prettyPrint := false) "e" => torusInnerExtensionSupportIso k X Y w hw

set_option maxHeartbeats 800000 in
-- The four original product factors remain visible in the native support comparison.
/-- The actual inclusion preserves the full original exterior support map
and both original swaps. -/
@[reassoc]
theorem torusInnerExtensionSupportIso_inclusion :
    (e).hom ≫ (integralComponentAt w').subschemeι =
      (e₀).hom ≫ exteriorIdentityInclusion (G(X)) (G(Y)) T (integralComponentAt w) ≫ a₁ ≫ a₂ := by
  let eX := productSwapLastIso X T T
  let eY := productSwapLastIso Y T T
  let : IsIso a₁ := Cor.productMap_left_isIso eX.inv (𝟙 (G(G(Y))))
  let : IsIso a₂ := Cor.productMap_left_isIso (𝟙 (G(G(X)))) eY.hom
  let : IsIso (a₁ ≫ a₂) := inferInstance
  let d := a₁ ≫ a₂
  let eN := nativeExteriorSupportIso (G(X)) (G(Y)) T w hw
  have hd : (integralComponentIso d z).hom ≫ (integralComponentAt w').subschemeι =
      (integralComponentAt z).subschemeι ≫ d := integralComponentMap_subschemeι d z
  change ((e₀).hom ≫ (eN.hom ≫ (integralComponentIso d z).hom)) ≫ _ = _
  calc
    _ = (e₀).hom ≫ eN.hom ≫ (integralComponentIso d z).hom ≫
        (integralComponentAt w').subschemeι := by simp only [Category.assoc]
    _ = (e₀).hom ≫ eN.hom ≫ (integralComponentAt z).subschemeι ≫ d :=
      congrArg (fun a => (e₀).hom ≫ eN.hom ≫ a) hd
    _ = _ := by
      simp only [eN, nativeExteriorSupportIso_hom_inclusion_assoc, d]

set_option maxHeartbeats 800000 in
-- Both sides retain the actual source projection across the original swap.
private theorem torusInnerExtensionSupportIso_source :
    (e).hom ≫ (integralComponentAt w').subschemeι ≫ pullback.fst g' h' =
      (e₀).hom ≫ Cor.torusSupportParameterExtension k (X := X) p₀ := by
  have h₁ : a₁ ≫ pullback.fst g' h' =
      pullback.fst g' h' ≫ (productSwapLastIso X T T).inv.left :=
    congrArg (fun m => m.left)
      (SmoothSite.productMap_fst (productSwapLastIso X T T).inv (𝟙 (G(G(Y)))))
  have h₂ : a₂ ≫ pullback.fst g' h' = pullback.fst g' h' := by
    have hproj : a₂ ≫ pullback.fst g' h' =
        pullback.fst g' h' ≫ 𝟙 (G(G(X))).left :=
      congrArg (fun m => m.left)
        (SmoothSite.productMap_fst (𝟙 (G(G(X)))) (productSwapLastIso Y T T).hom)
    exact hproj.trans (Category.comp_id _)
  rw [torusInnerExtensionSupportIso_inclusion_assoc]
  simp only [h₂, h₁, exteriorIdentityInclusion_fst_assoc]
  have hsource : exteriorIdentitySource (G(X)) (G(Y)) T (integralComponentAt w) =
      pullbackParameterExtensionMap p₀ g (T).hom := rfl
  have hswap : (productSwapLastIso X T T).inv = productSwapLast X T T := rfl
  rw [hsource, hswap]
  change (e₀).hom ≫ pullbackParameterExtensionMap p₀ g (T).hom ≫
      (productSwapLast X T T).left =
    (e₀).hom ≫ (pullbackParameterExtensionMap p₀ g (T).hom ≫ (productSwapLast X T T).left)
  rfl

set_option maxHeartbeats 800000 in
-- Both sides retain the actual target projection across the original swap.
private theorem torusInnerExtensionSupportIso_target :
    (e).hom ≫ (integralComponentAt w').subschemeι ≫ pullback.snd g' h' =
      (e₀).hom ≫ exteriorIdentityTarget (G(X)) (G(Y)) T (integralComponentAt w) ≫
        (productSwapLastIso Y T T).hom.left := by
  have h₁ : a₁ ≫ pullback.snd g' h' = pullback.snd g' h' := by
    have hproj : a₁ ≫ pullback.snd g' h' =
        pullback.snd g' h' ≫ 𝟙 (G(G(Y))).left :=
      congrArg (fun m => m.left)
        (SmoothSite.productMap_snd (productSwapLastIso X T T).inv (𝟙 (G(G(Y)))))
    exact hproj.trans (Category.comp_id _)
  have h₂ : a₂ ≫ pullback.snd g' h' =
      pullback.snd g' h' ≫ (productSwapLastIso Y T T).hom.left :=
    congrArg (fun m => m.left)
      (SmoothSite.productMap_snd (𝟙 (G(G(X)))) (productSwapLastIso Y T T).hom)
  rw [torusInnerExtensionSupportIso_inclusion_assoc]
  simp only [h₂, reassoc_of% h₁, exteriorIdentityInclusion_snd_assoc]

local notation3 (prettyPrint := false) "p'" =>
  (integralComponentAt w').subschemeι ≫ pullback.fst g' h'
local notation3 (prettyPrint := false) "q'" =>
  (integralComponentAt w').subschemeι ≫ pullback.snd g' h'
set_option maxHeartbeats 800000 in
-- The native product projection retains the four original scheme coordinates.
/-- The two base projections of the permuted support are precisely the
original cut projections extended by the same parameter. -/
theorem torusInnerExtensionSupportIso_cut_projections
    (hb : p ≫ X.hom = q ≫ Y.hom) :
    ((e).hom ≫ Cor.torusSupportBaseProjection k (X := G(X)) p' =
      pullbackParameterExtensionMap p X.hom (T).hom) ∧
    ((e).hom ≫ Cor.torusSupportBaseProjection k (X := G(Y)) q' =
      Cor.sectionCutExteriorTarget T p q hb) := by
  have hs := torusInnerExtensionSupportIso_source k X Y w hw
  have ht := torusInnerExtensionSupportIso_target k X Y w hw
  have hswap : (productSwapLastIso Y T T).hom.left ≫ pullback.fst (G(Y)).hom (T).hom =
      (SmoothSite.productMap (productFst Y T) (𝟙 T)).left :=
    congrArg (fun m => m.left) (productSwapLast_fst Y T T)
  have hfst : (SmoothSite.productMap (productFst Y T) (𝟙 T)).left ≫ pullback.fst Y.hom (T).hom =
      pullback.fst (G(Y)).hom (T).hom ≫ (productFst Y T).left :=
    congrArg (fun m => m.left) (SmoothSite.productMap_fst (productFst Y T) (𝟙 T))
  have hsnd : (SmoothSite.productMap (productFst Y T) (𝟙 T)).left ≫ pullback.snd Y.hom (T).hom =
      pullback.snd (G(Y)).hom (T).hom := by
    have he : (SmoothSite.productMap (productFst Y T) (𝟙 T)).left ≫
        pullback.snd Y.hom (T).hom = pullback.snd (G(Y)).hom (T).hom ≫ 𝟙 (T).left :=
      congrArg (fun m => m.left) (SmoothSite.productMap_snd (productFst Y T) (𝟙 T))
    exact he.trans (Category.comp_id _)
  let π₀ := pullback.fst (p₀ ≫ g) (T).hom
  let t₀ := pullback.snd (p₀ ≫ g) (T).hom
  let s := Cor.torusSupportParameterExtension k (X := X) p₀
  let t := exteriorIdentityTarget (G(X)) (G(Y)) T (integralComponentAt w)
  let jY := exteriorSupportTargetProjection (G(X)) (G(Y)) (integralComponentAt w)
  let v := (productSwapLastIso Y T T).hom.left
  let bX := pullback.fst (G(X)).hom (T).hom
  let bY := pullback.fst (G(Y)).hom (T).hom
  let x₁ := pullback.fst X.hom (T).hom
  let x₂ := pullback.snd X.hom (T).hom
  let y₁ := pullback.fst Y.hom (T).hom
  let y₂ := pullback.snd Y.hom (T).hom
  have hs₁ : (s ≫ bX) ≫ x₁ = π₀ ≫ p :=
    Cor.torusSupportParameterExtension_base k (X := X) p₀
  have hs₂ : (s ≫ bX) ≫ x₂ = t₀ :=
    Cor.torusSupportParameterExtension_parameter k (X := X) p₀
  have ht₁ : (t ≫ v ≫ bY) ≫ y₁ = π₀ ≫ q := by
    change (t ≫ v ≫ bY) ≫ y₁ = π₀ ≫ jY ≫ y₁
    have h₁ : t ≫ bY = π₀ ≫ jY := exteriorIdentityTarget_fst _ _ _ _
    calc
      _ = t ≫ (v ≫ bY) ≫ y₁ := by simp only [Category.assoc]
      _ = t ≫ (SmoothSite.productMap (productFst Y T) (𝟙 T)).left ≫ y₁ :=
        congrArg (fun a => t ≫ a ≫ y₁) hswap
      _ = t ≫ bY ≫ y₁ := congrArg (t ≫ ·) hfst
      _ = _ := (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ y₁) h₁).trans (Category.assoc _ _ _))
  have ht₂ : (t ≫ v ≫ bY) ≫ y₂ = t₀ := by
    calc
      _ = t ≫ (v ≫ bY) ≫ y₂ := by simp only [Category.assoc]
      _ = t ≫ (SmoothSite.productMap (productFst Y T) (𝟙 T)).left ≫ y₂ :=
        congrArg (fun a => t ≫ a ≫ y₂) hswap
      _ = t ≫ pullback.snd (G(Y)).hom (T).hom := congrArg (t ≫ ·) hsnd
      _ = _ := exteriorIdentityTarget_snd _ _ _ _
  have hπ : (e₀).hom ≫ π₀ = π := originalSupportProductIso_fst k X Y w
  have hparamProjection : (e₀).hom ≫ t₀ = pullback.snd b (T).hom :=
    originalSupportProductIso_snd k X Y w
  have es₁ : (e).hom ≫ Cor.torusSupportBaseProjection k (X := G(X)) p' ≫ x₁ = π ≫ p := by
    change (e).hom ≫ (p' ≫ bX) ≫ x₁ = _
    calc
      _ = (((e).hom ≫ p') ≫ bX) ≫ x₁ := by simp only [Category.assoc]
      _ = (((e₀).hom ≫ s) ≫ bX) ≫ x₁ := congrArg (fun a => (a ≫ bX) ≫ x₁) hs
      _ = (e₀).hom ≫ ((s ≫ bX) ≫ x₁) := by simp only [Category.assoc]
      _ = (e₀).hom ≫ (π₀ ≫ p) := congrArg ((e₀).hom ≫ ·) hs₁
      _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) hπ)
  have es₂ : (e).hom ≫ Cor.torusSupportBaseProjection k (X := G(X)) p' ≫ x₂ =
      pullback.snd b (T).hom := by
    change (e).hom ≫ (p' ≫ bX) ≫ x₂ = _
    calc
      _ = (((e).hom ≫ p') ≫ bX) ≫ x₂ := by simp only [Category.assoc]
      _ = (((e₀).hom ≫ s) ≫ bX) ≫ x₂ := congrArg (fun a => (a ≫ bX) ≫ x₂) hs
      _ = (e₀).hom ≫ ((s ≫ bX) ≫ x₂) := by simp only [Category.assoc]
      _ = (e₀).hom ≫ t₀ := congrArg ((e₀).hom ≫ ·) hs₂
      _ = _ := hparamProjection
  have et₁ : (e).hom ≫ Cor.torusSupportBaseProjection k (X := G(Y)) q' ≫ y₁ = π ≫ q := by
    change (e).hom ≫ (q' ≫ bY) ≫ y₁ = _
    calc
      _ = (((e).hom ≫ q') ≫ bY) ≫ y₁ := by simp only [Category.assoc]
      _ = (((e₀).hom ≫ t ≫ v) ≫ bY) ≫ y₁ := congrArg (fun a => (a ≫ bY) ≫ y₁) ht
      _ = (e₀).hom ≫ ((t ≫ v ≫ bY) ≫ y₁) := by simp only [Category.assoc]
      _ = (e₀).hom ≫ (π₀ ≫ q) := congrArg ((e₀).hom ≫ ·) ht₁
      _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) hπ)
  have et₂ : (e).hom ≫ Cor.torusSupportBaseProjection k (X := G(Y)) q' ≫ y₂ =
      pullback.snd b (T).hom := by
    change (e).hom ≫ (q' ≫ bY) ≫ y₂ = _
    calc
      _ = (((e).hom ≫ q') ≫ bY) ≫ y₂ := by simp only [Category.assoc]
      _ = (((e₀).hom ≫ t ≫ v) ≫ bY) ≫ y₂ := congrArg (fun a => (a ≫ bY) ≫ y₂) ht
      _ = (e₀).hom ≫ ((t ≫ v ≫ bY) ≫ y₂) := by simp only [Category.assoc]
      _ = (e₀).hom ≫ t₀ := congrArg ((e₀).hom ≫ ·) ht₂
      _ = _ := hparamProjection
  constructor
  · apply pullback.hom_ext (f := X.hom) («g» := (T).hom)
    · exact ((Category.assoc _ _ _).trans es₁).trans
        (pullbackParameterExtensionMap_fst p X.hom (T).hom).symm
    · exact ((Category.assoc _ _ _).trans es₂).trans
        (pullbackParameterExtensionMap_snd p X.hom (T).hom).symm
  · apply pullback.hom_ext (f := Y.hom) («g» := (T).hom)
    · exact ((Category.assoc _ _ _).trans et₁).trans
        (Cor.sectionCutExteriorTarget_fst T p q hb).symm
    · exact ((Category.assoc _ _ _).trans et₂).trans
        (Cor.sectionCutExteriorTarget_snd T p q hb).symm

/-- The two original torus maps pull back along the actual support projection. -/
theorem torusInnerExtensionSupportIso_torus_projections :
    ((e).hom ≫ p' ≫ pullback.snd (G(X)).hom (T).hom =
      π ≫ p₀ ≫ pullback.snd X.hom (T).hom) ∧
    ((e).hom ≫ q' ≫ pullback.snd (G(Y)).hom (T).hom =
      π ≫ j ≫ pullback.snd g h ≫ pullback.snd Y.hom (T).hom) := by
  have hs := torusInnerExtensionSupportIso_source k X Y w hw
  have ht := torusInnerExtensionSupportIso_target k X Y w hw
  have hswap : (productSwapLastIso Y T T).hom.left ≫ pullback.snd (G(Y)).hom (T).hom =
      pullback.fst (G(Y)).hom (T).hom ≫ pullback.snd Y.hom (T).hom :=
    congrArg (fun m => m.left) (productSwapLast_snd Y T T)
  let π₀ := pullback.fst (p₀ ≫ g) (T).hom
  have hπ : (e₀).hom ≫ π₀ = π := originalSupportProductIso_fst k X Y w
  constructor
  · calc
      _ = ((e).hom ≫ p') ≫ pullback.snd (G(X)).hom (T).hom := (Category.assoc _ _ _).symm
      _ = ((e₀).hom ≫ Cor.torusSupportParameterExtension k (X := X) p₀) ≫
          pullback.snd (G(X)).hom (T).hom := congrArg (· ≫ _) hs
      _ = (e₀).hom ≫ (π₀ ≫ p₀ ≫ pullback.snd X.hom (T).hom) :=
        (Category.assoc _ _ _).trans
          (congrArg ((e₀).hom ≫ ·) (Cor.torusSupportParameterExtension_torus k (X := X) p₀))
      _ = _ := (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ p₀ ≫ pullback.snd X.hom (T).hom) hπ)
  · let t := exteriorIdentityTarget (G(X)) (G(Y)) T (integralComponentAt w)
    let v := (productSwapLastIso Y T T).hom.left
    let a := pullback.snd (G(Y)).hom (T).hom
    let d := pullback.fst (G(Y)).hom (T).hom
    let eY := pullback.snd Y.hom (T).hom
    have ht₀ : t ≫ d = π₀ ≫ j ≫ pullback.snd g h := exteriorIdentityTarget_fst _ _ _ _
    calc
      _ = ((e).hom ≫ q') ≫ a := (Category.assoc _ _ _).symm
      _ = ((e₀).hom ≫ t ≫ v) ≫ a := congrArg (· ≫ a) ht
      _ = (e₀).hom ≫ t ≫ (v ≫ a) := by simp only [Category.assoc]
      _ = (e₀).hom ≫ t ≫ (d ≫ eY) := congrArg (fun m => (e₀).hom ≫ t ≫ m) hswap
      _ = (e₀).hom ≫ (t ≫ d) ≫ eY := by simp only [Category.assoc]
      _ = (e₀).hom ≫ (π₀ ≫ j ≫ pullback.snd g h) ≫ eY :=
        congrArg (fun m => (e₀).hom ≫ m ≫ eY) ht₀
      _ = ((e₀).hom ≫ π₀) ≫ j ≫ pullback.snd g h ≫ eY := by simp only [Category.assoc]
      _ = _ := congrArg (· ≫ j ≫ pullback.snd g h ≫ eY) hπ

end AlgebraicGeometry.PresheafWithTransfers
