/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.OrientationVanishing
public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.AffineContraction
import Colib.AlgebraicGeometry.Correspondences.BaseChange.IntegralSource
import Colib.AlgebraicGeometry.SheavesWithTransfers.LocalVanishing.DenseOpen
import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Field
import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Weight-zero classes on integral smooth parameters

The original structure graph generates the maps from an integral smooth
motive to the base motive. A section locally has this form at the generic
point. Dense-open detection extends the equality over the original scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme SmoothSite.Contraction Opposite TopologicalSpace
open Stacks.Chow

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "B" => SmoothSite.base S
local notation "J" => SmoothSite.nisnevichTopology S
set_option quotPrecheck false in
local notation "F₀" => (transferRepresentable k).obj (Cor.mk B)
set_option quotPrecheck false in
local notation "P₀" => (representableLarge k).obj (Cor.mk B)
local notation "M" => effectiveSmoothMotive k
local notation "R" => transferRepresentable k

/-- Use the native transfer abelian structure for the parameter restriction maps. -/
local instance parameterOrientationAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k
set_option quotPrecheck false in
local notation "Γ" => (Cor.graphFunctor k).map

private abbrev baseCoefficientSections : (Sm)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  ((SheafWithTransfers.toSheaf k).obj (F₀)).obj

private abbrev baseCoefficientUnit :
    (toPresheaf k).obj (P₀) ⟶ baseCoefficientSections k :=
  (toPresheaf k).map (toNisnevichSheafify k P₀)

private theorem baseCoefficientHom_isMultiple (X : Sm) [IsIntegral X.left]
    (f : (R).obj (Cor.mk X) ⟶ F₀) :
    ∃ n : ℤ, f = n • (R).map (Γ (toBase X)) := by
  let η := baseCoefficientUnit k
  let sections (Y : Sm) := transferSectionsEquiv k (Cor.mk Y) (F₀)
  let s := sections X f
  obtain ⟨U, hU, a, ha⟩ := SmoothSite.exists_generic_open_mem_covering_sieve X _
    (Presheaf.imageSieve_mem J η s)
  let Y := (SmoothSite.opensFunctor X).obj U
  let i := SmoothSite.openInclusion X U
  let : Nonempty Y.left := ⟨⟨genericPoint X.left, hU⟩⟩
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion U.ι)
  let : IsIntegral Y.left := isIntegral_of_isOpenImmersion i.left
  let : IsIntegral ((𝟭 Scheme).obj Y.left) := inferInstanceAs (IsIntegral Y.left)
  let n : ℤ := structureCorrespondenceCoeff Y.hom a.down
  have ha' : a = n • ULift.up (Γ (toBase Y)) := by
    apply ULift.ext
    change a.down = n • Γ (toBase Y)
    have h : Γ (toBase Y) = structureGraphCorrespondence Y.hom :=
      graphCorrespondenceOfComponents_structure Y.hom (Cor.finite_genericPoints k (Cor.mk Y))
    exact (eq_coeff_zsmul_structureGraph Y.hom a.down).trans (congrArg (n • ·) h.symm)
  have he (Z : Sm) :
      sections Z ((R).map (Γ (toBase Z))) = η.app (op Z) (ULift.up (Γ (toBase Z))) := by
    rw [transferSectionsEquiv_apply]
    change ((PresheafWithTransfers.nisnevichSheafify k).map
      ((representableLarge k).map (Γ (toBase Z)))).hom.hom.app (op (Cor.mk Z))
        ((toNisnevichSheafify k ((representableLarge k).obj (Cor.mk Z))).hom.app (op (Cor.mk Z))
          (ULift.up (𝟙 (Cor.mk Z)))) = _
    have h := NatTrans.congr_app
      (congrArg (fun f => f.hom)
        (toNisnevichSheafify_naturality k ((representableLarge k).map (Γ (toBase Z)))))
      (op (Cor.mk Z))
    let x : ((representableLarge k).obj (Cor.mk Z)).sections (Cor.mk Z) :=
      ULift.up (𝟙 (Cor.mk Z))
    have hc := (ConcreteCategory.congr_hom h x).symm
    let M₀ := (representableLarge k).map (Γ (toBase Z))
    let A := nisnevichSheafify k
    let T := op (Cor.mk Z)
    let v := (toNisnevichSheafify k ((representableLarge k).obj (Cor.mk Z))).hom.app T
    let z := (toNisnevichSheafify k P₀).hom.app T
    let u := (A.map M₀).hom.hom.app T
    let w := M₀.hom.app T
    change ConcreteCategory.hom (v ≫ u) x = ConcreteCategory.hom (w ≫ z) x at hc
    have hw : w x = ULift.up (Γ (toBase Z)) :=
      (representableLarge_map_app_apply k (Γ (toBase Z)) (𝟙 (Cor.mk Z))).trans
        (congrArg ULift.up (Category.id_comp (Γ (toBase Z))))
    exact ((ConcreteCategory.comp_apply v u x).symm.trans hc).trans
      ((ConcreteCategory.comp_apply w z x).trans (congrArg (fun t => z t) hw))
  have hbase : DenseRange i.left := by
    change Dense (Set.range U.ι)
    rw [Scheme.Opens.range_ι]
    exact U.isOpen.dense ⟨genericPoint X.left, hU⟩
  refine ⟨n, (sections X).injective (sub_eq_zero.mp ?_)⟩
  refine SheafWithTransfers.section_eq_zero_of_dense_open_of_integralAffineLocalZero
    (integralAffineLocalZero_of_field k) i hbase (F₀)
    (baseTransferRepresentable_isA1Invariant k) _ ?_
  change (baseCoefficientSections k).map i.op
    (s - sections X (n • (R).map (Γ (toBase X)))) = 0
  rw [map_sub, sub_eq_zero, ← ha, ha', map_zsmul, map_zsmul, he]
  have hn := ConcreteCategory.congr_hom (η.naturality i.op) (ULift.up (Γ (toBase X)))
  have hγ : Γ i ≫ Γ (toBase X) = Γ (toBase Y) :=
    ((Cor.graphFunctor k).map_comp i (toBase X)).symm.trans
      ((Cor.graphFunctor k).congr_map (comp_toBase i))
  have h' : (baseCoefficientSections k).map i.op
      (η.app (op X) (ULift.up (Γ (toBase X)))) =
      η.app (op Y) (ULift.up (Γ (toBase Y))) :=
    hn.symm.trans (congrArg (fun g => η.app (op Y) (ULift.up g)) hγ)
  have hmap := map_zsmul (AddCommGrpCat.Hom.hom ((baseCoefficientSections k).map i.op)) n
    (η.app (op X) (ULift.up (Γ (toBase X))))
  exact (hmap.trans (congrArg (n • ·) h')).symm

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "D" => DerivedCategory.singleFunctor (LargeSheaves k) (0 : ℤ)

/-- A class of weight and degree zero has the same restriction along any two
maps with the same source and integral target. -/
theorem effectiveSmoothMotive_baseHom_precomp_eq {X Y : Sm} [IsIntegral Y.left]
    (f g : X ⟶ Y) (a : (M).obj Y ⟶ (M).obj B) :
    (M).map f ≫ a = (M).map g ≫ a := by
  let e := effectiveBaseMotiveToSingleIso k
  let h := Functor.FullyFaithful.ofFullyFaithful (D)
  let b := effectiveMotiveDerivedHomEquiv k (Cor.mk Y) ((M).obj B) a ≫ e.hom
  let c := h.preimage b
  obtain ⟨n, hc⟩ := baseCoefficientHom_isMultiple k Y c
  have hb : (D).map c = b := h.map_preimage b
  let H := effectiveMotiveDerivedHomEquiv k (Cor.mk X) ((M).obj B)
  let d := effectiveMotiveDerivedHomEquiv k (Cor.mk Y) ((M).obj B) a
  let f₀ := (D).map ((R).map (Γ f))
  let g₀ := (D).map ((R).map (Γ g))
  have hf : H ((M).map f ≫ a) = f₀ ≫ d :=
    effectiveMotiveDerivedHomEquiv_precomp k (Γ f) a
  have hg : H ((M).map g ≫ a) = g₀ ≫ d :=
    effectiveMotiveDerivedHomEquiv_precomp k (Γ g) a
  have hh : (f₀ ≫ d) ≫ e.hom = (g₀ ≫ d) ≫ e.hom := calc
    (f₀ ≫ d) ≫ e.hom = f₀ ≫ b := Category.assoc _ _ _
    _ = g₀ ≫ b := by
      let x : Cor.mk X ⟶ Cor.mk Y := Γ f
      let y : Cor.mk X ⟶ Cor.mk Y := Γ g
      let t : Cor.mk Y ⟶ Cor.mk B := Γ (toBase Y)
      have hx : x ≫ t = Γ (toBase X) :=
        ((Cor.graphFunctor k).map_comp f (toBase Y)).symm.trans
          ((Cor.graphFunctor k).congr_map (comp_toBase f))
      have hy : y ≫ t = Γ (toBase X) :=
        ((Cor.graphFunctor k).map_comp g (toBase Y)).symm.trans
          ((Cor.graphFunctor k).congr_map (comp_toBase g))
      have hxy : (R).map x ≫ c = (R).map y ≫ c := by
        have hc' : c = n • (R).map t := hc
        rw [hc', Preadditive.comp_zsmul, Preadditive.comp_zsmul, ← (R).map_comp,
          ← (R).map_comp, hx, hy]
      calc
        f₀ ≫ b = (D).map ((R).map x ≫ c) :=
          (congrArg (f₀ ≫ ·) hb.symm).trans ((D).map_comp ((R).map x) c).symm
        _ = (D).map ((R).map y ≫ c) := (D).congr_map hxy
        _ = g₀ ≫ b := ((D).map_comp ((R).map y) c).trans (congrArg (g₀ ≫ ·) hb)
    _ = (g₀ ≫ d) ≫ e.hom := (Category.assoc _ _ _).symm
  exact H.injective (hf.trans (((cancel_mono e.hom).mp hh).trans hg.symm))

end AlgebraicGeometry.MotivicHomotopy
