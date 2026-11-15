/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Category
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.GraphTransport
import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction

/-!
# Naturality of the product switch in finite correspondences

The switch transports the two whole closed supports by their pullback
symmetry. Graph transport gives naturality on signed native cycles.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.Scheme MonoidalCategory BraidedCategory

universe u

namespace Stacks.Chow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] (X Y U V : SmoothSite (Spec (.of k)))

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

private theorem braiding_left_fst (X U : SmoothSite (Spec (.of k))) :
    (β_ X U).hom.left ≫ pullback.fst U.hom X.hom = pullback.snd X.hom U.hom :=
  congrArg (fun f => f.left) (CartesianMonoidalCategory.braiding_hom_fst X U)

private theorem braiding_left_snd (X U : SmoothSite (Spec (.of k))) :
    (β_ X U).hom.left ≫ pullback.snd U.hom X.hom = pullback.fst X.hom U.hom :=
  congrArg (fun f => f.left) (CartesianMonoidalCategory.braiding_hom_snd X U)

private theorem correspondenceExteriorInclusion_comp_braiding
    (A : (pullback X.hom Y.hom).IdealSheafData)
    (B : (pullback U.hom V.hom).IdealSheafData) :
    correspondenceExteriorInclusion X Y U V A B ≫
        (SmoothSite.productMap (β_ X U).hom (β_ Y V).hom).left =
      (pullbackSymmetry
        (exteriorSupportSourceProjection X Y A ≫ X.hom)
        (exteriorSupportSourceProjection U V B ≫ U.hom)).hom ≫
          correspondenceExteriorInclusion U V X Y B A := by
  let p := (SmoothSite.productMap (β_ X U).hom (β_ Y V).hom).left
  have hp₁ : p ≫ pullback.fst (SmoothSite.product U X).hom (SmoothSite.product V Y).hom =
      pullback.fst (SmoothSite.product X U).hom (SmoothSite.product Y V).hom ≫ (β_ X U).hom.left :=
    congrArg (fun f => f.left) (SmoothSite.productMap_fst (β_ X U).hom (β_ Y V).hom)
  have hp₂ : p ≫ pullback.snd (SmoothSite.product U X).hom (SmoothSite.product V Y).hom =
      pullback.snd (SmoothSite.product X U).hom (SmoothSite.product Y V).hom ≫ (β_ Y V).hom.left :=
    congrArg (fun f => f.left) (SmoothSite.productMap_snd (β_ X U).hom (β_ Y V).hom)
  change correspondenceExteriorInclusion X Y U V A B ≫ p = _
  apply pullback.hom_ext (f := (SmoothSite.product U X).hom) (g := (SmoothSite.product V Y).hom)
  · rw [Category.assoc, hp₁, correspondenceExteriorInclusion_fst_assoc,
      Category.assoc, correspondenceExteriorInclusion_fst]
    change correspondenceExteriorSource X Y U V A B ≫ (β_ X U).hom.left =
      (pullbackSymmetry
        (exteriorSupportSourceProjection X Y A ≫ X.hom)
        (exteriorSupportSourceProjection U V B ≫ U.hom)).hom ≫
          correspondenceExteriorSource U V X Y B A
    apply pullback.hom_ext (f := U.hom) (g := X.hom)
    · simp only [Category.assoc, braiding_left_fst X U, correspondenceExteriorSource_fst,
        correspondenceExteriorSource_snd, pullbackSymmetry_hom_comp_fst_assoc]
    · simp only [Category.assoc, braiding_left_snd X U, correspondenceExteriorSource_snd,
        correspondenceExteriorSource_fst, pullbackSymmetry_hom_comp_snd_assoc]
  · rw [Category.assoc, hp₂, correspondenceExteriorInclusion_snd_assoc,
      Category.assoc, correspondenceExteriorInclusion_snd]
    change correspondenceExteriorTarget X Y U V A B ≫ (β_ Y V).hom.left =
      (pullbackSymmetry
        (exteriorSupportSourceProjection X Y A ≫ X.hom)
        (exteriorSupportSourceProjection U V B ≫ U.hom)).hom ≫
          correspondenceExteriorTarget U V X Y B A
    apply pullback.hom_ext (f := V.hom) (g := Y.hom)
    · simp only [Category.assoc, braiding_left_fst Y V, correspondenceExteriorTarget_fst,
        correspondenceExteriorTarget_snd, pullbackSymmetry_hom_comp_fst_assoc]
    · simp only [Category.assoc, braiding_left_snd Y V, correspondenceExteriorTarget_snd,
        correspondenceExteriorTarget_fst, pullbackSymmetry_hom_comp_snd_assoc]

private theorem pushforward_correspondenceExteriorPrime_braiding
    (a : pullback (C := Scheme) X.hom Y.hom) (b : pullback (C := Scheme) U.hom V.hom)
    (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
    (hb : IsFiniteCorrespondencePoint U.hom V.hom b) :
    letI : IsIso (SmoothSite.productMap (β_ X U).hom (β_ Y V).hom).left :=
      Cor.productMap_left_isIso (β_ X U).hom (β_ Y V).hom
    finiteCyclePushforward (SmoothSite.productMap (β_ X U).hom (β_ Y V).hom).left
        (correspondenceExteriorPrime X Y U V a b ha hb).val =
      (correspondenceExteriorPrime U V X Y b a hb ha).val := by
  let A := integralComponentAt a
  let B := integralComponentAt b
  let : IsFinite (exteriorSupportSourceProjection X Y A) := ha.1
  let : IsFinite (exteriorSupportSourceProjection U V B) := hb.1
  let := correspondenceExteriorSupport_isNoetherian X Y U V a b ha hb
  let := correspondenceExteriorSupport_isNoetherian U V X Y b a hb ha
  let p := (SmoothSite.productMap (β_ X U).hom (β_ Y V).hom).left
  let : IsIso p := Cor.productMap_left_isIso (β_ X U).hom (β_ Y V).hom
  let r := correspondenceExteriorInclusion X Y U V A B
  let s := correspondenceExteriorInclusion U V X Y B A
  let e := pullbackSymmetry
    (exteriorSupportSourceProjection X Y A ≫ X.hom)
    (exteriorSupportSourceProjection U V B ≫ U.hom)
  rw [correspondenceExteriorPrime_val, correspondenceExteriorPrime_val]
  change finiteCyclePushforward p (finiteCyclePushforward r (AlgebraicCycle.fundamentalCycle _)) =
    finiteCyclePushforward s (AlgebraicCycle.fundamentalCycle _)
  rw [finiteCyclePushforward_comp_apply]
  calc
    _ = finiteCyclePushforward (e.hom ≫ s) (AlgebraicCycle.fundamentalCycle _) :=
      finiteCyclePushforward_congr _ _
        (correspondenceExteriorInclusion_comp_braiding X Y U V A B) _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso]

private theorem pushforward_correspondenceExterior_braiding
    (a : finiteCorrespondences X.hom Y.hom) (b : finiteCorrespondences U.hom V.hom) :
    letI : IsIso (SmoothSite.productMap (β_ X U).hom (β_ Y V).hom).left :=
      Cor.productMap_left_isIso (β_ X U).hom (β_ Y V).hom
    finiteCyclePushforward (SmoothSite.productMap (β_ X U).hom (β_ Y V).hom).left
        (correspondenceExterior X Y U V a b).val =
      (correspondenceExterior U V X Y b a).val := by
  let p := (SmoothSite.productMap (β_ X U).hom (β_ Y V).hom).left
  let : IsIso p := Cor.productMap_left_isIso (β_ X U).hom (β_ Y V).hom
  let F := (finiteCyclePushforward p).comp
    (finiteCorrespondences (SmoothSite.product X U).hom (SmoothSite.product Y V).hom).subtype
  let G := (finiteCorrespondences
    (SmoothSite.product U X).hom (SmoothSite.product V Y).hom).subtype
  let L := (AddMonoidHom.compHom F).comp (correspondenceExterior X Y U V)
  let R := (AddMonoidHom.compHom G).comp (correspondenceExterior U V X Y).flip
  have h : L = R := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro x hx
    apply finiteCorrespondences.addHom_ext_one U.hom V.hom
    intro y hy
    change finiteCyclePushforward p (correspondenceExterior X Y U V
        (singleFiniteCorrespondence X.hom Y.hom x hx 1)
        (singleFiniteCorrespondence U.hom V.hom y hy 1)).val =
      (correspondenceExterior U V X Y
        (singleFiniteCorrespondence U.hom V.hom y hy 1)
        (singleFiniteCorrespondence X.hom Y.hom x hx 1)).val
    simp only [correspondenceExterior_single, one_mul, one_smul]
    exact pushforward_correspondenceExteriorPrime_braiding X Y U V x y hx hy
  exact DFunLike.congr_fun (DFunLike.congr_fun h a) b

end Stacks.Chow

namespace AlgebraicGeometry.Cor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- The graph switch is natural on the original signed correspondences. -/
theorem exteriorBraidingNaturality : ExteriorBraidingNaturality k := by
  rintro ⟨X⟩ ⟨Y⟩ ⟨U⟩ ⟨V⟩ a b
  exact comp_graph_iso_eq_graph_iso_comp (β_ X U) (β_ Y V)
    (exteriorProduct a b) (exteriorProduct b a)
    (pushforward_correspondenceExterior_braiding X Y U V a b)

end AlgebraicGeometry.Cor
