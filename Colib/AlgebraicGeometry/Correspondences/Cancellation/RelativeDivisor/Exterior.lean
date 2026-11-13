/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor
public import Colib.AlgebraicGeometry.Correspondences.Exterior.FiniteSupport
import Colib.AlgebraicGeometry.Chow.PrincipalSection.Naturality
import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward

/-!
# Principal cuts commute with the exterior identity

The cut of the pulled section on the parameter product is its actual
zero scheme times the parameter. The original section-cut maps and
their exterior maps agree on all four outer coordinates.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite AffineLineFiber AlgebraicCycle

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  (T : SmoothSite (Spec (.of k))) {P : Scheme.{u}}
  (p : P ⟶ X.left) (g : P ⟶ Y.left) (h : p ≫ X.hom = g ≫ Y.hom)

local notation3 (prettyPrint := false) "sP" => p ≫ X.hom
local notation3 (prettyPrint := false) "PT" => pullback sP T.hom
local notation3 (prettyPrint := false) "π" => pullback.fst sP T.hom
local notation3 (prettyPrint := false) "pT" => pullbackParameterExtensionMap p X.hom T.hom

/-- The actual target map of the cut support with the same external parameter. -/
def sectionCutExteriorTarget : PT ⟶ (product Y T).left :=
  (pullback.congrHom h rfl).hom ≫ pullbackParameterExtensionMap g Y.hom T.hom

local notation3 (prettyPrint := false) "gT" => sectionCutExteriorTarget T p g h

@[reassoc (attr := simp)]
theorem sectionCutExteriorTarget_fst :
    gT ≫ pullback.fst Y.hom T.hom = π ≫ g := by
  simp [sectionCutExteriorTarget, pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem sectionCutExteriorTarget_snd :
    gT ≫ pullback.snd Y.hom T.hom = pullback.snd sP T.hom := by
  simp [sectionCutExteriorTarget, pullback.congrHom_hom, pullback.map, Category.assoc]

/-- Both exterior projections have the same actual structure map. -/
theorem sectionCutExterior_base :
    pT ≫ (product X T).hom = gT ≫ (product Y T).hom := by
  simp only [product_hom, pullbackParameterExtensionMap_fst_assoc,
    sectionCutExteriorTarget_fst_assoc, h]

variable [GeometricallyIntegral T.hom] [IsNoetherian P]
  (s : Γ(P, ⊤))

local notation3 (prettyPrint := false) "f" => sectionToAffineLine sP s
local notation3 (prettyPrint := false) "Z" => fiber f 0
local notation3 (prettyPrint := false) "i" => inclusion f 0
local notation3 (prettyPrint := false) "sT" => (π).appTop s
local notation3 (prettyPrint := false) "fT" => sectionToAffineLine (pT ≫ (product X T).hom) sT
local notation3 (prettyPrint := false) "ZT" => fiber fT 0
local notation3 (prettyPrint := false) "iT" => inclusion fT 0
local notation3 (prettyPrint := false) "hT" => sectionCutExterior_base T p g h

set_option maxHeartbeats 800000 in
-- The full cut supports and their four projection equations use dependent pullback types.
/-- On the actual admissible cuts, adjoining a geometrically integral
smooth parameter preserves the full cut multiplicities. -/
theorem sectionCutCorrespondence_exterior
    [hf : IsFinite (i ≫ p)] [hfT : IsFinite (iT ≫ pT)]
    (hgen : ∀ x : genericPoints Z, (i ≫ p) x.val ∈ genericPoints X.left)
    (hgenT : ∀ x : genericPoints ZT, (iT ≫ pT) x.val ∈ genericPoints (product X T).left) :
    @sectionCutCorrespondence k _ (product X T) (product Y T) PT pT gT hT sT hfT hgenT =
      nativeExterior X Y T (@sectionCutCorrespondence k _ X Y P p g h s hf hgen) := by
  let m := sectionCutSupportMap (k := k) (X := X) (Y := Y) (P := P) p g h s
  let mT := sectionCutSupportMap (k := k) (X := product X T) (Y := product Y T) (P := PT)
    pT gT hT sT
  let B := pullback X.hom Y.hom
  let b : B ⟶ Spec (.of k) := pullback.fst X.hom Y.hom ≫ X.hom
  let bZ : Z ⟶ Spec (.of k) := m ≫ b
  let Z' := pullback bZ T.hom
  let πZ : Z' ⟶ Z := pullback.fst bZ T.hom
  let m' : Z' ⟶ pullback b T.hom := pullbackParameterExtensionMap m b T.hom
  let δ : pullback b T.hom ⟶ pullback (product X T).hom (product Y T).hom :=
    exteriorOuterDiagonal X Y T
  have hm₁ : m ≫ pullback.fst X.hom Y.hom = i ≫ p := sectionCutSupportMap_fst p g h s
  have hm₂ : m ≫ pullback.snd X.hom Y.hom = i ≫ g := sectionCutSupportMap_snd p g h s
  have hmT₁ : mT ≫ pullback.fst (product X T).hom (product Y T).hom = iT ≫ pT :=
    sectionCutSupportMap_fst (k := k) (X := product X T) (Y := product Y T) (P := PT)
      pT gT hT sT
  have hmT₂ : mT ≫ pullback.snd (product X T).hom (product Y T).hom = iT ≫ gT :=
    sectionCutSupportMap_snd (k := k) (X := product X T) (Y := product Y T) (P := PT)
      pT gT hT sT
  have hbase : pT ≫ (product X T).hom = π ≫ sP := by
    simp only [product_hom, pullbackParameterExtensionMap_fst_assoc]
  have hparam : π ≫ f = fT := by
    rw [← sectionToAffineLine_comp, hbase]
  have hZbase : bZ = i ≫ sP :=
    (Category.assoc m (pullback.fst X.hom Y.hom) X.hom).symm.trans
      ((congrArg (· ≫ X.hom) hm₁).trans (Category.assoc i p X.hom))
  let e₀ : Z' ≅ pullback (i ≫ sP) T.hom :=
    pullback.congrHom hZbase (rfl : T.hom = T.hom)
  let i' : pullback (i ≫ sP) T.hom ⟶ PT := pullbackParameterExtensionMap i sP T.hom
  have hsq :
      IsPullback i' (pullback.fst (i ≫ sP) T.hom ≫ pullback.fst (point (0 : k)) f)
        fT (point (0 : k)) := by
    simpa only [hparam] using
      (pullbackParameterExtension_isPullback i sP T.hom).paste_vert
        (IsPullback.of_hasPullback (point (0 : k)) f).flip
  let e₁ := hsq.flip.isoPullback
  let e : Z' ≅ ZT := e₀ ≪≫ e₁
  have he : e.hom ≫ iT = e₀.hom ≫ i' := by
    change (e₀.hom ≫ e₁.hom) ≫ pullback.snd (point (0 : k)) fT = _
    rw [Category.assoc, hsq.flip.isoPullback_hom_snd]
  have he₀₁ : e₀.hom ≫ pullback.fst (i ≫ sP) T.hom = πZ :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have he₀₂ : e₀.hom ≫ pullback.snd (i ≫ sP) T.hom = pullback.snd bZ T.hom :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hπ : e.hom ≫ iT ≫ π = πZ ≫ i := by
    rw [← Category.assoc, he, Category.assoc]
    have hi : i' ≫ π = pullback.fst (i ≫ sP) T.hom ≫ i :=
      pullbackParameterExtensionMap_fst i sP T.hom
    rw [hi, ← Category.assoc, he₀₁]
  have ht : e.hom ≫ iT ≫ pullback.snd sP T.hom = pullback.snd bZ T.hom := by
    rw [← Category.assoc, he, Category.assoc]
    have hi : i' ≫ pullback.snd sP T.hom = pullback.snd (i ≫ sP) T.hom :=
      pullbackParameterExtensionMap_snd i sP T.hom
    rw [hi, he₀₂]
  have hm'₁ : m' ≫ pullback.fst b T.hom = πZ ≫ m :=
    pullbackParameterExtensionMap_fst m b T.hom
  have hm'₂ : m' ≫ pullback.snd b T.hom = pullback.snd bZ T.hom :=
    pullbackParameterExtensionMap_snd m b T.hom
  let LX := pullback.fst (product X T).hom (product Y T).hom
  let LY := pullback.snd (product X T).hom (product Y T).hom
  let X₁ := pullback.fst X.hom T.hom
  let X₂ := pullback.snd X.hom T.hom
  let Y₁ := pullback.fst Y.hom T.hom
  let Y₂ := pullback.snd Y.hom T.hom
  have hδX : δ ≫ LX ≫ X₁ = pullback.fst b T.hom ≫ pullback.fst X.hom Y.hom :=
    ((Category.assoc δ LX X₁).symm.trans (pullback.lift_fst_assoc _ _ _ X₁)).trans
      (pullback.lift_fst _ _ _)
  have hδXT : δ ≫ LX ≫ X₂ = pullback.snd b T.hom :=
    ((Category.assoc δ LX X₂).symm.trans (pullback.lift_fst_assoc _ _ _ X₂)).trans
      (pullback.lift_snd _ _ _)
  have hδY : δ ≫ LY ≫ Y₁ = pullback.fst b T.hom ≫ pullback.snd X.hom Y.hom :=
    ((Category.assoc δ LY Y₁).symm.trans (pullback.lift_snd_assoc _ _ _ Y₁)).trans
      (pullback.lift_fst _ _ _)
  have hδYT : δ ≫ LY ≫ Y₂ = pullback.snd b T.hom :=
    ((Category.assoc δ LY Y₂).symm.trans (pullback.lift_snd_assoc _ _ _ Y₂)).trans
      (pullback.lift_snd _ _ _)
  have hp₁ : pT ≫ X₁ = π ≫ p := pullbackParameterExtensionMap_fst p X.hom T.hom
  have hp₂ : pT ≫ X₂ = pullback.snd sP T.hom :=
    pullbackParameterExtensionMap_snd p X.hom T.hom
  have hg₁ : gT ≫ Y₁ = π ≫ g := sectionCutExteriorTarget_fst T p g h
  have hg₂ : gT ≫ Y₂ = pullback.snd sP T.hom := sectionCutExteriorTarget_snd T p g h
  have hXL : e.hom ≫ mT ≫ LX = e.hom ≫ iT ≫ pT := by
    change e.hom ≫ (mT ≫ pullback.fst (product X T).hom (product Y T).hom) =
      e.hom ≫ (iT ≫ pT)
    exact congrArg (e.hom ≫ ·) hmT₁
  have hYL : e.hom ≫ mT ≫ LY = e.hom ≫ iT ≫ gT := by
    change e.hom ≫ (mT ≫ pullback.snd (product X T).hom (product Y T).hom) =
      e.hom ≫ (iT ≫ gT)
    exact congrArg (e.hom ≫ ·) hmT₂
  have houter : e.hom ≫ mT = m' ≫ δ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext («f» := X.hom) («g» := T.hom)
      · change ((e.hom ≫ mT) ≫ LX) ≫ X₁ = ((m' ≫ δ) ≫ LX) ≫ X₁
        calc
          _ = (e.hom ≫ mT ≫ LX) ≫ X₁ :=
            congrArg (· ≫ X₁) (Category.assoc e.hom mT LX)
          _ = (e.hom ≫ iT ≫ pT) ≫ X₁ := congrArg (· ≫ X₁) hXL
          _ = e.hom ≫ iT ≫ (pT ≫ X₁) := by simp only [Category.assoc]
          _ = e.hom ≫ iT ≫ (π ≫ p) :=
            congrArg (fun u : PT ⟶ X.left => e.hom ≫ iT ≫ u) hp₁
          _ = (e.hom ≫ iT ≫ π) ≫ p := by simp only [Category.assoc]
          _ = (πZ ≫ i) ≫ p := congrArg (· ≫ p) hπ
          _ = _ := by simp only [Category.assoc, hδX, reassoc_of% hm'₁, hm₁]
      · change ((e.hom ≫ mT) ≫ LX) ≫ X₂ = ((m' ≫ δ) ≫ LX) ≫ X₂
        calc
          _ = (e.hom ≫ mT ≫ LX) ≫ X₂ :=
            congrArg (· ≫ X₂) (Category.assoc e.hom mT LX)
          _ = (e.hom ≫ iT ≫ pT) ≫ X₂ := congrArg (· ≫ X₂) hXL
          _ = pullback.snd bZ T.hom := by simp only [Category.assoc, hp₂, ht]
          _ = _ := by simp only [Category.assoc, hδXT, hm'₂]
    · apply pullback.hom_ext («f» := Y.hom) («g» := T.hom)
      · change ((e.hom ≫ mT) ≫ LY) ≫ Y₁ = ((m' ≫ δ) ≫ LY) ≫ Y₁
        calc
          _ = (e.hom ≫ mT ≫ LY) ≫ Y₁ :=
            congrArg (· ≫ Y₁) (Category.assoc e.hom mT LY)
          _ = (e.hom ≫ iT ≫ gT) ≫ Y₁ := congrArg (· ≫ Y₁) hYL
          _ = e.hom ≫ iT ≫ (gT ≫ Y₁) := by simp only [Category.assoc]
          _ = e.hom ≫ iT ≫ (π ≫ g) :=
            congrArg (fun u : PT ⟶ Y.left => e.hom ≫ iT ≫ u) hg₁
          _ = (e.hom ≫ iT ≫ π) ≫ g := by simp only [Category.assoc]
          _ = (πZ ≫ i) ≫ g := congrArg (· ≫ g) hπ
          _ = _ := by simp only [Category.assoc, hδY, reassoc_of% hm'₁, hm₂]
      · change ((e.hom ≫ mT) ≫ LY) ≫ Y₂ = ((m' ≫ δ) ≫ LY) ≫ Y₂
        calc
          _ = (e.hom ≫ mT ≫ LY) ≫ Y₂ :=
            congrArg (· ≫ Y₂) (Category.assoc e.hom mT LY)
          _ = (e.hom ≫ iT ≫ gT) ≫ Y₂ := congrArg (· ≫ Y₂) hYL
          _ = pullback.snd bZ T.hom := by simp only [Category.assoc, hg₂, ht]
          _ = _ := by simp only [Category.assoc, hδYT, hm'₂]
  let : IsFinite m := sectionCutSupportMap_isFinite p g h s
  let : IsFinite mT := @sectionCutSupportMap_isFinite k _ (product X T) (product Y T) PT
    pT gT hT sT hfT
  let : IsNoetherian Z := isNoetherian_of_finiteType_of_isNoetherian (i ≫ p)
  let : IsNoetherian
      (pullback (product X T).hom (product Y T).hom : Scheme.{u}) :=
    inferInstanceAs (IsNoetherian (product (product X T) (product Y T)).left)
  let : IsNoetherian ZT := Scheme.isNoetherian_of_finiteType_of_isNoetherian mT
  let : IsFinite m' := isFinite_exteriorParameterSupportMap m b T.hom
  let : IsNoetherian Z' := isNoetherian_exteriorParameterSupport bZ T.hom
  let : IsFinite (m' ≫ δ) := MorphismProperty.comp_mem (@IsFinite) _ _
    (inferInstance : IsFinite m')
    (inferInstanceAs (IsFinite (exteriorOuterDiagonal X Y T)))
  have hadm (x : genericPoints Z) : IsFiniteCorrespondencePoint X.hom Y.hom (m x.val) := by
    apply isFiniteCorrespondencePoint_finiteMap X.hom Y.hom m x.val
    · rw [Category.assoc, hm₁]
      exact MorphismProperty.comp_mem (@IsFinite) _ _
        (inferInstance : IsFinite (integralComponentAt x.val).subschemeι) hf
    · rw [Category.assoc, hm₁]
      exact range_integralComponentAt_mem_irreducibleComponents_of_image_generic (i ≫ p)
        x.val (hgen x)
  apply Subtype.ext
  calc
    _ = finiteCyclePushforward mT (fundamentalCycle ZT) :=
      sectionCutCorrespondence_val (k := k) (X := product X T) (Y := product Y T) (P := PT)
        pT gT hT sT hgenT
    _ = finiteCyclePushforward mT (finiteCyclePushforward e.hom (fundamentalCycle Z')) :=
      congrArg (finiteCyclePushforward mT) (finiteCyclePushforward_fundamentalCycle_iso e).symm
    _ = finiteCyclePushforward (e.hom ≫ mT) (fundamentalCycle Z') :=
      finiteCyclePushforward_comp_apply e.hom mT _
    _ = finiteCyclePushforward (m' ≫ δ) (fundamentalCycle Z') :=
      DFunLike.congr_fun (finiteCyclePushforward_congr _ _ houter) _
    _ = nativeExteriorFiniteSupportPushforward X Y T m :=
      (nativeExteriorFiniteSupportPushforward_eq X Y T m).symm
    _ = _ := (nativeExterior_val_eq_fundamentalCycle_of_finite_support X Y T m
      (sectionCutCorrespondence p g h s hgen)
      (sectionCutCorrespondence_val p g h s hgen) hadm).symm

end AlgebraicGeometry.Cor
