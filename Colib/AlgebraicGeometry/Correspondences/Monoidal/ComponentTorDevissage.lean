/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ComponentIncidences
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Stalks

/-!
# Dévissage of the whole exterior-incidence coefficient by support pairs

Each minimal component of the whole support product projects to exactly one
generic pair. Group the Koszul dévissage by those pairs. Each group is the
native Tor Euler coefficient of the corresponding actual incidence when the
point occurs in it.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped BigOperators

universe u

namespace Stacks.Chow

set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k] [PerfectField k]
  (X Y Z U V W : SmoothSite (Spec (.of k)))
  (a : pullback (C := Scheme) X.hom Y.hom)
  (b : pullback (C := Scheme) Y.hom Z.hom)
  (c : pullback (C := Scheme) U.hom V.hom)
  (d : pullback (C := Scheme) V.hom W.hom)
  (ha : IsFiniteCorrespondencePoint X.hom Y.hom a)
  (hb : IsFiniteCorrespondencePoint Y.hom Z.hom b)
  (hc : IsFiniteCorrespondencePoint U.hom V.hom c)
  (hd : IsFiniteCorrespondencePoint V.hom W.hom d)

local notation "D₁" =>
  correspondenceExteriorSupport X Y U V (integralComponentAt a) (integralComponentAt c)
local notation "D₂" =>
  correspondenceExteriorSupport Y Z V W (integralComponentAt b) (integralComponentAt d)
local notation "H" => correspondenceExteriorWholeIncidence X Y Z U V W a b c d
local notation "i" => correspondenceExteriorWholeIncidenceInclusion X Y Z U V W a b c d
local notation "P" => correspondenceExteriorWholeSupportProduct X Y Z U V W a b c d
local notation "leftTarget" => correspondenceExteriorTarget X Y U V (integralComponentAt a)
  (integralComponentAt c)
local notation "rightSource" => correspondenceExteriorSource Y Z V W (integralComponentAt b)
  (integralComponentAt d)
local notation "q" => correspondenceExteriorWholeIncidenceToSupport X Y Z U V W a b c d
local notation "kP" => correspondenceExteriorWholeSupportInclusion X Y Z U V W a b c d
local notation "sq" => correspondenceExteriorWholeIncidence_isPullback X Y Z U V W a b c d
set_option quotPrecheck false in
local notation "f" => (SmoothSite.product X U).hom
set_option quotPrecheck false in
local notation "g" => (SmoothSite.product Y V).hom
set_option quotPrecheck false in
local notation "h" => (SmoothSite.product Z W).hom
local notation "δ" => correspondenceTripleInclusion f g h
local notation "T₀" => correspondenceIntersectionAmbient f g h

variable (z : genericPoints (correspondenceExteriorWholeIncidence X Y Z U V W a b c d))

set_option quotPrecheck false in
local notation "pt" => δ (i z.val)
set_option quotPrecheck false in
local notation "p" => q z.val
local notation "ρ" => cartesianIntersectionGenericStalkMap sq z
set_option quotPrecheck false in
local notation "σ" => ((δ).stalkMap (i z.val)).hom
set_option quotPrecheck false in
local notation "All" => {η : genericPoints P // η.val ⤳ p}
set_option quotPrecheck false in
local notation "labels" => fun (η : All) =>
  (exteriorWholeSupportFirstGeneric X Y Z U V W a b c d η.val,
    exteriorWholeSupportSecondGeneric X Y Z U V W a b c d η.val)

set_option quotPrecheck false in
local notation "term" => fun (η : All) =>
  structureTorCoefficient (((integralComponentAt η.val.val).subschemeι.stalkMap
    (genericSupportComponentPoint p η)).hom.comp ρ) σ

variable
  (α : genericPoints (correspondenceExteriorSupport X Y U V
    (integralComponentAt a) (integralComponentAt c)))
  (β : genericPoints (correspondenceExteriorSupport Y Z V W
    (integralComponentAt b) (integralComponentAt d)))

local notation "j₁" => leftComponentPoint X Y U V a c α
local notation "j₂" => rightComponentPoint Y Z V W b d β
local notation "L" => correspondenceIncidence f g h j₁ j₂
local notation "P'" => correspondenceSupportProduct f g h j₁ j₂
local notation "m" => exteriorComponentIncidenceMap X Y Z U V W a b c d ha hb hc hd α β
local notation "w" => exteriorComponentSupportMap X Y Z U V W a b c d ha hb hc hd α β
local notation "q'" => correspondenceIncidenceToSupportProduct f g h j₁ j₂
local notation "i'" => correspondenceIncidenceInclusion f g h j₁ j₂
local notation "kP'" => correspondenceSupportProductInclusion f g h j₁ j₂

omit [PerfectField k] in
private theorem exists_mem_componentIncidence_iff :
    z.val ∈ Set.range m ↔ p ∈ Set.range w := by
  rw [range_exteriorComponentIncidenceMap, range_exteriorComponentSupportMap]
  have hfst : q ≫ pullback.fst (leftTarget ≫ g) (rightSource ≫ g) =
      pullback.fst leftTarget rightSource :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hsnd : q ≫ pullback.snd (leftTarget ≫ g) (rightSource ≫ g) =
      pullback.snd leftTarget rightSource :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have h₁ := congrArg (fun o : H ⟶ D₁ => o z.val) hfst
  have h₂ := congrArg (fun o : H ⟶ D₂ => o z.val) hsnd
  simpa only [Set.mem_inter_iff, Set.mem_preimage, Scheme.Hom.comp_apply] using
    and_congr (iff_of_eq (congrArg (· ∈ closure ({α.val} : Set D₁)) h₁.symm))
      (iff_of_eq (congrArg (· ∈ closure ({β.val} : Set D₂)) h₂.symm))

private def componentGenericThroughEquiv
    (z' : genericPoints L) (hz' : m z'.val = z.val) :
    {η : genericPoints P' // η.val ⤳ q' z'.val} ≃
      {η : All // labels η = (α, β)} := by
  let rw₀ : w (q' z'.val) = p := by
    rw [← Scheme.Hom.comp_apply, ← exteriorComponentIncidenceMap_support,
      Scheme.Hom.comp_apply, hz']
  refine Equiv.ofBijective (fun ξ => ?_) ?_
  · let η : genericPoints P :=
      ⟨w ξ.val.val, (exteriorComponentSupportGeneric_iff
        X Y Z U V W a b c d ha hb hc hd α β _).1 ξ.val.property⟩
    let hη : η.val ⤳ p := rw₀ ▸ ξ.property.map (w).continuous
    refine ⟨⟨η, hη⟩, Prod.ext ?_ ?_⟩
    · exact ((exteriorWholeSupportGeneric_component_iff
        X Y Z U V W a b c d ha hb hc hd α β η).1 (Set.mem_range_self _)).1
    · exact ((exteriorWholeSupportGeneric_component_iff
        X Y Z U V W a b c d ha hb hc hd α β η).1 (Set.mem_range_self _)).2
  · constructor
    · intro ξ ξ' hη
      apply Subtype.ext
      apply Subtype.ext
      apply (w).isClosedEmbedding.injective
      exact congrArg (fun η : {η : All // labels η = (α, β)} => η.val.val.val) hη
    · intro η
      have hw : η.val.val.val ∈ Set.range w :=
        (exteriorWholeSupportGeneric_component_iff
          X Y Z U V W a b c d ha hb hc hd α β η.val.val).2
            ⟨congrArg Prod.fst η.property, congrArg Prod.snd η.property⟩
      obtain ⟨ξ, hξ⟩ := hw
      refine ⟨⟨⟨ξ, (exteriorComponentSupportGeneric_iff
        X Y Z U V W a b c d ha hb hc hd α β ξ).2 (hξ ▸ η.val.val.property)⟩, ?_⟩, ?_⟩
      · exact (w).isClosedEmbedding.isInducing.specializes_iff.mp
          (hξ.symm ▸ rw₀.symm ▸ η.val.property)
      · apply Subtype.ext
        apply Subtype.ext
        exact Subtype.ext hξ

private theorem transportedClosedStalkMap_comp
    {A B C : Scheme.{u}} (f' : A ⟶ B) (g' : B ⟶ C) (y : A) (p' : C)
    (hp : p' = g' (f' y)) :
    transportedClosedStalkMap (f' ≫ g') y p' (hp.trans (Scheme.Hom.comp_apply f' g' y).symm) =
      (f'.stalkMap y).hom.comp (transportedClosedStalkMap g' (f' y) p' hp) := by
  let transport := (C.presheaf.stalkCongr (.of_eq hp)).hom
  have he : transport ≫ (f' ≫ g').stalkMap y =
      (transport ≫ g'.stalkMap (f' y)) ≫ f'.stalkMap y :=
    (congrArg (transport ≫ ·) (Scheme.Hom.stalkMap_comp f' g' y)).trans
      (Category.assoc _ _ _).symm
  exact congrArg CommRingCat.Hom.hom he

private theorem transportedClosedStalkMap_congr_same_ambient
    {A B T : Scheme.{u}} (a₀ : A ⟶ T) (b₀ : B ⟶ T)
    (e : B ≅ A) (he : e.hom ≫ a₀ = b₀) (x : A) (y : B) (hxy : x = e.hom y)
    (y₀ y₁ : T) (hp : y₀ = a₀ x) (hp' : y₁ = b₀ y) (hpp' : y₀ = y₁) :
    ((A.presheaf.stalkCongr (.of_eq hxy)).hom ≫ e.hom.stalkMap y).hom.comp
      (transportedClosedStalkMap a₀ x y₀ hp) =
    (transportedClosedStalkMap b₀ y y₁ hp').comp
      (T.presheaf.stalkCongr (.of_eq hpp')).hom.hom := by
  subst x y₀ y₁
  simp only [transportedClosedStalkMap, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  have hmap := Scheme.Hom.stalkMap_congr_hom (e.hom ≫ a₀) b₀ he y
  rw [Scheme.Hom.stalkMap_comp] at hmap
  let transport := (T.presheaf.stalkCongr (.of_eq hp)).hom
  have hcancel : transport ≫ (T.presheaf.stalkCongr (.of_eq hp.symm)).hom = 𝟙 _ := by
    change (T.presheaf.stalkSpecializes (specializes_of_eq hp.symm) ≫
      T.presheaf.stalkSpecializes (specializes_of_eq hp)) = 𝟙 _
    exact (TopCat.Presheaf.stalkSpecializes_comp T.presheaf
      (specializes_of_eq hp) (specializes_of_eq hp.symm)).trans
        (TopCat.Presheaf.stalkSpecializes_refl _ _)
  have hfinal : (transport ≫ a₀.stalkMap (e.hom y)) ≫ e.hom.stalkMap y = b₀.stalkMap y :=
    (Category.assoc _ _ _).trans
      ((congrArg (transport ≫ ·) hmap).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ b₀.stalkMap y) hcancel).trans (Category.id_comp _))))
  exact congrArg CommRingCat.Hom.hom hfinal

set_option maxHeartbeats 700000 in
-- Comparing the stalk maps unfolds both of the displayed incidence diagrams.
omit [PerfectField k] in
private theorem componentTorTerm_eq
    (z' : genericPoints L) (hz' : m z'.val = z.val)
    (ξ : {η : genericPoints P' // η.val ⤳ q' z'.val}) :
    let η := (componentGenericThroughEquiv X Y Z U V W a b c d ha hb hc hd z α β z' hz') ξ
    let sq' := (isPullback_correspondenceAmbientIncidence f g h j₁ j₂).flip
    let ρ' := cartesianIntersectionGenericStalkMap sq' z'
    let σ' := ((δ).stalkMap (i' z'.val)).hom
    term η.val = structureTorCoefficient
      ((((integralComponentAt ξ.val.val).subschemeι).stalkMap
        (genericSupportComponentPoint (q' z'.val) ξ)).hom.comp ρ') σ' := by
  let η := (componentGenericThroughEquiv X Y Z U V W a b c d ha hb hc hd z α β z' hz') ξ
  let A₀ := integralComponentAt η.val.val.val
  let B₀ := integralComponentAt ξ.val.val
  let X₀ := genericSupportComponentPoint p η.val
  let Y₀ := genericSupportComponentPoint (q' z'.val) ξ
  let sq' := (isPullback_correspondenceAmbientIncidence f g h j₁ j₂).flip
  have hT : i' z'.val = i z.val := by
    have he := exteriorComponentIncidenceMap_inclusion X Y Z U V W a b c d ha hb hc hd α β
    simpa only [Scheme.Hom.comp_apply, hz'] using
      congrArg (fun t : L ⟶ correspondenceTripleProduct f g h => t z'.val) he.symm
  have hP : w (q' z'.val) = p := by
    rw [← Scheme.Hom.comp_apply, ← exteriorComponentIncidenceMap_support,
      Scheme.Hom.comp_apply, hz']
  have hX : A₀.subschemeι X₀ = p := rfl
  have hY : B₀.subschemeι Y₀ = q' z'.val := rfl
  obtain ⟨e, he⟩ : ∃ e : B₀.subscheme ≅ A₀.subscheme,
      e.hom ≫ A₀.subschemeι = B₀.subschemeι ≫ w :=
    exteriorComponentSupportMap_closureIso X Y Z U V W a b c d ha hb hc hd α β ξ.val
  have hXY : e.hom Y₀ = X₀ := by
    apply A₀.subschemeι.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply, hY, hP, hX]
  have hcomp : e.hom ≫ (A₀.subschemeι ≫ kP) = B₀.subschemeι ≫ kP' := by
    rw [← Category.assoc, he, Category.assoc, exteriorComponentSupportMap_inclusion]
  -- Both composites are the original support stalk map followed by its component quotient.
  let h₀ : pt = (A₀.subschemeι ≫ kP) X₀ := by
    rw [Scheme.Hom.comp_apply, hX]
    exact cartesianIntersection_genericPoint_eq sq z
  let h₁ : δ (i' z'.val) = (B₀.subschemeι ≫ kP') Y₀ := by
    rw [Scheme.Hom.comp_apply, hY]
    exact cartesianIntersection_genericPoint_eq sq' z'
  let e₀ : A₀.subscheme.presheaf.stalk X₀ ≅ B₀.subscheme.presheaf.stalk Y₀ :=
    A₀.subscheme.presheaf.stalkCongr (.of_eq hXY.symm) ≪≫ asIso (e.hom.stalkMap Y₀)
  let e₁ := (T₀).presheaf.stalkCongr
    (.of_eq (congrArg δ hT.symm))
  let e₂ := (correspondenceTripleProduct f g h).presheaf.stalkCongr (.of_eq hT.symm)
  let ρ₀ := transportedClosedStalkMap (A₀.subschemeι ≫ kP) X₀ pt h₀
  let ρ₁ := transportedClosedStalkMap (B₀.subschemeι ≫ kP') Y₀ (δ (i' z'.val)) h₁
  have hcoeff := structureTorCoefficient_eq_of_ringEquiv
    ρ₀ σ ρ₁ ((δ).stalkMap (i' z'.val)).hom
    e₁.commRingCatIsoToRingEquiv e₀.commRingCatIsoToRingEquiv e₂.commRingCatIsoToRingEquiv
    (transportedClosedStalkMap_congr_same_ambient _ _ e hcomp X₀ Y₀ hXY.symm
      pt (δ (i' z'.val)) h₀ h₁ (congrArg δ hT.symm))
    (congrArg CommRingCat.Hom.hom
      (Scheme.Hom.stalkMap_congr_point δ (i z.val) (i' z'.val) hT.symm))
  have hρ₀ : ρ₀ = (A₀.subschemeι.stalkMap X₀).hom.comp ρ :=
    transportedClosedStalkMap_comp A₀.subschemeι kP X₀ pt
      (cartesianIntersection_genericPoint_eq sq z)
  have hρ₁ : ρ₁ = (B₀.subschemeι.stalkMap Y₀).hom.comp
      (cartesianIntersectionGenericStalkMap sq' z') :=
    transportedClosedStalkMap_comp B₀.subschemeι kP' Y₀ (δ (i' z'.val))
      (cartesianIntersection_genericPoint_eq sq' z')
  rw [hρ₀, hρ₁] at hcoeff
  exact hcoeff

/-- The fibre over a generic whole-incidence point carries the original component Tor
coefficient. An empty fibre contributes zero. -/
def exteriorComponentTorCoefficientAt : ℤ :=
  ∑ᶠ z' : {z' : genericPoints L // m z'.val = z.val},
    correspondenceIncidenceTorCoefficient k f g h j₁ j₂ z'.val

omit [PerfectField k] in
private theorem incidenceCoefficient_eq_stalk {A B C : Scheme.{u}}
    (f' : A ⟶ Spec (.of k)) (g' : B ⟶ Spec (.of k)) (h' : C ⟶ Spec (.of k))
    (x : pullback (C := Scheme) f' g') (y : pullback (C := Scheme) g' h')
    (v : genericPoints (correspondenceIncidence f' g' h' x y)) :
    correspondenceIncidenceTorCoefficient k f' g' h' x y v =
      structureTorCoefficient
        (cartesianIntersectionGenericStalkMap
          (isPullback_correspondenceAmbientIncidence f' g' h' x y).flip v)
        ((correspondenceTripleInclusion f' g' h').stalkMap
          (correspondenceIncidenceInclusion f' g' h' x y v.val)).hom := rfl

set_option maxHeartbeats 1400000 in
-- The scalar presentations and generic fibres are all those of the actual closed maps.
private theorem componentCoefficient_eq_finsum_support :
    exteriorComponentTorCoefficientAt X Y Z U V W a b c d ha hb hc hd z α β =
      ∑ᶠ η : {η : All // labels η = (α, β)}, term η.val := by
  classical
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  by_cases hz : z.val ∈ Set.range m
  · obtain ⟨z₀, hz₀⟩ := hz
    let z' : genericPoints L := ⟨z₀, mem_genericPoints_of_isFinite_image m z₀
      (hz₀.symm ▸ z.property)⟩
    rw [exteriorComponentTorCoefficientAt, finsum_eq_single _ ⟨z', hz₀⟩]
    · let e := componentGenericThroughEquiv X Y Z U V W a b c d ha hb hc hd z α β z' hz₀
      rw [← finsum_comp_equiv e]
      let sq' := (isPullback_correspondenceAmbientIncidence f g h j₁ j₂).flip
      let : IsLocallyNoetherian T₀ :=
        isLocallyNoetherian_correspondenceIntersectionAmbient (S := Spec (.of k)) f g h
      let : IsLocallyNoetherian P' := LocallyOfFiniteType.isLocallyNoetherian kP'
      let : IsReduced P' :=
        isReduced_exteriorComponentSupportProduct X Y Z U V W a b c d α β
      obtain ⟨_, l, hl, hl'⟩ :=
        exists_correspondenceTripleInclusion_regularList X Y Z U V W (i' z'.val)
      have hχ := structureTorCoefficient_eq_finsum_cartesianIntersectionComponents sq' z' l hl hl'
      rw [incidenceCoefficient_eq_stalk f g h j₁ j₂ z', hχ]
      refine finsum_congr fun ξ => ?_
      let := (isField_stalk_of_closure_mem_irreducibleComponents P'
        ξ.val.val ξ.val.property).toField
      have hlen :
          Module.length ((P').presheaf.stalk ξ.val.val) ((P').presheaf.stalk ξ.val.val) = 1 :=
        Module.length_eq_one_iff.mpr inferInstance
      rw [hlen, ENat.toNat_one, Nat.cast_one, one_mul]
      exact (componentTorTerm_eq X Y Z U V W a b c d ha hb hc hd z α β z' hz₀ ξ).symm
    · intro t ht
      exfalso
      exact ht (Subtype.ext (Subtype.ext
        ((m).isClosedEmbedding.injective (t.property.trans hz₀.symm))))
  · rw [exteriorComponentTorCoefficientAt]
    have : IsEmpty {z' : genericPoints L // m z'.val = z.val} :=
      ⟨fun t => hz ⟨t.val.val, t.property⟩⟩
    have : IsEmpty {η : All // labels η = (α, β)} := ⟨fun η => by
      have hd' : η.val.val.val ∈ Set.range w :=
        (exteriorWholeSupportGeneric_component_iff
          X Y Z U V W a b c d ha hb hc hd α β η.val.val).2
            ⟨congrArg Prod.fst η.property, congrArg Prod.snd η.property⟩
      exact hz ((exists_mem_componentIncidence_iff X Y Z U V W a b c d ha hb hc hd z α β).2
        (η.val.property.mem_closed (w).isClosedEmbedding.isClosed_range hd'))⟩
    rw [finsum_of_isEmpty, finsum_of_isEmpty]

set_option maxHeartbeats 1400000 in
omit [PerfectField k] in
/-- The component coefficient carries both input generic multiplicities. Their product
converts the component-support weight into the actual whole-support weight. -/
private theorem weighted_componentCoefficient_eq_finsum_support :
    ((Module.length ((D₁).presheaf.stalk α.val) ((D₁).presheaf.stalk α.val)).toNat : ℤ) *
      ((Module.length ((D₂).presheaf.stalk β.val) ((D₂).presheaf.stalk β.val)).toNat : ℤ) *
    exteriorComponentTorCoefficientAt X Y Z U V W a b c d ha hb hc hd z α β =
      ∑ᶠ η : {η : All // labels η = (α, β)},
        ((Module.length ((P).presheaf.stalk η.val.val.val)
          ((P).presheaf.stalk η.val.val.val)).toNat : ℤ) * term η.val := by
  classical
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt a)) := ha.1
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt c)) := hc.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  by_cases hz : z.val ∈ Set.range m
  · obtain ⟨z₀, hz₀⟩ := hz
    let z' : genericPoints L := ⟨z₀, mem_genericPoints_of_isFinite_image m z₀
      (hz₀.symm ▸ z.property)⟩
    rw [exteriorComponentTorCoefficientAt, finsum_eq_single _ ⟨z', hz₀⟩]
    · let e := componentGenericThroughEquiv X Y Z U V W a b c d ha hb hc hd z α β z' hz₀
      rw [← finsum_comp_equiv e]
      let sq' := (isPullback_correspondenceAmbientIncidence f g h j₁ j₂).flip
      let : IsLocallyNoetherian T₀ :=
        isLocallyNoetherian_correspondenceIntersectionAmbient (S := Spec (.of k)) f g h
      let : IsLocallyNoetherian P' := LocallyOfFiniteType.isLocallyNoetherian kP'
      obtain ⟨_, l, hl, hl'⟩ :=
        exists_correspondenceTripleInclusion_regularList X Y Z U V W (i' z'.val)
      have hχ := structureTorCoefficient_eq_finsum_cartesianIntersectionComponents sq' z' l hl hl'
      rw [incidenceCoefficient_eq_stalk f g h j₁ j₂ z', hχ, mul_finsum]
      refine finsum_congr fun ξ => ?_
      have hlen := length_stalk_exteriorWholeSupport_eq_mul_component
        X Y Z U V W a b c d ha hb hc hd α β ξ.val
      change _ = ((Module.length ((P).presheaf.stalk (w ξ.val.val))
        ((P).presheaf.stalk (w ξ.val.val))).toNat : ℤ) * term (e ξ).val
      rw [hlen]
      simp only [ENat.toNat_mul, Nat.cast_mul]
      rw [componentTorTerm_eq X Y Z U V W a b c d ha hb hc hd z α β z' hz₀ ξ]
      ring
    · intro t ht
      exfalso
      exact ht (Subtype.ext (Subtype.ext
        ((m).isClosedEmbedding.injective (t.property.trans hz₀.symm))))
  · rw [exteriorComponentTorCoefficientAt]
    have : IsEmpty {z' : genericPoints L // m z'.val = z.val} :=
      ⟨fun t => hz ⟨t.val.val, t.property⟩⟩
    have : IsEmpty {η : All // labels η = (α, β)} := ⟨fun η => by
      have hd' : η.val.val.val ∈ Set.range w :=
        (exteriorWholeSupportGeneric_component_iff
          X Y Z U V W a b c d ha hb hc hd α β η.val.val).2
            ⟨congrArg Prod.fst η.property, congrArg Prod.snd η.property⟩
      exact hz ((exists_mem_componentIncidence_iff X Y Z U V W a b c d ha hb hc hd z α β).2
        (η.val.property.mem_closed (w).isClosedEmbedding.isClosed_range hd'))⟩
    rw [finsum_of_isEmpty, finsum_of_isEmpty, mul_zero]

omit α β [PerfectField k] in
/-- Group the whole-incidence dévissage by its actual pair of generic support labels,
retaining every whole-support generic length. This regrouping holds over an arbitrary field. -/
theorem structureTorCoefficient_eq_sum_weighted_genericPairs :
    letI := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
    letI := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
    structureTorCoefficient ρ σ =
      ∑ t : genericPoints D₁ × genericPoints D₂,
        ∑ᶠ η : {η : All // labels η = t},
          ((Module.length ((P).presheaf.stalk η.val.val.val)
            ((P).presheaf.stalk η.val.val.val)).toNat : ℤ) * term η.val := by
  classical
  let := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
  let := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
  rw [structureTorCoefficient_exteriorWhole_eq_finsum_genericComponents X Y Z U V W a b c d
    ha hb hc hd z]
  let l := correspondenceExteriorTarget X Y U V (integralComponentAt a) (integralComponentAt c)
  let r := correspondenceExteriorSource Y Z V W (integralComponentAt b) (integralComponentAt d)
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  let : IsFinite r := correspondenceExteriorSource_isFinite Y Z V W
    (integralComponentAt b) (integralComponentAt d)
  let : LocallyOfFiniteType (r ≫ g) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  let : IsNoetherian P :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian
      (pullback.fst (l ≫ g) (r ≫ g))
  let : Fintype (genericPoints P) :=
    (AlgebraicCycle.fundamentalCycle_genericPoints_finite P).fintype
  let : Fintype All := Fintype.ofFinite All
  let : ∀ t : genericPoints D₁ × genericPoints D₂, Fintype {η : All // labels η = t} :=
    fun _ => Fintype.ofFinite _
  let F : All → ℤ := fun η =>
    ((Module.length ((P).presheaf.stalk η.val.val)
      ((P).presheaf.stalk η.val.val)).toNat : ℤ) * term η
  change (∑ᶠ η : All, F η) =
    ∑ t : genericPoints D₁ × genericPoints D₂, ∑ᶠ η : {η : All // labels η = t}, F η.val
  simp only [finsum_eq_sum_of_fintype]
  exact (Fintype.sum_equiv (Equiv.sigmaFiberEquiv labels).symm F
    (fun t => F t.2.val) (fun _ => rfl)).trans (Fintype.sum_sigma _)

omit α β [PerfectField k] in
/-- Over an arbitrary field, the whole Tor coefficient is the sum of the native component
incidence coefficients weighted by both input generic multiplicities. -/
theorem structureTorCoefficient_eq_sum_weighted_componentIncidences :
    letI := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
    letI := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
    structureTorCoefficient ρ σ =
      ∑ α : genericPoints D₁, ∑ β : genericPoints D₂,
        ((Module.length ((D₁).presheaf.stalk α.val) ((D₁).presheaf.stalk α.val)).toNat : ℤ) *
          ((Module.length ((D₂).presheaf.stalk β.val) ((D₂).presheaf.stalk β.val)).toNat : ℤ) *
            exteriorComponentTorCoefficientAt X Y Z U V W a b c d ha hb hc hd z α β := by
  classical
  let := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
  let := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
  rw [structureTorCoefficient_eq_sum_weighted_genericPairs X Y Z U V W a b c d
    ha hb hc hd z]
  rw [← Fintype.sum_prod_type' (fun α β =>
    ((Module.length ((D₁).presheaf.stalk α.val) ((D₁).presheaf.stalk α.val)).toNat : ℤ) *
      ((Module.length ((D₂).presheaf.stalk β.val) ((D₂).presheaf.stalk β.val)).toNat : ℤ) *
        exteriorComponentTorCoefficientAt X Y Z U V W a b c d ha hb hc hd z α β)]
  apply Finset.sum_congr rfl
  intro t _
  exact (weighted_componentCoefficient_eq_finsum_support X Y Z U V W a b c d
    ha hb hc hd z t.1 t.2).symm

omit α β in
/-- The whole local Tor coefficient is the sum over the actual native component incidences.
The local product-support multiplicities are one over the perfect field. -/
theorem structureTorCoefficient_eq_sum_componentIncidences :
    letI := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
    letI := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
    structureTorCoefficient ρ σ =
      ∑ α : genericPoints D₁, ∑ β : genericPoints D₂,
        exteriorComponentTorCoefficientAt X Y Z U V W a b c d ha hb hc hd z α β := by
  classical
  let := correspondenceExteriorSupport_isNoetherian X Y U V a c ha hc
  let := correspondenceExteriorSupport_isNoetherian Y Z V W b d hb hd
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₁).fintype
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D₂).fintype
  rw [structureTorCoefficient_exteriorWhole_eq_finsum_genericComponents X Y Z U V W a b c d
    ha hb hc hd z]
  have hterm : (∑ᶠ η : All,
      ((Module.length ((P).presheaf.stalk η.val.val) ((P).presheaf.stalk η.val.val)).toNat : ℤ) *
        term η) = ∑ᶠ η : All, term η := by
    refine finsum_congr fun η => ?_
    rw [length_stalk_correspondenceExteriorWholeSupportProduct X Y Z U V W a b c d η.val,
      ENat.toNat_one, Nat.cast_one, one_mul]
  rw [hterm, ← Fintype.sum_prod_type' (fun α β =>
    exteriorComponentTorCoefficientAt X Y Z U V W a b c d ha hb hc hd z α β)]
  let l := correspondenceExteriorTarget X Y U V (integralComponentAt a) (integralComponentAt c)
  let r := correspondenceExteriorSource Y Z V W (integralComponentAt b) (integralComponentAt d)
  let : IsFinite (exteriorSupportSourceProjection Y Z (integralComponentAt b)) := hb.1
  let : IsFinite (exteriorSupportSourceProjection V W (integralComponentAt d)) := hd.1
  let : IsFinite r := correspondenceExteriorSource_isFinite Y Z V W
    (integralComponentAt b) (integralComponentAt d)
  let : LocallyOfFiniteType (r ≫ g) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  let : IsNoetherian P :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian
      (pullback.fst (l ≫ g) (r ≫ g))
  let : Fintype (genericPoints P) :=
    (AlgebraicCycle.fundamentalCycle_genericPoints_finite P).fintype
  let : Fintype All := Fintype.ofFinite All
  let : ∀ t : genericPoints D₁ × genericPoints D₂, Fintype {η : All // labels η = t} :=
    fun _ => Fintype.ofFinite _
  calc
    _ = ∑ η : All, term η := finsum_eq_sum_of_fintype _
    _ = ∑ t : genericPoints D₁ × genericPoints D₂, ∑ η : {η : All // labels η = t},
        term η.val := by
      let F : (Σ t : genericPoints D₁ × genericPoints D₂, {η : All // labels η = t}) → ℤ :=
        fun t => term t.2.val
      exact (Fintype.sum_equiv (Equiv.sigmaFiberEquiv labels).symm term F
        (fun _ => rfl)).trans (Fintype.sum_sigma F)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      exact (finsum_eq_sum_of_fintype _).symm.trans
        (componentCoefficient_eq_finsum_support X Y Z U V W a b c d ha hb hc hd
          z t.1 t.2).symm

end Stacks.Chow
