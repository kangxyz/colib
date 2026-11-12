/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.CartierNormRatio
public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.ChartFrames
public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.RatioGerm
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionCoefficient

/-!
# Principal cycles of norms of section ratios

The principal cycle of a ratio of section norms is the finite pushforward
of the difference of the original zero cycles, minus the corresponding
target difference. On each original affine chart the norm is the determinant
and the comparison uses the full Cartier ideals of the four sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.Chow Stacks.Divisors Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme

open RelativeCurvePencil

private theorem functionFieldMap_germToFunctionField_open {Y : Scheme.{u}} [IsIntegral Y]
    (U : Y.Opens) [Nonempty U] (r : Γ(Y, U)) :
    letI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.1 ‹_›))
    letI : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨genericPoint U.toScheme, trivial⟩⟩
    dominantFunctionFieldMap U.ι (Y.germToFunctionField U r) =
      U.toScheme.germToFunctionField ⊤ (U.topIso.inv r) := by
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.1 ‹_›))
  let : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨genericPoint U.toScheme, trivial⟩⟩
  have happ : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact congrArg Y.presheaf.map (Subsingleton.elim _ _)
  rw [dominantFunctionFieldMap_germToFunctionField_of_mem U.ι (genericPoint U.toScheme) U
    (genericPoint U.toScheme).2 ⊤ trivial (by simp) r, happ]

private theorem frameCoordinate_mul_of_sectionRatio {X W U Z : Scheme.{u}}
    (i : W ⟶ X) (j : U ⟶ X) (v : Z ⟶ W) (u' : Z ⟶ U) (h : v ≫ i = u' ≫ j)
    (L : X.Modules) [IsInvertibleModule X L] (a b : Γ(L, ⊤))
    (e : (Modules.pullback i).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
    (ha : zeroScheme U ((Modules.pullback j).obj L) (pullbackGlobalSections j L a) = ⊤) :
    let c := sectionRatioCoefficient ((Modules.pullback j).obj L)
      (pullbackGlobalSections j L a) (pullbackGlobalSections j L b) ha
    let a₀ : Γ(W, ⊤) := e.hom.app ⊤ (pullbackGlobalSections i L a)
    let b₀ : Γ(W, ⊤) := e.hom.app ⊤ (pullbackGlobalSections i L b)
    u'.appTop c * v.appTop a₀ = v.appTop b₀ := by
  dsimp only
  let c := sectionRatioCoefficient ((Modules.pullback j).obj L)
    (pullbackGlobalSections j L a) (pullbackGlobalSections j L b) ha
  have hab : pullbackGlobalSections j L b = c • pullbackGlobalSections j L a :=
    (sectionRatioCoefficient_smul_eq _ _ _ ha).symm
  have hz := congrArg (fun x ↦ (Modules.framePullback v e).hom.app ⊤ x)
    (boundary_smul_identity_after_sourceChange i j v u' h L b a c hab)
  rw [Modules.Hom.app_smul, Modules.framePullback_coordinate,
    Modules.framePullback_coordinate] at hz
  exact hz.symm

/-- The divisor of the regular unit on the actual good domain, read in the
function field, has the original four section cycles with their signs. -/
theorem principalCycle_eq_sectionNormRatio
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsIntegral Y]
    (f : X ⟶ Y) [IsFiniteLocallyFree f]
    (L : X.Modules) [IsInvertibleModule X L] (M : Y.Modules) [IsInvertibleModule Y M]
    (a₁ b₁ : Γ(L, ⊤)) (a₂ b₂ : Γ(M, ⊤))
    (ha₁ : IsEffectiveCartierDivisor (zeroScheme X L a₁))
    (hb₁ : IsEffectiveCartierDivisor (zeroScheme X L b₁))
    (ha₂ : IsEffectiveCartierDivisor (zeroScheme Y M a₂))
    (hb₂ : IsEffectiveCartierDivisor (zeroScheme Y M b₂))
    (U : Y.Opens) [Nonempty U] (r : Γ(Y, U)) (hr : IsUnit r)
    (h₁ : zeroScheme (pullback f U.ι) ((Modules.pullback (pullback.fst f U.ι)).obj L)
      (pullbackGlobalSections (pullback.fst f U.ι) L a₁) = ⊤)
    (h₂ : zeroScheme U.toScheme ((Modules.pullback U.ι).obj M)
      (pullbackGlobalSections U.ι M a₂) = ⊤) :
    letI : IsFinite f := IsFiniteLocallyFree.isFinite f
    letI : IsFiniteLocallyFree (pullback.snd f U.ι) :=
      isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f U.ι) inferInstance
    let c₁ := sectionRatioCoefficient ((Modules.pullback (pullback.fst f U.ι)).obj L)
      (pullbackGlobalSections (pullback.fst f U.ι) L a₁)
      (pullbackGlobalSections (pullback.fst f U.ι) L b₁) h₁
    let c₂ := sectionRatioCoefficient ((Modules.pullback U.ι).obj M)
      (pullbackGlobalSections U.ι M a₂) (pullbackGlobalSections U.ι M b₂) h₂
    normTop (pullback.snd f U.ι) c₁ * U.topIso.inv r = c₂ →
    principalCycle Y (Y.germToFunctionField U r) =
      finiteCyclePushforward f (cartierCycle (zeroScheme X L a₁) -
        cartierCycle (zeroScheme X L b₁)) -
      (cartierCycle (zeroScheme Y M a₂) - cartierCycle (zeroScheme Y M b₂)) := by
  dsimp only
  let fU := pullback.snd f U.ι
  let iU := pullback.fst f U.ι
  let : IsFinite f := IsFiniteLocallyFree.isFinite f
  let : Flat f := IsFiniteLocallyFree.flat f
  let : IsFiniteLocallyFree fU := isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f U.ι) inferInstance
  let c₁ := sectionRatioCoefficient ((Modules.pullback iU).obj L)
    (pullbackGlobalSections iU L a₁) (pullbackGlobalSections iU L b₁) h₁
  let c₂ := sectionRatioCoefficient ((Modules.pullback U.ι).obj M)
    (pullbackGlobalSections U.ι M a₂) (pullbackGlobalSections U.ι M b₂) h₂
  intro hnorm
  change normTop fU c₁ * U.topIso.inv r = c₂ at hnorm
  have hr₀ : Y.germToFunctionField U r ≠ 0 :=
    (hr.map (Y.germToFunctionField U).hom).ne_zero
  apply principalCycle_eq_cartierNormRatio f _ _ _ _ ha₁ hb₁ ha₂ hb₂ _ hr₀
  intro y
  obtain ⟨W, hy, ⟨eL⟩, ⟨eM⟩, hfree⟩ := exists_freeAffineNormChart_frames f L M y
  let : IsAffine W.1.toScheme := W.2
  let : Nonempty W.1 := ⟨⟨y, hy⟩⟩
  let fW := pullback.snd f W.1.ι
  let iW := pullback.fst f W.1.ι
  let : IsFiniteLocallyFree fW := isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f W.1.ι) inferInstance
  let : IsAffine (pullback f W.1.ι) := isAffine_of_isAffineHom fW
  let : Algebra Γ(W.1.toScheme, ⊤) Γ(pullback f W.1.ι, ⊤) := fW.appTop.hom.toAlgebra
  let : Module.Free Γ(W.1.toScheme, ⊤) Γ(pullback f W.1.ι, ⊤) := hfree
  let a₁W : Γ(pullback f W.1.ι, ⊤) := eL.hom.app ⊤ (pullbackGlobalSections iW L a₁)
  let b₁W : Γ(pullback f W.1.ι, ⊤) := eL.hom.app ⊤ (pullbackGlobalSections iW L b₁)
  let a₂W : Γ(W.1.toScheme, ⊤) := eM.hom.app ⊤ (pullbackGlobalSections W.1.ι M a₂)
  let b₂W : Γ(W.1.toScheme, ⊤) := eM.hom.app ⊤ (pullbackGlobalSections W.1.ι M b₂)
  refine ⟨W.1, W.2, hy, a₁W, b₁W, a₂W, b₂W, hfree, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← zeroScheme_pullback]
    exact zeroScheme_ideal_eq_span_frame _ eL _
  · rw [← zeroScheme_pullback]
    exact zeroScheme_ideal_eq_span_frame _ eL _
  · rw [← zeroScheme_pullback]
    exact zeroScheme_ideal_eq_span_frame _ eM _
  · rw [← zeroScheme_pullback]
    exact zeroScheme_ideal_eq_span_frame _ eM _
  let Z : Y.Opens := W.1 ⊓ U
  have hηW := ((genericPoint_spec Y).mem_open_set_iff W.1.isOpen).2
    ⟨y, Set.mem_univ _, hy⟩
  have hηU := ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 (by
    simpa only [Set.univ_inter] using (Set.nonempty_coe_sort.1 ‹Nonempty U›))
  let : Nonempty Z := ⟨⟨genericPoint Y, hηW, hηU⟩⟩
  let v := Y.homOfLE (show Z ≤ W.1 from inf_le_left)
  let u' := Y.homOfLE (show Z ≤ U from inf_le_right)
  have huv : u' ≫ U.ι = v ≫ W.1.ι := by simp [v, u']
  let fZ := pullback.snd fW v
  let iZ := pullback.fst fW v
  let : IsFiniteLocallyFree fZ := isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback fW v) inferInstance
  have houter : IsPullback (iZ ≫ iW) fZ f (v ≫ W.1.ι) :=
    (IsPullback.of_hasPullback fW v).paste_horiz (IsPullback.of_hasPullback f W.1.ι)
  have hk : (iZ ≫ iW) ≫ f = (fZ ≫ u') ≫ U.ι := by
    rw [Category.assoc fZ u' U.ι, huv]
    exact houter.w
  let k := pullback.lift (iZ ≫ iW) (fZ ≫ u') hk
  have hk₁ : k ≫ iU = iZ ≫ iW := pullback.lift_fst _ _ _
  have hk₂ : k ≫ fU = fZ ≫ u' := pullback.lift_snd _ _ _
  have hcart : IsPullback k fZ fU u' :=
    (show IsPullback (k ≫ iU) fZ f (u' ≫ U.ι) by rwa [hk₁, huv]).of_right
      hk₂ (IsPullback.of_hasPullback f U.ι)
  have hsrc : k.appTop c₁ * iZ.appTop a₁W = iZ.appTop b₁W :=
    frameCoordinate_mul_of_sectionRatio iW iU iZ k hk₁.symm L a₁ b₁ eL h₁
  have htgt : u'.appTop c₂ * v.appTop a₂W = v.appTop b₂W :=
    frameCoordinate_mul_of_sectionRatio W.1.ι U.ι v u' huv.symm M a₂ b₂ eM h₂
  have hnormZ : normTop fZ (k.appTop c₁) * u'.appTop (U.topIso.inv r) = u'.appTop c₂ := by
    rw [normTop_appTop_of_isPullback fU fZ k u' hcart, ← map_mul, hnorm]
  let : IsOpenImmersion v := by dsimp [v]; infer_instance
  let : IsOpenImmersion u' := by dsimp [u']; infer_instance
  let : IsDominant v := ⟨v.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty v)⟩
  let : IsDominant u' := ⟨u'.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty u')⟩
  let : IsDominant W.1.ι := Opens.isDominant_ι (W.1.isOpen.dense ⟨y, hy⟩)
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.1 ‹_›))
  let : Nonempty (⊤ : Z.toScheme.Opens) := ⟨⟨genericPoint Z.toScheme, trivial⟩⟩
  have hmap (g g' : Z.toScheme ⟶ Y) [IsDominant g] [IsDominant g'] (h : g = g') :
      dominantFunctionFieldMap g = dominantFunctionFieldMap g' := by
    subst g'
    rfl
  have hgerm : dominantFunctionFieldMap v
      (dominantFunctionFieldMap W.1.ι (Y.germToFunctionField U r)) =
      Z.toScheme.germToFunctionField ⊤ (u'.appTop (U.topIso.inv r)) := by
    rw [← RingHom.comp_apply, ← dominantFunctionFieldMap_comp v W.1.ι,
      hmap (v ≫ W.1.ι) (u' ≫ U.ι) huv.symm,
      dominantFunctionFieldMap_comp u' U.ι, RingHom.comp_apply,
      functionFieldMap_germToFunctionField_open U r,
      dominantFunctionFieldMap_germToFunctionField_top]
  exact affineNormCrossProduct_of_open fW v a₁W b₁W a₂W b₂W (k.appTop c₁) (u'.appTop c₂)
    (u'.appTop (U.topIso.inv r)) hsrc htgt _ hgerm hnormZ

end AlgebraicGeometry.Scheme
