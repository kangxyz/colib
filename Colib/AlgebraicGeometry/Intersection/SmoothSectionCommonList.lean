/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Sequence.Regular.SplitBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.PerfectFactor
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A common stalk family for a smooth section and its arbitrary base change

Let `σ : S ⟶ T` be a section of a smooth map `p : T ⟶ S`. At any point
`t = σ s`, the actual section stalk kernel has a regular generating family.
Its quotient is flat over `𝒪_{S,p(t)}`: the section stalk map, followed by the
inverse of the stalk map of `σ ≫ p`, is an algebra retraction of the literal
map `p.stalkMap t`.

Given an arbitrary `f : X ⟶ S` with `X` locally Noetherian and a point `z`
of `T ×[S] X` over `t`, the *same* family remains regular in the actual
pullback stalk. The scalar map is exactly `(pullback.fst p f).stalkMap z`.
Native Stacks supplies the tensor-product localization and identifies both
factor maps. Smoothness of its projection to `X` makes that stalk Noetherian.
The proof does not assume flatness of `f` or choose an independent target list.

This is the section form of the common smooth-diagonal family needed for
graph and mixed graph/exterior coefficients. It uses native Stacks 067R,
0CEP and 061S rather than reconstructing a standard-smooth presentation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A smooth section supplies an actual regular kernel family with a flat
quotient over the projection stalk. The displayed point equality is retained
in the section stalk map. -/
theorem exists_isRegular_stalkList_flatQuotient_of_smooth_section
    {S T : Scheme.{u}} (p : T ⟶ S) [Smooth p]
    (σ : S ⟶ T) (hσ : σ ≫ p = 𝟙 S) (s : S)
    (t : T) (ht : t = σ s) :
    let A := S.presheaf.stalk (p t)
    let B := T.presheaf.stalk t
    letI : Algebra A B := (p.stalkMap t).hom.toAlgebra
    ∃ (r : ℕ) (b : Fin r → B), IsRegular B (List.ofFn b) ∧
      Ideal.span (Set.range b) =
        RingHom.ker ((T.presheaf.stalkCongr (.of_eq ht)).hom ≫ σ.stalkMap s).hom ∧
      Module.Flat A (B ⧸ Ideal.span (Set.range b)) := by
  subst t
  dsimp only
  let : Algebra (S.presheaf.stalk (p (σ s))) (T.presheaf.stalk (σ s)) :=
    (p.stalkMap (σ s)).hom.toAlgebra
  have : IsIso (σ ≫ p) := by rw [hσ]; infer_instance
  have hsplit :
      (σ.stalkMap s ≫ inv ((σ ≫ p).stalkMap s)).hom.comp (p.stalkMap (σ s)).hom =
        RingHom.id (S.presheaf.stalk (p (σ s))) := by
    change ((p.stalkMap (σ s) ≫ σ.stalkMap s) ≫
      inv ((σ ≫ p).stalkMap s)).hom = _
    rw [← Scheme.Hom.stalkMap_comp]
    simp
  let ε : T.presheaf.stalk (σ s) →ₐ[S.presheaf.stalk (p (σ s))]
      S.presheaf.stalk (p (σ s)) :=
    { (σ.stalkMap s ≫ inv ((σ ≫ p).stalkMap s)).hom with
      commutes' := fun a => DFunLike.congr_fun hsplit a }
  have hκε : RingHom.ker ε.toRingHom = RingHom.ker (σ.stalkMap s).hom := by
    change RingHom.ker ((inv ((σ ≫ p).stalkMap s)).hom.comp (σ.stalkMap s).hom) = _
    exact RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (inv ((σ ≫ p).stalkMap s))).1
  let : IsImmersion σ :=
    Stacks.AlgebraicGeometry.isImmersion_of_comp_eq_id σ p hσ
  obtain ⟨l, hl, hk⟩ :=
    Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
      σ (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section p σ hσ) s
  have hfamily : Ideal.span (Set.range l.get) = RingHom.ker (σ.stalkMap s).hom := by
    rw [← Ideal.ofList_ofFn, List.ofFn_get]
    exact hk
  refine ⟨l.length, l.get, ?_, ?_, ?_⟩
  · simpa only [List.ofFn_get] using hl
  · simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] using hfamily
  · rw [hfamily, ← hκε]
    exact flat_quotient_ker_algebraRetraction ε

/-- One source regular family generates the actual section kernel and remains
regular under the literal pullback projection stalk map. The base-change map
is arbitrary; local Noetherianity is required only on its source. -/
@[stacks 067R "application: regular family in the smooth-section stalk kernel",
  stacks 0CEP "application: the same family after arbitrary base change",
  stacks 061S "application: regularity in the actual Noetherian local pullback stalk"]
theorem exists_isRegular_stalkList_pullback_of_smooth_section
    {S T X : Scheme.{u}} (p : T ⟶ S) [Smooth p]
    (σ : S ⟶ T) (hσ : σ ≫ p = 𝟙 S)
    (f : X ⟶ S) [IsLocallyNoetherian X]
    (z : pullback (C := Scheme) p f) (s : S) (hz : pullback.fst p f z = σ s) :
    ∃ (r : ℕ) (b : Fin r → T.presheaf.stalk (pullback.fst p f z)),
      IsRegular (T.presheaf.stalk (pullback.fst p f z)) (List.ofFn b) ∧
      Ideal.span (Set.range b) = RingHom.ker
        ((T.presheaf.stalkCongr (.of_eq hz)).hom ≫ σ.stalkMap s).hom ∧
      IsRegular ((pullback p f).presheaf.stalk z)
        (List.ofFn (fun i => ((pullback.fst p f).stalkMap z).hom (b i))) := by
  let pT : pullback p f ⟶ T := pullback.fst p f
  let pX : pullback p f ⟶ X := pullback.snd p f
  let h : (pT ≫ p).base z = (pX ≫ f).base z :=
    congrArg (fun k : pullback p f ⟶ S => k.base z) pullback.condition
  let A := S.presheaf.stalk ((pT ≫ p).base z)
  let B := T.presheaf.stalk (pT.base z)
  let A' := X.presheaf.stalk (pX.base z)
  let D := (pullback p f).presheaf.stalk z
  let : Algebra A B := (p.stalkMap (pT.base z)).hom.toAlgebra
  let : Algebra A A' :=
    (eqToHom (congrArg S.presheaf.stalk h) ≫ f.stalkMap (pX.base z)).hom.toAlgebra
  have : IsLocallyNoetherian (pullback p f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p f)
  obtain ⟨r, b, hb, hk, hflat⟩ :=
    exists_isRegular_stalkList_flatQuotient_of_smooth_section p σ hσ s (pT z) hz
  obtain ⟨φ, hφ, _, hloc⟩ := BaseChangeStalk.pullback_stalk_isLocalization p f z
  refine ⟨r, b, hb, hk, ?_⟩
  exact hb.map_of_quotient_flat_tensor_localization (A := A) (A' := A')
    hflat (pT.stalkMap z).hom φ hφ hloc

set_option backward.isDefEq.respectTransparency.types false in
/-- Replacing the actual coefficient pullback by a specified scheme isomorphism
preserves the same family and the literal composite stalk map. -/
theorem exists_isRegular_stalkList_pullbackIso_of_smooth_section
    {S T X V : Scheme.{u}} (p : T ⟶ S) [Smooth p]
    (σ : S ⟶ T) (hσ : σ ≫ p = 𝟙 S)
    (f : X ⟶ S) [IsLocallyNoetherian X]
    (e : V ≅ pullback p f) (z : V) (s : S)
    (hz : (e.hom ≫ pullback.fst p f) z = σ s) :
    ∃ (r : ℕ) (b : Fin r → T.presheaf.stalk ((e.hom ≫ pullback.fst p f) z)),
      IsRegular (T.presheaf.stalk ((e.hom ≫ pullback.fst p f) z)) (List.ofFn b) ∧
      Ideal.span (Set.range b) = RingHom.ker
        ((T.presheaf.stalkCongr (.of_eq hz)).hom ≫ σ.stalkMap s).hom ∧
      IsRegular (V.presheaf.stalk z)
        (List.ofFn (fun i => ((e.hom ≫ pullback.fst p f).stalkMap z).hom (b i))) := by
  obtain ⟨r, b, hb, hk, himage⟩ :=
    exists_isRegular_stalkList_pullback_of_smooth_section p σ hσ f (e.hom z) s hz
  refine ⟨r, b, hb, hk, ?_⟩
  let E := (asIso (e.hom.stalkMap z)).commRingCatIsoToRingEquiv
  have hE := himage.map_ringEquiv E
  have hE_apply (a : (pullback (C := Scheme) p f).presheaf.stalk (e.hom z)) :
      E a = (e.hom.stalkMap z).hom a := by
    exact DFunLike.congr_fun
      (Iso.commRingCatIsoToRingEquiv_toRingHom (asIso (e.hom.stalkMap z))) a
  have hfamily :
      (List.ofFn (fun i => ((pullback.fst p f).stalkMap (e.hom z)).hom (b i))).map E =
        List.ofFn (fun i => ((e.hom ≫ pullback.fst p f).stalkMap z).hom (b i)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    change E (((pullback.fst p f).stalkMap (e.hom z)).hom (b i)) = _
    rw [hE_apply]
    exact DFunLike.congr_fun
      (congrArg (fun k => k.hom)
        (Scheme.Hom.stalkMap_comp e.hom (pullback.fst p f) z)).symm (b i)
  rw [← hfamily]
  exact hE

/-- A smooth diagonal admits a single regular stalk family that stays regular
after arbitrary base change from a locally Noetherian scheme. This is stated
on the native reassociated pullback before any graph-product identification. -/
theorem exists_isRegular_diagonalStalkList_pullback
    {S Y X : Scheme.{u}} (g : Y ⟶ S) [Smooth g]
    (f : X ⟶ Y) [IsLocallyNoetherian X]
    (z : pullback (C := Scheme) (pullback.fst g g) f) (y : Y)
    (hz : pullback.fst (pullback.fst g g) f z = pullback.diagonal g y) :
    ∃ (r : ℕ)
      (b : Fin r → (pullback g g).presheaf.stalk
        (pullback.fst (pullback.fst g g) f z)),
      IsRegular ((pullback g g).presheaf.stalk
        (pullback.fst (pullback.fst g g) f z)) (List.ofFn b) ∧
      Ideal.span (Set.range b) = RingHom.ker
        (((pullback g g).presheaf.stalkCongr (.of_eq hz)).hom ≫
          (pullback.diagonal g).stalkMap y).hom ∧
      IsRegular ((pullback (pullback.fst g g) f).presheaf.stalk z)
        (List.ofFn (fun i =>
          ((pullback.fst (pullback.fst g g) f).stalkMap z).hom (b i))) :=
  exists_isRegular_stalkList_pullback_of_smooth_section (pullback.fst g g)
    (pullback.diagonal g) (pullback.diagonal_fst g) f z y hz

end AlgebraicGeometry.Scheme.Hom
