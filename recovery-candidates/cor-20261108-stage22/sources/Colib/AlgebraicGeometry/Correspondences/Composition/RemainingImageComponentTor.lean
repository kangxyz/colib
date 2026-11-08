/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentIncidence
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients

/-!
# Full image-component Euler and the original remaining pair Tor

The original incidence point `t` retains its literal image in the adjacent product. At an
actual remaining incidence point over that image support, the full component quotient is
identified with the original support stalk along the actual closed scalar map. The middle
list is transported from the original remaining middle self-product stalk; the scalar
triangle is proved before comparing Koszul complexes. Native regular Koszul resolution then
identifies every length with the actual remaining pair Tor length.

Neither admissibility of the image point nor genericity is needed for the module and degree
comparisons. When the remaining point is generic, the existing actual Tor finite-length
supplier certifies finite lengths. The full signed formula uses the proved Koszul resolution
bound, not an assumed cutoff. This is one component's original Tor coefficient, not a claim
that the whole iterated correspondence bracket has already been reindexed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

private theorem component_comap_idealStalk_congr {T : Scheme.{u}} (J : T.IdealSheafData)
    {a b : T} (hab : a = b) :
    (IdealSheafData.stalk J b).comap
      (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom.hom = IdealSheafData.stalk J a := by
  subst b
  simp [TopCat.Presheaf.stalkCongr]

private theorem component_map_idealStalk_congr {T : Scheme.{u}} (J : T.IdealSheafData)
    {a b : T} (hab : a = b) :
    (IdealSheafData.stalk J a).map
      (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom.hom = IdealSheafData.stalk J b := by
  subst b
  simp [TopCat.Presheaf.stalkCongr]

private theorem component_transported_stalkMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (hxy : y = f x) (hyz : z = g y) :
    ((Z.presheaf.stalkCongr (Inseparable.of_eq hyz)).hom ≫ g.stalkMap y) ≫
      ((Y.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ f.stalkMap x) =
    (Z.presheaf.stalkCongr (Inseparable.of_eq (hyz.trans (congrArg g hxy)))).hom ≫
      (f ≫ g).stalkMap x := by
  subst y
  subst z
  simp [TopCat.Presheaf.stalkCongr, Scheme.Hom.stalkMap_comp]

private theorem component_transported_stalkMap_congr {X Y : Scheme.{u}}
    (f g : X ⟶ Y) (hfg : f = g) (x : X) (y : Y) (hf : y = f x) (hg : y = g x) :
    (Y.presheaf.stalkCongr (Inseparable.of_eq hf)).hom ≫ f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq hg)).hom ≫ g.stalkMap x := by
  subst g
  rfl

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "q" => correspondenceIncidenceMap f g h z w t
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct f h i q v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "u" =>
  correspondenceRemainingSupportToImageExterior f g h i z w v t
local notation3 (prettyPrint := false) "mT" => correspondenceLeftImageMiddlePair f g h i z w v
local notation3 (prettyPrint := false) "mP" => correspondenceMiddlePair f h i
local notation3 (prettyPrint := false) "ι" => correspondenceSupportProductInclusion f h i q v

variable (y : correspondenceIncidence f h i q v)

local notation3 (prettyPrint := false) "x" =>
  correspondenceRemainingPairToImageIncidence f g h i z w v t y
local notation3 (prettyPrint := false) "e" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "p" => correspondenceIncidenceToSupportProduct f h i q v y
local notation3 (prettyPrint := false) "c" => correspondenceIncidenceAmbientInclusion f h i q v y
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "B" => (P).presheaf.stalk p
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk (mT e)
local notation3 (prettyPrint := false) "A₀" => (pullback h h).presheaf.stalk (mP c)
local notation3 (prettyPrint := false) "C" => correspondenceIncidenceAmbientStalk f h i q v y
local notation3 (prettyPrint := false) "I" => IdealSheafData.stalk D e
local notation3 (prettyPrint := false) "M" =>
  correspondenceRemainingImageComponentStalk f g h i z w v x t
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "φ" => correspondenceIncidenceSupportStalkMap f h i q v y
local notation3 (prettyPrint := false) "β" => ((mP).stalkMap c).hom

/-- The full component quotient maps to the original remaining support stalk at its exact point. -/
def correspondenceRemainingPairImageSupportStalkMap : R →+* B :=
  (((T).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRemainingPairToImageIncidence_point f g h i z w v t y))).hom ≫
      (u).stalkMap p).hom

local notation3 (prettyPrint := false) "σ" =>
  correspondenceRemainingPairImageSupportStalkMap f g h i z w v t y

/-- The actual point-transported closed scalar map is surjective. -/
theorem correspondenceRemainingPairImageSupportStalkMap_surjective : Function.Surjective σ :=
  (SurjectiveOnStalks.stalkMap_surjective u p).comp
    (ConcreteCategory.bijective_of_isIso ((T).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRemainingPairToImageIncidence_point f g h i z w v t y))).hom).2

/-- Its kernel is precisely the full component ideal at the actual image-incidence point. -/
theorem correspondenceRemainingPairImageSupportStalkMap_ker : RingHom.ker σ = I := by
  change RingHom.ker (((u).stalkMap p).hom.comp
    ((T).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRemainingPairToImageIncidence_point f g h i z w v t y))).hom.hom) = _
  rw [← RingHom.comap_ker,
    correspondenceRemainingSupportToImageExterior_stalkMap_ker f g h i z w v t p]
  exact component_comap_idealStalk_congr D
    (correspondenceRemainingPairToImageIncidence_point f g h i z w v t y)

/-- The literal coefficient from the whole-image Euler formula is the original support algebra. -/
def correspondenceRemainingPairImageQuotientAlgEquiv :
    letI : Algebra R B := (σ).toAlgebra
    M ≃ₐ[R] B := by
  letI : Algebra R B := (σ).toAlgebra
  change (R ⧸ I) ≃ₐ[R] B
  rw [← correspondenceRemainingPairImageSupportStalkMap_ker f g h i z w v t y]
  exact Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R B)
    (correspondenceRemainingPairImageSupportStalkMap_surjective f g h i z w v t y)

/-- The remaining middle point is the same original point in the two actual presentations. -/
theorem correspondenceRemainingPairImage_middle_point : mT e = mP c := by
  rw [correspondenceRemainingPairToImageIncidence_point f g h i z w v t y]
  calc
    mT (u p) = mP (ι p) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun r => r p)
          (correspondenceRemainingSupportToImageExterior_middle f g h i z w v t)
    _ = mP c := congrArg mP (correspondenceIncidence_ambient_point_eq f h i q v y).symm

/-- Transport only the actual equality of original remaining middle points. -/
abbrev correspondenceRemainingPairMiddleStalkIso : CommRingCat.of A ≅ CommRingCat.of A₀ :=
  (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRemainingPairImage_middle_point f g h i z w v t y))

local notation3 (prettyPrint := false) "ε" =>
  correspondenceRemainingPairMiddleStalkIso f g h i z w v t y

/-- Both routes from the original middle stalk to the original support stalk are the actual map. -/
theorem correspondenceRemainingPairImageSupportStalkMap_middle :
    (σ).comp α = (φ).comp ((β).comp (ε).hom.hom) := by
  have hl := component_transported_stalkMap_comp u mT p e (mT e)
    (correspondenceRemainingPairToImageIncidence_point f g h i z w v t y) rfl
  have hr := component_transported_stalkMap_comp ι mP p c (mT e)
    (correspondenceIncidence_ambient_point_eq f h i q v y)
    (correspondenceRemainingPairImage_middle_point f g h i z w v t y)
  have hc := component_transported_stalkMap_congr (u ≫ mT) (ι ≫ mP)
    (correspondenceRemainingSupportToImageExterior_middle f g h i z w v t) p (mT e)
    (congrArg mT (correspondenceRemainingPairToImageIncidence_point f g h i z w v t y))
    ((correspondenceRemainingPairImage_middle_point f g h i z w v t y).trans
      (congrArg mP (correspondenceIncidence_ambient_point_eq f h i q v y)))
  have H := hl.trans (hc.trans hr.symm)
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] at H
  exact congrArg (fun a => a.hom) H

/-- The same ordered original list is regular and defines the original pair diagonal. -/
theorem correspondenceRemainingPairMiddleList_regular [IsSeparated h] {r : ℕ}
    (s : Fin r → A) (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s)) :
    IsRegular A₀ (List.ofFn (fun j => (ε).hom.hom (s j))) ∧
      IdealSheafData.stalk (pullback.diagonal h).ker (mP c) =
        Ideal.span (Set.range (fun j => (ε).hom.hom (s j))) := by
  constructor
  · let : Algebra A A₀ := (ε).hom.hom.toAlgebra
    have : Module.Flat A A₀ :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (ε).hom)
    have : IsLocalHom (algebraMap A A₀) := isLocalHom_of_iso ε
    have : Module.FaithfullyFlat A A₀ := Module.FaithfullyFlat.of_flat_of_isLocalHom
    have H : IsRegular A₀ ((List.ofFn s).map (algebraMap A A₀)) := hsr.of_faithfullyFlat
    change IsRegular A₀ ((List.ofFn s).map (ε).hom.hom) at H
    simpa only [List.map_ofFn, Function.comp_def] using H
  · have H := component_map_idealStalk_congr (pullback.diagonal h).ker
      (correspondenceRemainingPairImage_middle_point f g h i z w v t y)
    rw [hs, Ideal.map_span, ← Set.range_comp] at H
    exact H.symm

/-- The quotient Koszul homology is the original support Koszul homology with actual scalars. -/
def correspondenceRemainingPairImageKoszulIso {r : ℕ} (a : Fin r → R) (n : ℕ) :
    (Koszul.seqComplexTensor a M).homology n ≅
      (ModuleCat.restrictScalars σ).obj
        ((Koszul.seqComplexTensor (fun j => σ (a j)) B).homology n) := by
  letI : Algebra R B := (σ).toAlgebra
  exact Koszul.homologyTensorCongr a
      (correspondenceRemainingPairImageQuotientAlgEquiv f g h i z w v t y).toLinearEquiv n ≪≫
    Koszul.homologySeqComplexTensorRestrictScalarsIso a (ModuleCat.of B B) n

/-- Every actual quotient Koszul length is the corresponding original remaining pair Tor length. -/
theorem length_correspondenceRemainingPairImageKoszul_eq_Tor
    [Flat f] [Flat i] [IsSeparated h] {r : ℕ} (s : Fin r → A)
    (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s))
    (n : ℕ) :
    Module.length R ((Koszul.seqComplexTensor (fun j => α (s j)) M).homology n) =
      Module.length C (correspondenceIncidenceAmbientTor f h i q v y n) := by
  let s₀ : Fin r → A₀ := fun j => (ε).hom.hom (s j)
  obtain ⟨hs₀, hk₀⟩ := correspondenceRemainingPairMiddleList_regular
    f g h i z w v t y s hsr hs
  have hlist : (fun j => σ (α (s j))) = (fun j => φ (β (s₀ j))) := by
    funext j
    exact congrArg (fun a : A →+* B => a (s j))
      (correspondenceRemainingPairImageSupportStalkMap_middle f g h i z w v t y)
  have hleft : Module.length R ((Koszul.seqComplexTensor (fun j => α (s j)) M).homology n) =
      Module.length B ((Koszul.seqComplexTensor (fun j => σ (α (s j))) B).homology n) := by
    let : Algebra R B := (σ).toAlgebra
    let H := (Koszul.seqComplexTensor (fun j => σ (α (s j))) B).homology n
    let : Module R H := Module.compHom H σ
    have : IsScalarTower R B H := IsScalarTower.of_compHom R B H
    let eH : (Koszul.seqComplexTensor (fun j => α (s j)) M).homology n ≃ₗ[R] H :=
      (correspondenceRemainingPairImageKoszulIso
        f g h i z w v t y (fun j => α (s j)) n).toLinearEquiv
    exact eH.length_eq.trans (Module.length_eq_of_surjective (M := H)
      (correspondenceRemainingPairImageSupportStalkMap_surjective f g h i z w v t y))
  have hright : Module.length C (correspondenceIncidenceAmbientTor f h i q v y n) =
      Module.length B ((Koszul.seqComplexTensor (fun j => φ (β (s₀ j))) B).homology n) := by
    let : Algebra C B := (φ).toAlgebra
    let H := (Koszul.seqComplexTensor (fun j => φ (β (s₀ j))) B).homology n
    let : Module C H := Module.compHom H φ
    have : IsScalarTower C B H := IsScalarTower.of_compHom C B H
    let eH : correspondenceIncidenceAmbientTor f h i q v y n ≃ₗ[C] H :=
      (correspondenceIncidenceTorIsoOriginalSupportKoszul f h i q v y s₀ hs₀ hk₀ n).toLinearEquiv
    exact eH.length_eq.trans (Module.length_eq_of_surjective (M := H)
      (correspondenceIncidenceSupportStalkMap_surjective f h i q v y))
  rw [hlist] at hleft
  exact hleft.trans hright.symm

/-- At an actual generic pair label these lengths are genuinely finite. -/
theorem length_correspondenceRemainingPairImageKoszul_ne_top
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType h]
    [LocallyOfFiniteType i] [Flat f] [Flat i] [IsSeparated h]
    (hy : y ∈ genericPoints (correspondenceIncidence f h i q v)) {r : ℕ} (s : Fin r → A)
    (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s))
    (n : ℕ) : Module.length R
      ((Koszul.seqComplexTensor (fun j => α (s j)) M).homology n) ≠ ⊤ := by
  rw [length_correspondenceRemainingPairImageKoszul_eq_Tor f g h i z w v t y s hsr hs]
  exact correspondenceIncidenceTor_length_ne_top f h i q v ⟨y, hy⟩ n

/-- The full component quotient Euler has the actual original pair Tor lengths and signs. -/
theorem seqEuler_correspondenceRemainingPairImage_eq_sum_Tor
    [Flat f] [Flat i] [IsSeparated h] {r : ℕ} (s : Fin r → A)
    (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun j => α (s j)) M =
      ∑ n : Fin (r + 1), (-1 : ℤ) ^ (n : ℕ) *
        ((Module.length C (correspondenceIncidenceAmbientTor f h i q v y n)).toNat : ℤ) := by
  unfold Koszul.seqEuler
  apply Finset.sum_congr rfl
  intro n _
  rw [length_correspondenceRemainingPairImageKoszul_eq_Tor f g h i z w v t y s hsr hs]

/-- The actual original pair Tor vanishes above the length of the original regular list. -/
theorem isZero_correspondenceRemainingPairTor_of_listLength_lt
    [Flat f] [Flat i] [IsSeparated h] {r : ℕ} (s : Fin r → A)
    (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s))
    {n : ℕ} (hn : r < n) : IsZero (correspondenceIncidenceAmbientTor f h i q v y n) := by
  let s₀ : Fin r → A₀ := fun j => (ε).hom.hom (s j)
  obtain ⟨hs₀, hk₀⟩ := correspondenceRemainingPairMiddleList_regular
    f g h i z w v t y s hsr hs
  let a₀ : Fin r → C := fun j => β (s₀ j)
  let N := correspondenceIncidenceSupportStalkModule f h i q v y
  let J := RingHom.ker ((correspondenceTripleInclusion f h i).stalkMap
    (correspondenceIncidenceInclusion f h i q v y)).hom
  let Q := ModuleCat.of C (C ⧸ J)
  obtain ⟨ha₀, hJ⟩ := correspondenceOriginalMiddleList_pair_regular f h i
    (correspondenceIncidenceInclusion f h i q v y) s₀ hs₀ hk₀
  let eTor := ((Tor (ModuleCat C) n).obj N).mapIso
      (correspondenceIncidenceDiagonalStalkQuotientIso f h i q v y).symm ≪≫
    (((Tor_iso_Tor' C n) ≪≫ (torFlip_iso_Tor' C n).symm).app N).app Q
  refine IsZero.of_iso ?_ eTor
  change IsZero (((Tor' (ModuleCat C) n).obj (ModuleCat.of C (C ⧸ J))).obj N)
  change J = Ideal.span (Set.range a₀) at hJ
  rw [hJ]
  exact Koszul.isZero_tor_of_lt a₀
    ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := C)).2.2 ha₀) N hn

/-- The component quotient gives the full original remaining Tor coefficient, in all degrees. -/
theorem seqEuler_correspondenceRemainingPairImage_eq_finsum_Tor
    [Flat f] [Flat i] [IsSeparated h] {r : ℕ} (s : Fin r → A)
    (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun j => α (s j)) M =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length C (correspondenceIncidenceAmbientTor f h i q v y n)).toNat : ℤ) := by
  rw [seqEuler_correspondenceRemainingPairImage_eq_sum_Tor f g h i z w v t y s hsr hs,
    Fin.sum_univ_eq_sum_range (fun n : ℕ => (-1 : ℤ) ^ n *
      ((Module.length C (correspondenceIncidenceAmbientTor f h i q v y n)).toNat : ℤ))]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  by_contra hnr
  have hz := isZero_correspondenceRemainingPairTor_of_listLength_lt
    f g h i z w v t y s hsr hs (lt_of_not_ge hnr)
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  apply hn
  simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]

/-- Smoothness supplies a list at the original middle point for this actual component comparison. -/
theorem exists_correspondenceRemainingPairImage_originalList_Tor
    [Flat f] [Flat i] [Smooth h] [IsSeparated h] :
    ∃ (r : ℕ) (s : Fin r → A),
      IsRegular A (List.ofFn s) ∧
      IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s) ∧
      Koszul.seqEuler (fun j => α (s j)) M =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length C (correspondenceIncidenceAmbientTor f h i q v y n)).toNat : ℤ) := by
  obtain ⟨r, s, hsr, hs⟩ := exists_correspondenceRemainingOriginalMiddleList f g h i z w v x
  exact ⟨r, s, hsr, hs,
    seqEuler_correspondenceRemainingPairImage_eq_finsum_Tor f g h i z w v t y s hsr hs⟩

end Stacks.Chow
