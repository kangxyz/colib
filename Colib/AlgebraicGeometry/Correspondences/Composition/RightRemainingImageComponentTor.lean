/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingComponentExterior
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingOriginalMiddleList

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

private theorem right_component_comap_idealStalk_congr {T : Scheme.{u}} (J : T.IdealSheafData)
    {a b : T} (hab : a = b) :
    (IdealSheafData.stalk J b).comap
      (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom.hom = IdealSheafData.stalk J a := by
  subst b
  simp [TopCat.Presheaf.stalkCongr]

private theorem right_component_map_idealStalk_congr {T : Scheme.{u}} (J : T.IdealSheafData)
    {a b : T} (hab : a = b) :
    (IdealSheafData.stalk J a).map
      (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom.hom = IdealSheafData.stalk J b := by
  subst b
  simp [TopCat.Presheaf.stalkCongr]

private theorem right_component_transported_stalkMap_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (hxy : y = f x) (hyz : z = g y) :
    ((Z.presheaf.stalkCongr (Inseparable.of_eq hyz)).hom ≫ g.stalkMap y) ≫
      ((Y.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ f.stalkMap x) =
    (Z.presheaf.stalkCongr (Inseparable.of_eq (hyz.trans (congrArg g hxy)))).hom ≫
      (f ≫ g).stalkMap x := by
  subst y
  subst z
  simp [TopCat.Presheaf.stalkCongr, Scheme.Hom.stalkMap_comp]

private theorem right_component_transported_stalkMap_congr {X Y : Scheme.{u}}
    (f g : X ⟶ Y) (hfg : f = g) (x : X) (y : Y) (hf : y = f x) (hg : y = g x) :
    (Y.presheaf.stalkCongr (Inseparable.of_eq hf)).hom ≫ f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq hg)).hom ≫ g.stalkMap x := by
  subst g
  rfl

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

set_option backward.isDefEq.respectTransparency true

/-- The full component quotient maps to the original remaining support stalk at its exact point. -/
def correspondenceRightRemainingPairImageSupportStalkMap
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    let q := correspondenceIncidenceMap g h i w v t
    let P := correspondenceSupportProduct f g i z q
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let p := correspondenceIncidenceToSupportProduct f g i z q y
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let B := P.presheaf.stalk p
    R →+* B := by
  let q := correspondenceIncidenceMap g h i w v t
  let P := correspondenceSupportProduct f g i z q
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let u := correspondenceRightRemainingSupportToImageExterior f g h i z w v t
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let p := correspondenceIncidenceToSupportProduct f g i z q y
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let B := P.presheaf.stalk p
  exact (((T).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRightRemainingPairToImageIncidence_point f g h i z w v t y))).hom ≫
      (u).stalkMap p).hom

/-- The actual point-transported closed scalar map is surjective. -/
theorem correspondenceRightRemainingPairImageSupportStalkMap_surjective
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
    Function.Surjective σ := by
  let q := correspondenceIncidenceMap g h i w v t
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let u := correspondenceRightRemainingSupportToImageExterior f g h i z w v t
  let p := correspondenceIncidenceToSupportProduct f g i z q y
  let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
  exact (SurjectiveOnStalks.stalkMap_surjective u p).comp
    (ConcreteCategory.bijective_of_isIso ((T).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRightRemainingPairToImageIncidence_point f g h i z w v t y))).hom).2

/-- Its kernel is precisely the full component ideal at the actual image-incidence point. -/
theorem correspondenceRightRemainingPairImageSupportStalkMap_ker
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    let D := correspondenceRightRemainingImageComponent f g h i z w v t
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let I := IdealSheafData.stalk D e
    let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
    RingHom.ker σ = I := by
  let q := correspondenceIncidenceMap g h i w v t
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let D := correspondenceRightRemainingImageComponent f g h i z w v t
  let u := correspondenceRightRemainingSupportToImageExterior f g h i z w v t
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let p := correspondenceIncidenceToSupportProduct f g i z q y
  let I := IdealSheafData.stalk D e
  let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
  change RingHom.ker (((u).stalkMap p).hom.comp
    ((T).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRightRemainingPairToImageIncidence_point f g h i z w v t y))).hom.hom) = _
  rw [← RingHom.comap_ker, ker_stalkMap_eq_idealStalk_ker]
  have hu : u.ker = D := correspondenceRightRemainingSupportToImageExterior_ker f g h i z w v t
  rw [hu]
  exact right_component_comap_idealStalk_congr D
    (correspondenceRightRemainingPairToImageIncidence_point f g h i z w v t y)

/-- The literal coefficient from the whole-image Euler formula is the original support algebra. -/
def correspondenceRightRemainingPairImageQuotientAlgEquiv
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    let q := correspondenceIncidenceMap g h i w v t
    let P := correspondenceSupportProduct f g i z q
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let p := correspondenceIncidenceToSupportProduct f g i z q y
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let B := P.presheaf.stalk p
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
    letI : Algebra R B := (σ).toAlgebra
    M ≃ₐ[R] B := by
  let q := correspondenceIncidenceMap g h i w v t
  let P := correspondenceSupportProduct f g i z q
  let D := correspondenceRightRemainingImageComponent f g h i z w v t
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let p := correspondenceIncidenceToSupportProduct f g i z q y
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let B := P.presheaf.stalk p
  let I := IdealSheafData.stalk D e
  let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
  let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
  let : Algebra R B := (σ).toAlgebra
  change (R ⧸ I) ≃ₐ[R] B
  have hI : I = RingHom.ker σ :=
    (correspondenceRightRemainingPairImageSupportStalkMap_ker f g h i z w v t y).symm
  rw [hI]
  exact Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R B)
    (correspondenceRightRemainingPairImageSupportStalkMap_surjective f g h i z w v t y)

/-- The remaining middle point is the same original point in the two actual presentations. -/
theorem correspondenceRightRemainingPairImage_middle_point
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let mP := correspondenceMiddlePair f g i
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let c := correspondenceIncidenceAmbientInclusion f g i z q y
    mT e = mP c := by
  let q := correspondenceIncidenceMap g h i w v t
  let u := correspondenceRightRemainingSupportToImageExterior f g h i z w v t
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let mP := correspondenceMiddlePair f g i
  let ι := correspondenceSupportProductInclusion f g i z q
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let p := correspondenceIncidenceToSupportProduct f g i z q y
  let c := correspondenceIncidenceAmbientInclusion f g i z q y
  have hp : e = u p := correspondenceRightRemainingPairToImageIncidence_point f g h i z w v t y
  change mT e = mP c
  rw [hp]
  calc
    mT (u p) = mP (ι p) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun r => r p)
          (correspondenceRightRemainingSupportToImageExterior_middle f g h i z w v t)
    _ = mP c := congrArg mP (correspondenceIncidence_ambient_point_eq f g i z q y).symm

/-- Transport only the actual equality of original remaining middle points. -/
abbrev correspondenceRightRemainingPairMiddleStalkIso
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let mP := correspondenceMiddlePair f g i
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let c := correspondenceIncidenceAmbientInclusion f g i z q y
    let A := (pullback g g).presheaf.stalk (mT e)
    let A₀ := (pullback g g).presheaf.stalk (mP c)
    CommRingCat.of A ≅ CommRingCat.of A₀ := by
  let q := correspondenceIncidenceMap g h i w v t
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let mP := correspondenceMiddlePair f g i
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let c := correspondenceIncidenceAmbientInclusion f g i z q y
  let A := (pullback g g).presheaf.stalk (mT e)
  let A₀ := (pullback g g).presheaf.stalk (mP c)
  exact (pullback g g).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRightRemainingPairImage_middle_point f g h i z w v t y))

/-- Both routes from the original middle stalk to the original support stalk are the actual map. -/
theorem correspondenceRightRemainingPairImageSupportStalkMap_middle
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    let q := correspondenceIncidenceMap g h i w v t
    let mP := correspondenceMiddlePair f g i
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let c := correspondenceIncidenceAmbientInclusion f g i z q y
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    let φ := correspondenceIncidenceSupportStalkMap f g i z q y
    let β := (mP.stalkMap c).hom
    let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
    let ε := correspondenceRightRemainingPairMiddleStalkIso f g h i z w v t y
    (σ).comp α = (φ).comp ((β).comp (ε).hom.hom) := by
  let q := correspondenceIncidenceMap g h i w v t
  let u := correspondenceRightRemainingSupportToImageExterior f g h i z w v t
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let mP := correspondenceMiddlePair f g i
  let ι := correspondenceSupportProductInclusion f g i z q
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let p := correspondenceIncidenceToSupportProduct f g i z q y
  let c := correspondenceIncidenceAmbientInclusion f g i z q y
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
  let φ := correspondenceIncidenceSupportStalkMap f g i z q y
  let β := (mP.stalkMap c).hom
  let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
  let ε := correspondenceRightRemainingPairMiddleStalkIso f g h i z w v t y
  have hl := right_component_transported_stalkMap_comp u mT p e (mT e)
    (correspondenceRightRemainingPairToImageIncidence_point f g h i z w v t y) rfl
  have hr := right_component_transported_stalkMap_comp ι mP p c (mT e)
    (correspondenceIncidence_ambient_point_eq f g i z q y)
    (correspondenceRightRemainingPairImage_middle_point f g h i z w v t y)
  have hc := right_component_transported_stalkMap_congr (u ≫ mT) (ι ≫ mP)
    (correspondenceRightRemainingSupportToImageExterior_middle f g h i z w v t) p (mT e)
    (congrArg mT (correspondenceRightRemainingPairToImageIncidence_point f g h i z w v t y))
    ((correspondenceRightRemainingPairImage_middle_point f g h i z w v t y).trans
      (congrArg mP (correspondenceIncidence_ambient_point_eq f g i z q y)))
  have H := hl.trans (hc.trans hr.symm)
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] at H
  exact congrArg (fun a => a.hom) H

/-- The same ordered original list is regular and defines the original pair diagonal. -/
theorem correspondenceRightRemainingPairMiddleList_regular
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    [IsSeparated g] :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let mP := correspondenceMiddlePair f g i
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let c := correspondenceIncidenceAmbientInclusion f g i z q y
    let A := (pullback g g).presheaf.stalk (mT e)
    let A₀ := (pullback g g).presheaf.stalk (mP c)
    let ε := correspondenceRightRemainingPairMiddleStalkIso f g h i z w v t y
    ∀ {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal g).ker (mT e) = Ideal.span (Set.range s)),
      IsRegular A₀ (List.ofFn (fun j => (ε).hom.hom (s j))) ∧
        IdealSheafData.stalk (pullback.diagonal g).ker (mP c) =
          Ideal.span (Set.range (fun j => (ε).hom.hom (s j))) := by
  let q := correspondenceIncidenceMap g h i w v t
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let mP := correspondenceMiddlePair f g i
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let c := correspondenceIncidenceAmbientInclusion f g i z q y
  let A := (pullback g g).presheaf.stalk (mT e)
  let A₀ := (pullback g g).presheaf.stalk (mP c)
  let ε := correspondenceRightRemainingPairMiddleStalkIso f g h i z w v t y
  dsimp only
  intro r s hsr hs
  constructor
  · let : Algebra A A₀ := (ε).hom.hom.toAlgebra
    have : Module.Flat A A₀ :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (ε).hom)
    have : IsLocalHom (algebraMap A A₀) := isLocalHom_of_iso ε
    have : Module.FaithfullyFlat A A₀ := Module.FaithfullyFlat.of_flat_of_isLocalHom
    have H : IsRegular A₀ ((List.ofFn s).map (algebraMap A A₀)) := hsr.of_faithfullyFlat
    change IsRegular A₀ ((List.ofFn s).map (ε).hom.hom) at H
    simpa only [List.map_ofFn, Function.comp_def] using H
  · have H := right_component_map_idealStalk_congr (pullback.diagonal g).ker
      (correspondenceRightRemainingPairImage_middle_point f g h i z w v t y)
    rw [hs, Ideal.map_span, ← Set.range_comp] at H
    exact H.symm

/-- The quotient Koszul homology is the original support Koszul homology with actual scalars. -/
def correspondenceRightRemainingPairImageKoszulIso
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    let q := correspondenceIncidenceMap g h i w v t
    let P := correspondenceSupportProduct f g i z q
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let p := correspondenceIncidenceToSupportProduct f g i z q y
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let B := P.presheaf.stalk p
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
    ∀ {r : ℕ}
      (a : Fin r → R)
      (n : ℕ),
      (Koszul.seqComplexTensor a M).homology n ≅
        (ModuleCat.restrictScalars σ).obj
          ((Koszul.seqComplexTensor (fun j => σ (a j)) B).homology n) := by
  let q := correspondenceIncidenceMap g h i w v t
  let P := correspondenceSupportProduct f g i z q
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let p := correspondenceIncidenceToSupportProduct f g i z q y
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let B := P.presheaf.stalk p
  let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
  let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
  dsimp only
  intro r a n
  let : Algebra R B := (σ).toAlgebra
  exact Koszul.homologyTensorCongr a
      (correspondenceRightRemainingPairImageQuotientAlgEquiv f g h i z w v t y).toLinearEquiv n ≪≫
    Koszul.homologySeqComplexTensorRestrictScalarsIso a (ModuleCat.of B B) n

/-- Every actual quotient Koszul length is the corresponding original remaining pair Tor length. -/
theorem length_correspondenceRightRemainingPairImageKoszul_eq_Tor
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    [Flat f] [Flat i] [IsSeparated g] :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let A := (pullback g g).presheaf.stalk (mT e)
    let C := correspondenceIncidenceAmbientStalk f g i z q y
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    ∀ {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal g).ker (mT e) = Ideal.span (Set.range s))
      (n : ℕ),
      Module.length R ((Koszul.seqComplexTensor (fun j => α (s j)) M).homology n) =
        Module.length C (correspondenceIncidenceAmbientTor f g i z q y n) := by
  let q := correspondenceIncidenceMap g h i w v t
  let P := correspondenceSupportProduct f g i z q
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let mP := correspondenceMiddlePair f g i
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let p := correspondenceIncidenceToSupportProduct f g i z q y
  let c := correspondenceIncidenceAmbientInclusion f g i z q y
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let B := P.presheaf.stalk p
  let A := (pullback g g).presheaf.stalk (mT e)
  let A₀ := (pullback g g).presheaf.stalk (mP c)
  let C := correspondenceIncidenceAmbientStalk f g i z q y
  let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
  let φ := correspondenceIncidenceSupportStalkMap f g i z q y
  let β := (mP.stalkMap c).hom
  let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
  let ε := correspondenceRightRemainingPairMiddleStalkIso f g h i z w v t y
  dsimp only
  intro r s hsr hs n
  let s₀ : Fin r → A₀ := fun j => (ε).hom.hom (s j)
  obtain ⟨hs₀, hk₀⟩ := correspondenceRightRemainingPairMiddleList_regular
    f g h i z w v t y s hsr hs
  have hlist : (fun j => σ (α (s j))) = (fun j => φ (β (s₀ j))) := by
    funext j
    exact congrArg (fun a : A →+* B => a (s j))
      (correspondenceRightRemainingPairImageSupportStalkMap_middle f g h i z w v t y)
  have hleft : Module.length R ((Koszul.seqComplexTensor (fun j => α (s j)) M).homology n) =
      Module.length B ((Koszul.seqComplexTensor (fun j => σ (α (s j))) B).homology n) := by
    let : Algebra R B := (σ).toAlgebra
    let H := (Koszul.seqComplexTensor (fun j => σ (α (s j))) B).homology n
    let : Module R H := Module.compHom H σ
    have : IsScalarTower R B H := IsScalarTower.of_compHom R B H
    let eH : (Koszul.seqComplexTensor (fun j => α (s j)) M).homology n ≃ₗ[R] H :=
      (correspondenceRightRemainingPairImageKoszulIso
        f g h i z w v t y (fun j => α (s j)) n).toLinearEquiv
    exact eH.length_eq.trans (Module.length_eq_of_surjective (M := H)
      (correspondenceRightRemainingPairImageSupportStalkMap_surjective f g h i z w v t y))
  have hright : Module.length C (correspondenceIncidenceAmbientTor f g i z q y n) =
      Module.length B ((Koszul.seqComplexTensor (fun j => φ (β (s₀ j))) B).homology n) := by
    let : Algebra C B := (φ).toAlgebra
    let H := (Koszul.seqComplexTensor (fun j => φ (β (s₀ j))) B).homology n
    let : Module C H := Module.compHom H φ
    have : IsScalarTower C B H := IsScalarTower.of_compHom C B H
    let eH : correspondenceIncidenceAmbientTor f g i z q y n ≃ₗ[C] H :=
      (correspondenceIncidenceTorIsoOriginalSupportKoszul f g i z q y s₀ hs₀ hk₀ n).toLinearEquiv
    exact eH.length_eq.trans (Module.length_eq_of_surjective (M := H)
      (correspondenceIncidenceSupportStalkMap_surjective f g i z q y))
  rw [hlist] at hleft
  exact hleft.trans hright.symm

/-- At an actual generic pair label these lengths are genuinely finite. -/
theorem length_correspondenceRightRemainingPairImageKoszul_ne_top
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [LocallyOfFiniteType i] [Flat f] [Flat i] [IsSeparated g] :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let A := (pullback g g).presheaf.stalk (mT e)
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    ∀ (_hy : y ∈ genericPoints (correspondenceIncidence f g i z q))
      {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal g).ker (mT e) = Ideal.span (Set.range s))
      (n : ℕ),
      Module.length R
        ((Koszul.seqComplexTensor (fun j => α (s j)) M).homology n) ≠ ⊤ := by
  let q := correspondenceIncidenceMap g h i w v t
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let A := (pullback g g).presheaf.stalk (mT e)
  let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
  dsimp only
  intro hy r s hsr hs n
  rw [length_correspondenceRightRemainingPairImageKoszul_eq_Tor f g h i z w v t y s hsr hs]
  exact correspondenceIncidenceTor_length_ne_top f g i z q ⟨y, hy⟩ n

/-- The full component quotient Euler has the actual original pair Tor lengths and signs. -/
theorem seqEuler_correspondenceRightRemainingPairImage_eq_sum_Tor
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    [Flat f] [Flat i] [IsSeparated g] :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let A := (pullback g g).presheaf.stalk (mT e)
    let C := correspondenceIncidenceAmbientStalk f g i z q y
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    ∀ {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal g).ker (mT e) = Ideal.span (Set.range s)),
      Koszul.seqEuler (fun j => α (s j)) M =
        ∑ n : Fin (r + 1), (-1 : ℤ) ^ (n : ℕ) *
          ((Module.length C (correspondenceIncidenceAmbientTor f g i z q y n)).toNat : ℤ) := by
  let q := correspondenceIncidenceMap g h i w v t
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let A := (pullback g g).presheaf.stalk (mT e)
  let C := correspondenceIncidenceAmbientStalk f g i z q y
  let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
  dsimp only
  intro r s hsr hs
  unfold Koszul.seqEuler
  apply Finset.sum_congr rfl
  intro n _
  rw [length_correspondenceRightRemainingPairImageKoszul_eq_Tor f g h i z w v t y s hsr hs]

/-- The actual original pair Tor vanishes above the length of the original regular list. -/
theorem isZero_correspondenceRightRemainingPairTor_of_listLength_lt
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    [Flat f] [Flat i] [IsSeparated g] :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let A := (pullback g g).presheaf.stalk (mT e)
    ∀ {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal g).ker (mT e) = Ideal.span (Set.range s))
      {n : ℕ}
      (_hn : r < n),
      IsZero (correspondenceIncidenceAmbientTor f g i z q y n) := by
  let q := correspondenceIncidenceMap g h i w v t
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let mP := correspondenceMiddlePair f g i
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let c := correspondenceIncidenceAmbientInclusion f g i z q y
  let A := (pullback g g).presheaf.stalk (mT e)
  let A₀ := (pullback g g).presheaf.stalk (mP c)
  let C := correspondenceIncidenceAmbientStalk f g i z q y
  let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
  let β := (mP.stalkMap c).hom
  let ε := correspondenceRightRemainingPairMiddleStalkIso f g h i z w v t y
  dsimp only
  intro r s hsr hs n hn
  let s₀ : Fin r → A₀ := fun j => (ε).hom.hom (s j)
  obtain ⟨hs₀, hk₀⟩ := correspondenceRightRemainingPairMiddleList_regular
    f g h i z w v t y s hsr hs
  let a₀ : Fin r → C := fun j => β (s₀ j)
  let N := correspondenceIncidenceSupportStalkModule f g i z q y
  let J : Ideal C := RingHom.ker ((correspondenceTripleInclusion f g i).stalkMap
    (correspondenceIncidenceInclusion f g i z q y)).hom
  let Q := ModuleCat.of C (C ⧸ J)
  obtain ⟨ha₀, hJ⟩ := correspondenceOriginalMiddleList_pair_regular f g i
    (correspondenceIncidenceInclusion f g i z q y) s₀ hs₀ hk₀
  let eTor := ((Tor (ModuleCat C) n).obj N).mapIso
      (correspondenceIncidenceDiagonalStalkQuotientIso f g i z q y).symm ≪≫
    (((Tor_iso_Tor' C n) ≪≫ (torFlip_iso_Tor' C n).symm).app N).app Q ≪≫
    ((Tor_iso_Tor' C n).app Q).app N
  refine IsZero.of_iso ?_ eTor
  change IsZero (((Tor' (ModuleCat C) n).obj (ModuleCat.of C (C ⧸ J))).obj N)
  change IsRegular C (List.ofFn a₀) at ha₀
  change J = Ideal.span (Set.range a₀) at hJ
  rw [hJ]
  exact Koszul.isZero_tor_of_lt a₀
    ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := C)).2.2 ha₀) N hn

/-- The component quotient gives the full original remaining Tor coefficient, in all degrees. -/
theorem seqEuler_correspondenceRightRemainingPairImage_eq_finsum_Tor
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    [Flat f] [Flat i] [IsSeparated g] :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let A := (pullback g g).presheaf.stalk (mT e)
    let C := correspondenceIncidenceAmbientStalk f g i z q y
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    ∀ {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal g).ker (mT e) = Ideal.span (Set.range s)),
      Koszul.seqEuler (fun j => α (s j)) M =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length C (correspondenceIncidenceAmbientTor f g i z q y n)).toNat : ℤ) := by
  let q := correspondenceIncidenceMap g h i w v t
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let A := (pullback g g).presheaf.stalk (mT e)
  let C := correspondenceIncidenceAmbientStalk f g i z q y
  let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
  dsimp only
  intro r s hsr hs
  rw [seqEuler_correspondenceRightRemainingPairImage_eq_sum_Tor f g h i z w v t y s hsr hs,
    Fin.sum_univ_eq_sum_range (fun n : ℕ => (-1 : ℤ) ^ n *
      ((Module.length C (correspondenceIncidenceAmbientTor f g i z q y n)).toNat : ℤ))]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  by_contra hnr
  have hz := isZero_correspondenceRightRemainingPairTor_of_listLength_lt
    f g h i z w v t y s hsr hs (lt_of_not_ge hnr)
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  apply hn
  simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]

/-- Smoothness supplies a list at the original middle point for this actual component comparison. -/
theorem exists_correspondenceRightRemainingPairImage_originalList_Tor
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    [Flat f] [Flat i] [Smooth g] [IsSeparated g] :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let A := (pullback g g).presheaf.stalk (mT e)
    let C := correspondenceIncidenceAmbientStalk f g i z q y
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    ∃ (r : ℕ) (s : Fin r → A),
      IsRegular A (List.ofFn s) ∧
      IdealSheafData.stalk (pullback.diagonal g).ker (mT e) = Ideal.span (Set.range s) ∧
      Koszul.seqEuler (fun j => α (s j)) M =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length C (correspondenceIncidenceAmbientTor f g i z q y n)).toNat : ℤ) := by
  let q := correspondenceIncidenceMap g h i w v t
  let mT := correspondenceRightImageMiddlePair f g h i z w v
  let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let A := (pullback g g).presheaf.stalk (mT e)
  let C := correspondenceIncidenceAmbientStalk f g i z q y
  let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
  obtain ⟨r, s, hsr, hs⟩ := exists_correspondenceRightRemainingOriginalMiddleList f g h i z w v x
  exact ⟨r, s, hsr, hs,
    seqEuler_correspondenceRightRemainingPairImage_eq_finsum_Tor f g h i z w v t y s hsr hs⟩

end Stacks.Chow
