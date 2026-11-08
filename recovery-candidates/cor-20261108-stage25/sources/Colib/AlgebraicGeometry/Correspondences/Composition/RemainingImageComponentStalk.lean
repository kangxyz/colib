/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentGeometry
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalKoszulTor
public import StacksFrontier.RingTheory.Koszul.Localization

/-!
# The full image-component quotient is the original remaining support stalk

The proved geometric component comparison supplies a closed map from the actual remaining
support product to the whole image exterior. Its ideal is the full inverse-image component
ideal, and its ambient map is the original support inclusion. Native closed-immersion stalk
surjectivity therefore identifies the actual component quotient with the actual support
stalk as an algebra, not merely as an abstract ring.

The ambient scalar triangle is proved with the required stalk-point transport. Native
coefficient and restriction-of-scalars Koszul comparisons then identify every homology degree
and its length, and hence the finite integer Koszul Euler sum. No comparison hypothesis,
flatness of the support product, reduction of the exterior, or admissibility of the original
image point is used. This is the coefficient realization; comparison with the original
remaining pair Tor also needs its actual incidence point and original diagonal list.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "P" =>
  correspondenceSupportProduct f h i (correspondenceIncidenceMap f g h z w t) v
local notation3 (prettyPrint := false) "j" => correspondenceLeftImageProductInclusion f g h i z w v
local notation3 (prettyPrint := false) "ι" =>
  correspondenceSupportProductInclusion f h i (correspondenceIncidenceMap f g h z w t) v

/-- The original full support product realizes the full component exterior. -/
def correspondenceRemainingImageComponentSupportIso : (D).subscheme ≅ P :=
  (exists_correspondenceRemainingImageComponentSupportIso f g h i z w v t).choose

/-- The chosen native geometric comparison preserves the actual ambient inclusion. -/
@[reassoc]
theorem correspondenceRemainingImageComponentSupportIso_ambient :
    (correspondenceRemainingImageComponentSupportIso f g h i z w v t).hom ≫ ι =
      (D).subschemeι ≫ j :=
  (exists_correspondenceRemainingImageComponentSupportIso f g h i z w v t).choose_spec

/-- The actual remaining support embeds into the whole image exterior. -/
def correspondenceRemainingSupportToImageExterior : P ⟶ T :=
  (correspondenceRemainingImageComponentSupportIso f g h i z w v t).inv ≫ (D).subschemeι

instance isClosedImmersion_correspondenceRemainingSupportToImageExterior :
    IsClosedImmersion (correspondenceRemainingSupportToImageExterior f g h i z w v t) := by
  dsimp only [correspondenceRemainingSupportToImageExterior]
  infer_instance

/-- The full scheme-theoretic component ideal, without radical replacement. -/
theorem correspondenceRemainingSupportToImageExterior_ker :
    (correspondenceRemainingSupportToImageExterior f g h i z w v t).ker = D := by
  rw [correspondenceRemainingSupportToImageExterior, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

/-- The full component embedding and the original support inclusion have the same ambient map. -/
@[reassoc]
theorem correspondenceRemainingSupportToImageExterior_ambient :
    correspondenceRemainingSupportToImageExterior f g h i z w v t ≫ j = ι := by
  dsimp only [correspondenceRemainingSupportToImageExterior]
  rw [Category.assoc, ← correspondenceRemainingImageComponentSupportIso_ambient]
  simp

set_option backward.isDefEq.respectTransparency true

/-- A typed name for the image of the original support point under the unchanged embedding. -/
def correspondenceRemainingSupportImagePoint (p : P) : T := by
  let a : P ⟶ T := correspondenceRemainingSupportToImageExterior f g h i z w v t
  exact a p

/-- The original stalk map, with its actual source and target rings explicitly fixed. -/
def correspondenceRemainingSupportImageStalkMap (p : P) :
    (T).presheaf.stalk (correspondenceRemainingSupportImagePoint f g h i z w v t p) →+*
      (P).presheaf.stalk p := by
  change (T).presheaf.stalk
    (correspondenceRemainingSupportToImageExterior f g h i z w v t p) →+*
      (P).presheaf.stalk p
  exact ((correspondenceRemainingSupportToImageExterior f g h i z w v t).stalkMap p).hom

/-- Surjectivity of the same actual closed-immersion scalar map. -/
theorem correspondenceRemainingSupportImageStalkMap_surjective (p : P) :
    Function.Surjective
      (correspondenceRemainingSupportImageStalkMap f g h i z w v t p) := by
  change Function.Surjective
    ((correspondenceRemainingSupportToImageExterior f g h i z w v t).stalkMap p).hom
  exact SurjectiveOnStalks.stalkMap_surjective
    (correspondenceRemainingSupportToImageExterior f g h i z w v t) p

/-- The literal full component ideal is the kernel of that same scalar map. -/
theorem correspondenceRemainingSupportToImageExterior_stalkMap_ker (p : P) :
    RingHom.ker (correspondenceRemainingSupportImageStalkMap f g h i z w v t p) =
      IdealSheafData.stalk D (correspondenceRemainingSupportImagePoint f g h i z w v t p) := by
  change RingHom.ker
    ((correspondenceRemainingSupportToImageExterior f g h i z w v t).stalkMap p).hom = _
  rw [ker_stalkMap_eq_idealStalk_ker,
    correspondenceRemainingSupportToImageExterior_ker]
  rfl

/-- The original support stalk is the actual image-exterior quotient, with its scalar map. -/
def correspondenceRemainingImageComponentSupportStalkAlgEquiv (p : P) :
    let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
    let R := (T).presheaf.stalk q
    let B := (P).presheaf.stalk p
    let I : Ideal R := IdealSheafData.stalk D q
    let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
    letI : Algebra R B := φ.toAlgebra
    (R ⧸ I) ≃ₐ[R] B := by
  let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
  let R := (T).presheaf.stalk q
  let B := (P).presheaf.stalk p
  let I : Ideal R := IdealSheafData.stalk D q
  let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
  letI : Algebra R B := φ.toAlgebra
  change (R ⧸ I) ≃ₐ[R] B
  rw [← correspondenceRemainingSupportToImageExterior_stalkMap_ker f g h i z w v t p]
  exact Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R B)
    (correspondenceRemainingSupportImageStalkMap_surjective f g h i z w v t p)

/-- This algebra comparison sends each original scalar to its actual stalk image. -/
theorem correspondenceRemainingImageComponentSupportStalkAlgEquiv_mk (p : P)
    (b : (T).presheaf.stalk (correspondenceRemainingSupportImagePoint f g h i z w v t p)) :
    correspondenceRemainingImageComponentSupportStalkAlgEquiv f g h i z w v t p
      (Ideal.Quotient.mk
        (IdealSheafData.stalk D (correspondenceRemainingSupportImagePoint f g h i z w v t p)) b) =
      correspondenceRemainingSupportImageStalkMap f g h i z w v t p b :=
  (correspondenceRemainingImageComponentSupportStalkAlgEquiv f g h i z w v t p).commutes b

/-- The original support ambient point equals the full component's ambient point. -/
theorem correspondenceRemainingSupportToImageExterior_point (p : P) :
    j (correspondenceRemainingSupportImagePoint f g h i z w v t p) = ι p := by
  simpa only [correspondenceRemainingSupportImagePoint, Scheme.Hom.comp_apply] using
    congrArg (fun m => m p)
      (correspondenceRemainingSupportToImageExterior_ambient f g h i z w v t)

/-- The actual image-to-support scalar map respects the ambient action and point transport. -/
theorem correspondenceRemainingSupportToImageExterior_stalkMap_comp (p : P) :
    let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
    let φ := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
    φ.comp (((j).stalkMap q).hom) =
      (((correspondenceIntersectionAmbient f h i).presheaf.stalkCongr
        (Inseparable.of_eq
          (correspondenceRemainingSupportToImageExterior_point f g h i z w v t p))).hom ≫
        (ι).stalkMap p).hom := by
  let a : P ⟶ T := correspondenceRemainingSupportToImageExterior f g h i z w v t
  have H := Scheme.Hom.stalkMap_congr_hom (a ≫ j) ι
    (correspondenceRemainingSupportToImageExterior_ambient f g h i z w v t) p
  rw [Scheme.Hom.stalkMap_comp] at H
  exact congrArg (fun a => a.hom) H

/-- The actual component quotient Koszul homology is the original support homology,
with the latter restricted along the actual surjective stalk map. -/
def correspondenceRemainingImageComponentSupportKoszulIso (p : P) {r : ℕ}
    (a : Fin r → (T).presheaf.stalk (correspondenceRemainingSupportImagePoint f g h i z w v t p))
    (n : ℕ) :
    let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
    let R := (T).presheaf.stalk q
    let B := (P).presheaf.stalk p
    let I : Ideal R := IdealSheafData.stalk D q
    let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
    (Koszul.seqComplexTensor a (R ⧸ I)).homology n ≅
      (ModuleCat.restrictScalars φ).obj
        ((Koszul.seqComplexTensor (fun j => φ (a j)) B).homology n) := by
  let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
  let R := (T).presheaf.stalk q
  let B := (P).presheaf.stalk p
  let I : Ideal R := IdealSheafData.stalk D q
  let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
  letI : Algebra R B := φ.toAlgebra
  exact Koszul.homologyTensorCongr a
      (correspondenceRemainingImageComponentSupportStalkAlgEquiv
        f g h i z w v t p).toLinearEquiv n ≪≫
    Koszul.homologySeqComplexTensorRestrictScalarsIso a (ModuleCat.of B B) n

/-- The closed scalar quotient preserves every actual Koszul homology length. -/
theorem length_correspondenceRemainingImageComponentSupportKoszul (p : P) {r : ℕ}
    (a : Fin r → (T).presheaf.stalk (correspondenceRemainingSupportImagePoint f g h i z w v t p))
    (n : ℕ) :
    let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
    let R := (T).presheaf.stalk q
    let B := (P).presheaf.stalk p
    let I : Ideal R := IdealSheafData.stalk D q
    let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
    Module.length R ((Koszul.seqComplexTensor a (R ⧸ I)).homology n) =
      Module.length B ((Koszul.seqComplexTensor (fun j => φ (a j)) B).homology n) := by
  let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
  let R := (T).presheaf.stalk q
  let B := (P).presheaf.stalk p
  let I : Ideal R := IdealSheafData.stalk D q
  let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
  letI : Algebra R B := φ.toAlgebra
  let H := (Koszul.seqComplexTensor (fun j => φ (a j)) B).homology n
  letI : Module R H := Module.compHom H φ
  haveI : IsScalarTower R B H := IsScalarTower.of_compHom R B H
  let e : (Koszul.seqComplexTensor a (R ⧸ I)).homology n ≃ₗ[R] H :=
    (correspondenceRemainingImageComponentSupportKoszulIso f g h i z w v t p a n).toLinearEquiv
  exact e.length_eq.trans (Module.length_eq_of_surjective (M := H)
    (correspondenceRemainingSupportImageStalkMap_surjective f g h i z w v t p))

/-- Genuine coefficient realization for the full, possibly nonreduced component Euler sum. -/
theorem seqEuler_correspondenceRemainingImageComponentSupport (p : P) {r : ℕ}
    (a : Fin r → (T).presheaf.stalk (correspondenceRemainingSupportImagePoint f g h i z w v t p)) :
    let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
    let R := (T).presheaf.stalk q
    let B := (P).presheaf.stalk p
    let I : Ideal R := IdealSheafData.stalk D q
    let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
    Koszul.seqEuler a (R ⧸ I) = Koszul.seqEuler (fun j => φ (a j)) B := by
  unfold Koszul.seqEuler
  apply Finset.sum_congr rfl
  intro n _
  rw [length_correspondenceRemainingImageComponentSupportKoszul f g h i z w v t p a n]

end Stacks.Chow
