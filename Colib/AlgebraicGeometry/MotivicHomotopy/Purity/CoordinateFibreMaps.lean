/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.CoordinateModel
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalSupport
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineOpenMaps

/-!
# Original fibre maps of the coordinate deformation

The polynomial presentation on the actual coborder identifies the original
deformation parameter and the homogeneous degree-one normal coordinates.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme Stacks.Conormal Stacks.MoreMorphisms

universe u

namespace Stacks.Deformation

section PolynomialModel

variable (R : Type u) [CommRing R] (m n : ℕ)

local notation "A" => MvPolynomial (Fin m ⊕ Fin n) R
local notation "B" => MvPolynomial (Fin m) R
local notation "P" => Polynomial (MvPolynomial (Fin n) B)
local notation "Y" => Spec (CommRingCat.of A)
local notation "Z" => Spec (CommRingCat.of B)
local notation "i" => coordinateEmbedding R m n
local notation "I" => coborderIdeal i
local notation "D" => deformationSpace I

local instance : IsClosedImmersion i := coordinateEmbedding_isClosedImmersion R m n

local instance : IsIso (i).coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion i

local instance : IsAffine (i).coborderRange.toScheme :=
  isAffine_of_isAffineHom (i).coborderRange.ι

local instance : IsAffine D :=
  have : IsAffineHom (deformationSpaceToBase I) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (extReesAlgebraSheaf I)
  isAffine_of_isAffineHom (deformationSpaceToBase I)

private abbrev coordinateCoborderTop : (i).coborderRange.toScheme.affineOpens :=
  ⟨⊤, isAffineOpen_top _⟩

private def coordinateCoborderAppTopEquiv :
    Γ(Y, ⊤) ≃+* Γ((i).coborderRange.toScheme, ⊤) :=
  (Scheme.Γ.mapIso (asIso (i).coborderRange.ι).op).commRingCatIsoToRingEquiv

private def coordinateCoborderRingEquiv :
    Γ((i).coborderRange.toScheme, ⊤) ≃+* MvPolynomial (Fin n) B :=
  (coordinateCoborderAppTopEquiv R m n).symm.trans (coordinateGlobalRingEquiv R m n)

private theorem coordinateCoborderIdeal_map :
    Ideal.map (coordinateCoborderRingEquiv R m n).toRingHom
        ((I).ideal (coordinateCoborderTop R m n)) = MvPolynomial.idealOfVars (Fin n) B := by
  let e := coordinateCoborderAppTopEquiv R m n
  have hker : (coordinateIdeal R m n).ideal (topAffineOpen R m n) =
      Ideal.comap e.toRingHom ((I).ideal (coordinateCoborderTop R m n)) := by
    rw [coordinateIdeal, Scheme.Hom.ker_apply, coborderIdeal_ideal, RingHom.comap_ker]
    apply congrArg RingHom.ker
    have h := congrArg (fun f : Z ⟶ Y => f.appTop.hom) (Scheme.Hom.liftCoborder_ι i).symm
    exact h
  have hmap : Ideal.map e.toRingHom ((coordinateIdeal R m n).ideal (topAffineOpen R m n)) =
      (I).ideal (coordinateCoborderTop R m n) := by
    rw [hker, Ideal.map_comap_of_surjective e.toRingHom e.surjective]
  rw [← hmap, Ideal.map_map]
  have he : (coordinateCoborderRingEquiv R m n).toRingHom.comp e.toRingHom =
      (coordinateGlobalRingEquiv R m n).toRingHom := by
    apply RingHom.ext
    intro a
    exact congrArg (coordinateGlobalRingEquiv R m n) (e.symm_apply_apply a)
  rw [he, coordinateIdeal_map_coordinateGlobalRingEquiv]

/-- Polynomial coordinates of the whole original closed-pair deformation. -/
def coordinateClosedPairPolynomialEquiv : P ≃+* Γ(D, ⊤) :=
  coordinateDeformationChartEquiv I (coordinateCoborderTop R m n)
    (coordinateCoborderRingEquiv R m n) (coordinateCoborderIdeal_map R m n)

private theorem paramChartOf_top_eq_paramGlobal {X : Scheme.{u}} (J : X.IdealSheafData) :
    paramChartOf J (⊤ : X.Opens) = paramGlobal J := by
  have h := paramGlobal_restrict J (⊤ : X.Opens)
  have hh : (homOfLE le_top : (⊤ : (deformationSpace J).Opens) ⟶ ⊤) = 𝟙 _ :=
    Subsingleton.elim _ _
  change (deformationSpace J).presheaf.map
    (homOfLE le_top : (⊤ : (deformationSpace J).Opens) ⟶ ⊤).op (paramGlobal J) = _ at h
  rw [hh, op_id] at h
  have h' := ConcreteCategory.congr_hom ((deformationSpace J).presheaf.map_id (op ⊤))
    (show Γ(deformationSpace J, ⊤) from paramGlobal J)
  exact h.symm.trans h'

private theorem appLE_top_top {Source Target : Scheme.{u}} (f : Source ⟶ Target) :
    f.appLE (⊤ : Target.Opens) (⊤ : Source.Opens) le_rfl = f.appTop :=
  Scheme.Hom.appLE_eq_app f

/-- The polynomial variable is the original global deformation parameter. -/
theorem coordinateClosedPairPolynomialEquiv_X :
    coordinateClosedPairPolynomialEquiv R m n Polynomial.X = paramGlobal I := by
  exact (coordinateDeformationChartEquiv_X I (coordinateCoborderTop R m n) _ _).trans
    (paramChartOf_top_eq_paramGlobal I)

private theorem coordinatePolynomialRingEquiv_rename_inl (a : B) :
    coordinatePolynomialRingEquiv R m n (MvPolynomial.rename Sum.inl a) = MvPolynomial.C a := by
  have h : (coordinatePolynomialRingEquiv R m n).toRingHom.comp
      ((MvPolynomial.rename (R := R) Sum.inl).toRingHom) =
      MvPolynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coordinatePolynomialRingEquiv, MvPolynomial.sumRingEquiv_C]
    · intro j
      simp [coordinatePolynomialRingEquiv, MvPolynomial.sumRingEquiv_X_inr]
  exact RingHom.congr_fun h a

/-- A coefficient from the centre ring is the pullback of its original ambient coordinate. -/
theorem coordinateClosedPairPolynomialEquiv_C_C (a : B) :
    coordinateClosedPairPolynomialEquiv R m n (Polynomial.C (MvPolynomial.C a)) =
      (deformationSpaceToBase I ≫ (i).coborderRange.ι).appTop
        (gammaEquiv R m n (MvPolynomial.rename Sum.inl a)) := by
  have hg : (coordinateGlobalRingEquiv R m n).symm (MvPolynomial.C a) =
      gammaEquiv R m n (MvPolynomial.rename Sum.inl a) := by
    apply (coordinateGlobalRingEquiv R m n).injective
    rw [RingEquiv.apply_symm_apply]
    change _ = coordinatePolynomialRingEquiv R m n
      ((gammaEquiv R m n).symm (gammaEquiv R m n (MvPolynomial.rename Sum.inl a)))
    rw [RingEquiv.symm_apply_apply, coordinatePolynomialRingEquiv_rename_inl]
  have hf := coordinateDeformationChartEquiv_C_C I (coordinateCoborderTop R m n)
    (coordinateCoborderRingEquiv R m n) (coordinateCoborderIdeal_map R m n) a
  change coordinateClosedPairPolynomialEquiv R m n (Polynomial.C (MvPolynomial.C a)) =
    (deformationSpaceToBase I).appTop ((coordinateCoborderAppTopEquiv R m n)
      ((coordinateGlobalRingEquiv R m n).symm (MvPolynomial.C a))) at hf
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact hf.trans (congrArg (fun a => (deformationSpaceToBase I).appTop
    ((coordinateCoborderAppTopEquiv R m n) a)) hg)

/-- The original normal coordinate pulls back to the parameter times its degree-one lift. -/
theorem coordinateClosedPairPolynomialEquiv_param_mul_C_X (j : Fin n) :
    (show Γ(D, ⊤) from paramGlobal I) * coordinateClosedPairPolynomialEquiv R m n
      (Polynomial.C (MvPolynomial.X j : MvPolynomial (Fin n) B)) =
      (deformationSpaceToBase I ≫ (i).coborderRange.ι).appTop
        (gammaEquiv R m n (MvPolynomial.X (Sum.inr j))) := by
  have hg : (coordinateGlobalRingEquiv R m n).symm (MvPolynomial.X j) =
      gammaEquiv R m n (MvPolynomial.X (Sum.inr j)) := by
    apply (coordinateGlobalRingEquiv R m n).injective
    rw [RingEquiv.apply_symm_apply]
    change _ = coordinatePolynomialRingEquiv R m n
      ((gammaEquiv R m n).symm (gammaEquiv R m n (MvPolynomial.X (Sum.inr j))))
    rw [RingEquiv.symm_apply_apply, coordinatePolynomialRingEquiv_X]
  have hf := coordinateDeformationChartEquiv_param_mul_C_X I (coordinateCoborderTop R m n)
    (coordinateCoborderRingEquiv R m n) (coordinateCoborderIdeal_map R m n) j
  change (show Γ(D, ⊤) from paramChartOf I (coordinateCoborderTop R m n).1) *
    coordinateClosedPairPolynomialEquiv R m n
      (Polynomial.C (MvPolynomial.X j : MvPolynomial (Fin n) B)) =
      (deformationSpaceToBase I).appTop ((coordinateCoborderAppTopEquiv R m n)
        ((coordinateGlobalRingEquiv R m n).symm (MvPolynomial.X j))) at hf
  have hp := coordinateDeformationChartEquiv_X I (coordinateCoborderTop R m n)
    (coordinateCoborderRingEquiv R m n) (coordinateCoborderIdeal_map R m n)
  change coordinateClosedPairPolynomialEquiv R m n Polynomial.X = _ at hp
  rw [← hp, coordinateClosedPairPolynomialEquiv_X] at hf
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact hf.trans (congrArg (fun a => (deformationSpaceToBase I).appTop
    ((coordinateCoborderAppTopEquiv R m n) a)) hg)

private theorem coordinateClosedPairOneSection_param :
    (closedPairOneSection i).appTop (paramGlobal I) = 1 := by
  have h := deformationOneSection_appLE_paramChartOf I (coordinateCoborderTop R m n) le_rfl
  change ((deformationOneSection I).appLE ⊤ ⊤ le_rfl).hom (paramChartOf I ⊤) = 1 at h
  have hp := coordinateDeformationChartEquiv_X I (coordinateCoborderTop R m n)
    (coordinateCoborderRingEquiv R m n) (coordinateCoborderIdeal_map R m n)
  change coordinateClosedPairPolynomialEquiv R m n Polynomial.X = _ at hp
  rw [← hp, coordinateClosedPairPolynomialEquiv_X] at h
  rw [appLE_top_top] at h
  rw [closedPairOneSection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h, map_one]

/-- The original one section evaluates the parameter at one and identifies the two sets
of normal coordinates. -/
theorem coordinateClosedPairOneSection_appTop :
    (closedPairOneSection i).appTop.hom.comp
        (coordinateClosedPairPolynomialEquiv R m n).toRingHom =
      ((gammaEquiv R m n).toRingHom.comp
        (coordinatePolynomialRingEquiv R m n).symm.toRingHom).comp
          (Polynomial.evalRingHom 1) := by
  apply Polynomial.ringHom_ext
  · have hbase (a : Γ(Y, ⊤)) :
        (closedPairOneSection i).appTop
          ((deformationSpaceToBase I ≫ (i).coborderRange.ι).appTop a) = a := by
      have h := congrArg (fun f : Y ⟶ Y => f.appTop) (closedPairOneSection_toAmbient i)
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at h
      exact ConcreteCategory.congr_hom h a
    intro a
    have hC (b : B) : (coordinatePolynomialRingEquiv R m n).symm (MvPolynomial.C b) =
        MvPolynomial.rename Sum.inl b :=
      (coordinatePolynomialRingEquiv R m n).injective
        ((RingEquiv.apply_symm_apply _ _).trans
          (coordinatePolynomialRingEquiv_rename_inl R m n b).symm)
    have hc : (closedPairOneSection i).appTop.hom.comp
        ((coordinateClosedPairPolynomialEquiv R m n).toRingHom.comp Polynomial.C) =
        ((gammaEquiv R m n).toRingHom.comp
          (coordinatePolynomialRingEquiv R m n).symm.toRingHom) := by
      apply MvPolynomial.ringHom_ext
      · intro b
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          coordinateClosedPairPolynomialEquiv_C_C, hC]
        exact hbase _
      · intro j
        have hj : (coordinatePolynomialRingEquiv R m n).symm (MvPolynomial.X j) =
            MvPolynomial.X (Sum.inr j) := by
          apply (coordinatePolynomialRingEquiv R m n).injective
          rw [RingEquiv.apply_symm_apply, coordinatePolynomialRingEquiv_X]
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hj]
        have hm := congrArg (closedPairOneSection i).appTop.hom
          (coordinateClosedPairPolynomialEquiv_param_mul_C_X R m n j)
        rw [map_mul, coordinateClosedPairOneSection_param, one_mul] at hm
        exact hm.trans (hbase _)
    simpa only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C] using
      RingHom.congr_fun hc a
  · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_one]
    exact (congrArg (closedPairOneSection i).appTop.hom
      (coordinateClosedPairPolynomialEquiv_X R m n)).trans
        (coordinateClosedPairOneSection_param R m n)

local notation "D₀" => deformationSpace (⊥ : Scheme.IdealSheafData Z)
local notation "q" => coordinateProjection R m n
local notation "F" => coordinateClosedPairPolynomialEquiv R m n

local instance : IsAffine D₀ :=
  have : IsAffineHom (deformationSpaceToBase (⊥ : Scheme.IdealSheafData Z)) :=
    Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase (extReesAlgebraSheaf _)
  isAffine_of_isAffineHom (deformationSpaceToBase _)

private abbrev coordinateCenterTop : (Z).affineOpens := ⟨⊤, isAffineOpen_top _⟩

private def centerΓEquiv : B ≃+* Γ(Z, ⊤) :=
  (ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv

/-- Polynomial coordinates of the actual deformation support. -/
def coordinateSupportPolynomialEquiv : Polynomial B ≃+* Γ(D₀, ⊤) :=
  (Polynomial.mapEquiv (centerΓEquiv R m)).trans
    (zeroIdealChartPolynomialEquiv (coordinateCenterTop R m))

/-- The support parameter is the original parameter on the zero-ideal deformation. -/
theorem coordinateSupportPolynomialEquiv_X :
    coordinateSupportPolynomialEquiv R m Polynomial.X =
      paramGlobal (⊥ : Scheme.IdealSheafData Z) := by
  change zeroIdealChartPolynomial (coordinateCenterTop R m) (Polynomial.X.map _) = _
  rw [Polynomial.map_X]
  rw [show zeroIdealChartPolynomial (coordinateCenterTop R m) Polynomial.X =
    paramChartOf (⊥ : Scheme.IdealSheafData Z) ⊤ from Polynomial.eval₂_X _ _]
  exact paramChartOf_top_eq_paramGlobal (⊥ : Scheme.IdealSheafData Z)

private theorem coordinateSupportPolynomialEquiv_C (b : B) :
    coordinateSupportPolynomialEquiv R m (Polynomial.C b) =
      (deformationSpaceToBase (⊥ : Scheme.IdealSheafData Z)).appTop (centerΓEquiv R m b) := by
  change zeroIdealChartPolynomial (coordinateCenterTop R m) ((Polynomial.C b).map _) = _
  rw [Polynomial.map_C]
  exact Polynomial.eval₂_C _ _

private theorem coordinateProjection_eq_constantCoeff :
    q = MvPolynomial.constantCoeff.comp (coordinatePolynomialRingEquiv R m n).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [coordinateProjection, coordinatePolynomialRingEquiv, MvPolynomial.sumRingEquiv_C]
  · intro j
    cases j with
    | inl j => simp [coordinateProjection, coordinatePolynomialRingEquiv,
        MvPolynomial.sumRingEquiv_X_inr]
    | inr j => simp [coordinateProjection, coordinatePolynomialRingEquiv_X]

/-- The original support map kills the normal coordinates and keeps the parameter. -/
theorem coordinateDeformationSupportMap_appTop :
    (deformationSupportMap i).appTop.hom.comp (F).toRingHom =
      (coordinateSupportPolynomialEquiv R m).toRingHom.comp
        (Polynomial.mapRingHom (MvPolynomial.constantCoeff :
          MvPolynomial (Fin n) B →+* B)) := by
  apply Polynomial.ringHom_ext
  · intro a
    have hc : (deformationSupportMap i).appTop.hom.comp ((F).toRingHom.comp Polynomial.C) =
        ((coordinateSupportPolynomialEquiv R m).toRingHom.comp Polynomial.C).comp
          MvPolynomial.constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro b
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          coordinateClosedPairPolynomialEquiv_C_C, MvPolynomial.constantCoeff_C,
          coordinateSupportPolynomialEquiv_C]
        have h := deformationSupportMap_toBase_assoc i (i).coborderRange.ι
        rw [Scheme.Hom.liftCoborder_ι] at h
        have h' := congrArg (fun f : D₀ ⟶ Y => f.appTop) h
        simp only [Scheme.Hom.comp_appTop, Category.assoc] at h'
        have ha := ConcreteCategory.congr_hom h'
          (gammaEquiv R m n (MvPolynomial.rename Sum.inl b))
        have hb : (i).appTop (gammaEquiv R m n (MvPolynomial.rename Sum.inl b)) =
            centerΓEquiv R m b := by
          apply (ConcreteCategory.bijective_of_isIso (ΓSpecIso (CommRingCat.of B)).hom).injective
          rw [gammaEquiv_coordinateEmbedding_appTop, RingEquiv.symm_apply_apply,
            coordinateProjection_rename_inl]
          exact (ΓSpecIso (CommRingCat.of B)).inv_hom_id_apply b |>.symm
        simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hb] using ha
      · intro j
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          MvPolynomial.constantCoeff_X, map_zero]
        have he : coordinateClosedPairPolynomialEquiv R m n
            (Polynomial.C (MvPolynomial.X j : MvPolynomial (Fin n) B)) =
            coordinateDeformationChartVar I (coordinateCoborderTop R m n)
              (coordinateCoborderRingEquiv R m n) (coordinateCoborderIdeal_map R m n) j :=
          coordinateDeformationChartEquiv_C_X I (coordinateCoborderTop R m n)
            (coordinateCoborderRingEquiv R m n) (coordinateCoborderIdeal_map R m n) j
        rw [he, coordinateDeformationChartVar]
        have h := deformationMap_appLE_chartIncl' (i).liftCoborder I ⊥
          (coborderIdeal_comap_liftCoborder i).le (coordinateCoborderTop R m n) 1
          (extReesOfMem I (coordinateCoborderTop R m n) 1
            ((coordinateCoborderRingEquiv R m n).symm (MvPolynomial.X j)) (by
              rw [pow_one]
              apply Ideal.symm_apply_mem_of_equiv_iff.2
              change MvPolynomial.X j ∈ Ideal.map (coordinateCoborderRingEquiv R m n).toRingHom _
              rw [coordinateCoborderIdeal_map]
              exact Ideal.subset_span ⟨j, rfl⟩)) le_rfl
        change ((deformationSupportMap i).appLE ⊤ ⊤ le_rfl).hom _ = _ at h
        rw [appLE_top_top] at h
        exact h.trans (chartIncl_eq_zero_of_ambient (⊥ : Scheme.IdealSheafData Z) ⊤ 1 _
          (extReesAmbient_bot_eq_zero_of_pos Z 1 (by omega) ⊤ _))
    simpa only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C] using
      RingHom.congr_fun hc a
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      coordinateClosedPairPolynomialEquiv_X, Polynomial.coe_mapRingHom, Polynomial.map_X,
      coordinateSupportPolynomialEquiv_X]
    have h := deformationMap_appLE_paramChartOf (i).liftCoborder I ⊥
      (coborderIdeal_comap_liftCoborder i).le (coordinateCoborderTop R m n) ⊤ le_rfl le_rfl
    change ((deformationSupportMap i).appLE (⊤ : (D).Opens) (⊤ : (D₀).Opens) le_rfl).hom
      (paramChartOf I ⊤) = paramChartOf (⊥ : Scheme.IdealSheafData Z) ⊤ at h
    rw [appLE_top_top, paramChartOf_top_eq_paramGlobal, paramChartOf_top_eq_paramGlobal] at h
    exact h

private def affineRingIsoSpec {X : Scheme.{u}} [IsAffine X] {T : Type u} [CommRing T]
    (e : T ≃+* Γ(X, ⊤)) : X ≅ Spec (.of T) :=
  X.isoSpec ≪≫ Scheme.Spec.mapIso e.toCommRingCatIso.op

private theorem affineRingIsoSpec_appTop {X : Scheme.{u}} [IsAffine X] {T : Type u} [CommRing T]
    (e : T ≃+* Γ(X, ⊤)) (a : T) :
    (affineRingIsoSpec e).hom.appTop ((ΓSpecIso (.of T)).inv a) = e a := by
  have h := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv e.toCommRingCatIso.hom
  change (ΓSpecIso (.of T)).inv ≫ (affineRingIsoSpec e).hom.appTop = _ at h
  exact ConcreteCategory.congr_hom h a

private theorem ext_toSpec_of_ringHom {X : Scheme.{u}} {T : Type u} [CommRing T]
    {f g : X ⟶ Spec (.of T)}
    (h : ∀ a : T, f.appTop ((ΓSpecIso (.of T)).inv a) =
      g.appTop ((ΓSpecIso (.of T)).inv a)) : f = g := by
  apply ext_of_isAffine
  apply (cancel_epi (ΓSpecIso (.of T)).inv).1
  exact CommRingCat.hom_ext (RingHom.ext h)

private theorem specMap_appTop_ΓSpecIso_inv {Source Target : CommRingCat.{u}}
    (f : Source ⟶ Target) (a : Source) :
    (Spec.map f).appTop ((ΓSpecIso Source).inv a) = (ΓSpecIso Target).inv (f a) := by
  have h := ConcreteCategory.congr_hom (ΓSpecIso_inv_naturality f).symm a
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  exact h

local notation "E" => RingEquiv.trans (Polynomial.mapEquiv (coordinatePolynomialRingEquiv R m n)) F
local notation "G" => coordinateSupportPolynomialEquiv R m

/-- The original closed-pair deformation is the polynomial cylinder of its ambient scheme. -/
def coordinateDeformationPolynomialIso : D ≅ Spec (.of (Polynomial A)) :=
  affineRingIsoSpec E

/-- The projection onto the centre coordinates of the original ambient scheme. -/
@[expose] def coordinateCentreProjection : Y ⟶ Z :=
  Spec.map (CommRingCat.ofHom ((MvPolynomial.rename (R := R) Sum.inl).toRingHom))

/-- Restriction to the original coordinate centre splits its coordinate projection. -/
theorem coordinateEmbedding_coordinateCentreProjection :
    i ≫ coordinateCentreProjection R m n = 𝟙 Z := by
  rw [coordinateEmbedding, coordinateCentreProjection, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact coordinateProjection_rename_inl R m n

/-- The projection onto the centre coordinates is smooth. -/
theorem smooth_coordinateCentreProjection : Smooth (coordinateCentreProjection R m n) := by
  apply HasRingHomProperty.Spec_iff.mpr
  let e := coordinatePolynomialRingEquiv R m n
  let a : CommRingCat.of B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom ((MvPolynomial.rename (R := R) Sum.inl).toRingHom)
  let e' : CommRingCat.of A ≅ CommRingCat.of (MvPolynomial (Fin n) B) :=
    RingEquiv.toCommRingCatIso (R := A) (S := MvPolynomial (Fin n) B) e
  have h : (a ≫ e'.hom).hom = (MvPolynomial.C : B →+* MvPolynomial (Fin n) B) :=
    RingHom.ext (coordinatePolynomialRingEquiv_rename_inl R m n)
  change a.hom.Smooth
  apply (RingHom.Smooth.respectsIso.cancel_right_isIso a e'.hom).mp
  change (a ≫ e'.hom).hom.Smooth
  rw [h]
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩

/-- The deformation cylinder comparison preserves the projection to the
centre coordinates of the original ambient scheme. -/
theorem coordinateDeformationPolynomialIso_centre :
    (coordinateDeformationPolynomialIso R m n).hom ≫
        (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫
          coordinateCentreProjection R m n) =
      deformationSpaceToBase I ≫ (i).coborderRange.ι ≫ coordinateCentreProjection R m n := by
  apply ext_toSpec_of_ringHom
  intro b
  let t : B →+* A := (MvPolynomial.rename (R := R) Sum.inl).toRingHom
  change ((coordinateDeformationPolynomialIso R m n).hom ≫
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫
        Spec.map (CommRingCat.ofHom t))).appTop ((ΓSpecIso (.of B)).inv b) =
    (deformationSpaceToBase I ≫ (i).coborderRange.ι ≫
      Spec.map (CommRingCat.ofHom t)).appTop ((ΓSpecIso (.of B)).inv b)
  rw [← Category.assoc (deformationSpaceToBase I), Scheme.Hom.comp_appTop,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, CommRingCat.comp_apply, specMap_appTop_ΓSpecIso_inv,
    specMap_appTop_ΓSpecIso_inv, coordinateDeformationPolynomialIso, affineRingIsoSpec_appTop]
  change F ((Polynomial.C (MvPolynomial.rename Sum.inl b)).map _) = _
  rw [Polynomial.map_C]
  have h := coordinatePolynomialRingEquiv_rename_inl R m n b
  exact (congrArg (fun a => F (Polynomial.C a)) h).trans
    (coordinateClosedPairPolynomialEquiv_C_C R m n b)

/-- The actual deformation support is the polynomial cylinder of the centre. -/
def coordinateSupportPolynomialIso : D₀ ≅ Spec (.of (Polynomial B)) :=
  affineRingIsoSpec G

/-- The polynomial support presentation has the original structural map. -/
theorem coordinateSupportPolynomialIso_projection :
    (coordinateSupportPolynomialIso R m).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) =
        deformationSpaceToBase (⊥ : Scheme.IdealSheafData Z) := by
  apply ext_toSpec_of_ringHom
  intro b
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [specMap_appTop_ΓSpecIso_inv, coordinateSupportPolynomialIso, affineRingIsoSpec_appTop]
  exact coordinateSupportPolynomialEquiv_C R m b

/-- The support comparison preserves the structure map to the coefficient ring. -/
theorem coordinateSupportPolynomialIso_over :
    (coordinateSupportPolynomialIso R m).hom ≫
        (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* B))) =
      deformationSpaceToBase (⊥ : Scheme.IdealSheafData Z) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* B)) := by
  rw [← Category.assoc, coordinateSupportPolynomialIso_projection]

/-- The actual support inclusion is the cylinder map of the original coordinate embedding. -/
theorem coordinateDeformationSupportMap_polynomialIso :
    deformationSupportMap i ≫ (coordinateDeformationPolynomialIso R m n).hom =
      (coordinateSupportPolynomialIso R m).hom ≫
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom q)) := by
  apply ext_toSpec_of_ringHom
  intro a
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, coordinateDeformationPolynomialIso, affineRingIsoSpec_appTop,
    specMap_appTop_ΓSpecIso_inv, coordinateSupportPolynomialIso, affineRingIsoSpec_appTop]
  have h := RingHom.congr_fun (coordinateDeformationSupportMap_appTop R m n)
    (a.map (coordinatePolynomialRingEquiv R m n).toRingHom)
  have hq : (a.map (coordinatePolynomialRingEquiv R m n).toRingHom).map
      MvPolynomial.constantCoeff = a.map q := by
    rw [Polynomial.map_map, ← coordinateProjection_eq_constantCoeff]
  exact h.trans (congrArg G hq)

private theorem eval_map_coordinatePolynomialRingEquiv (a : Polynomial A) (s : A) :
    (a.map (coordinatePolynomialRingEquiv R m n).toRingHom).eval
        (coordinatePolynomialRingEquiv R m n s) =
      coordinatePolynomialRingEquiv R m n (a.eval s) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply _ _

/-- The original ambient fibre map becomes the constant-one section in polynomial coordinates. -/
theorem coordinateClosedPairOneSection_polynomialIso :
    closedPairOneSection i ≫ (coordinateDeformationPolynomialIso R m n).hom =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : A))) := by
  apply ext_toSpec_of_ringHom
  intro a
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordinateDeformationPolynomialIso,
    affineRingIsoSpec_appTop, specMap_appTop_ΓSpecIso_inv]
  have h := RingHom.congr_fun (coordinateClosedPairOneSection_appTop R m n)
    (a.map (coordinatePolynomialRingEquiv R m n).toRingHom)
  have hEval := eval_map_coordinatePolynomialRingEquiv R m n a (1 : A)
  rw [map_one] at hEval
  exact h.trans (congrArg (fun b => gammaEquiv R m n
    ((coordinatePolynomialRingEquiv R m n).symm b)) hEval |>.trans
      (congrArg (gammaEquiv R m n) ((coordinatePolynomialRingEquiv R m n).symm_apply_apply _)))

/-- The zero fibre in the polynomial coordinates of the deformation space. -/
def coordinateZeroFibreMap : Y ⟶ D :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))) ≫
    (coordinateDeformationPolynomialIso R m n).inv

local instance : IsClosedImmersion (coordinateZeroFibreMap R m n) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)))) :=
    IsClosedImmersion.spec_of_surjective _ (fun a => ⟨Polynomial.C a, Polynomial.eval_C⟩)
  unfold coordinateZeroFibreMap
  infer_instance

private theorem coordinateZeroFibreMap_ker
    (p : Y ⟶ Spec (CommRingCat.of R)) [Smooth p] [Smooth (i ≫ p)] :
    (normalBundleToDeformation i p).ker = (coordinateZeroFibreMap R m n).ker := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [ker_normalBundleToDeformation, Scheme.Hom.ker_apply]
  have h₁ := zeroScheme_paramGlobal_ideal I (coordinateCoborderTop R m n)
  rw [← coordinateClosedPairPolynomialEquiv_X] at h₁
  have hE : E Polynomial.X = F Polynomial.X := by
    change F (Polynomial.X.map _) = F Polynomial.X
    rw [Polynomial.map_X]
  have h₂ : (coordinateZeroFibreMap R m n).appTop.hom.comp (E).toRingHom =
      (gammaEquiv R m n).toRingHom.comp (Polynomial.evalRingHom 0) := by
    apply RingHom.ext
    intro a
    have h := affineRingIsoSpec_appTop E a
    change (coordinateDeformationPolynomialIso R m n).hom.appTop
      ((ΓSpecIso (.of (Polynomial A))).inv a) = E a at h
    have hcomp :
        coordinateZeroFibreMap R m n ≫ (coordinateDeformationPolynomialIso R m n).hom =
          Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))) := by
      simp only [coordinateZeroFibreMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hh := congrArg (fun f : Y ⟶ Spec (CommRingCat.of (Polynomial A)) => f.appTop) hcomp
    rw [Scheme.Hom.comp_appTop] at hh
    have hv := ConcreteCategory.congr_hom hh ((ΓSpecIso (.of (Polynomial A))).inv a)
    rw [CommRingCat.comp_apply, h, specMap_appTop_ΓSpecIso_inv] at hv
    exact hv
  have h₃ : RingHom.ker ((coordinateZeroFibreMap R m n).appTop.hom.comp (E).toRingHom) =
      Ideal.span {Polynomial.X} := by
    rw [h₂, RingHom.ker_equiv_comp, Polynomial.ker_evalRingHom, map_zero, sub_zero]
  have h₄ : RingHom.ker (coordinateZeroFibreMap R m n).appTop.hom =
      Ideal.span {F Polynomial.X} := by
    let e := E
    let φ := (coordinateZeroFibreMap R m n).appTop.hom
    have hh : Ideal.map e.toRingHom (Ideal.comap e.toRingHom (RingHom.ker φ)) =
        RingHom.ker φ := Ideal.map_comap_of_surjective e.toRingHom e.surjective _
    rw [RingHom.comap_ker, h₃, Ideal.map_span, Set.image_singleton] at hh
    exact hh.symm.trans (congrArg (fun x => Ideal.span {x}) hE)
  have hparam := coordinateDeformationChartEquiv_X I (coordinateCoborderTop R m n)
    (coordinateCoborderRingEquiv R m n) (coordinateCoborderIdeal_map R m n)
  change F Polynomial.X = _ at hparam
  have h₁' : (Stacks.Divisors.zeroScheme D (Scheme.unitModule D) (F Polynomial.X)).ideal
      ⟨⊤, isAffineOpen_top D⟩ = Ideal.span {F Polynomial.X} :=
    h₁.trans (congrArg (fun x : Γ(D, ⊤) => Ideal.span {x}) hparam.symm)
  rw [← coordinateClosedPairPolynomialEquiv_X]
  exact h₁'.trans h₄.symm

section Normal

variable (p : Spec (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) ⟶
    Spec (CommRingCat.of R))
  [Smooth p] [Smooth (coordinateEmbedding R m n ≫ p)]

/-- The normal bundle is the original ambient affine space in the normal coordinates. -/
def coordinateNormalBundleIso : normalBundle i ≅ Y := by
  let e := coordinateZeroFibreMap_ker R m n p
  have := IsClosedImmersion.isIso_lift (coordinateZeroFibreMap R m n)
    (normalBundleToDeformation i p) e.symm
  exact asIso (IsClosedImmersion.lift (coordinateZeroFibreMap R m n)
    (normalBundleToDeformation i p) e.symm.le)

/-- The actual normal-bundle map becomes the constant-zero cylinder section. -/
theorem coordinateNormalBundleToDeformation_polynomialIso :
    normalBundleToDeformation i p ≫ (coordinateDeformationPolynomialIso R m n).hom =
      (coordinateNormalBundleIso R m n p).hom ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A))) := by
  have h : (coordinateNormalBundleIso R m n p).hom ≫ coordinateZeroFibreMap R m n =
      normalBundleToDeformation i p := IsClosedImmersion.lift_fac _ _ _
  rw [← h, Category.assoc]
  simp only [coordinateZeroFibreMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- On the centre the original zero section is evaluation at parameter zero. -/
theorem coordinateSupportZeroSection_polynomialIso :
    deformationZeroSectionBot Z ≫ (coordinateSupportPolynomialIso R m).hom =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : B))) := by
  apply ext_toSpec_of_ringHom
  intro a
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, coordinateSupportPolynomialIso,
    affineRingIsoSpec_appTop, specMap_appTop_ΓSpecIso_inv]
  have h := RingHom.congr_fun
    (deformationZeroSectionBot_appLE_comp_zeroIdealChartPolynomial (coordinateCenterTop R m)
      le_rfl) (a.map (centerΓEquiv R m).toRingHom)
  change ((deformationZeroSectionBot Z).appLE ⊤ ⊤ le_rfl).hom
    (G a) = (a.map (centerΓEquiv R m).toRingHom).eval 0 at h
  rw [appLE_top_top] at h
  have hev : (a.map (centerΓEquiv R m).toRingHom).eval 0 =
      centerΓEquiv R m (a.eval 0) := by
    exact Polynomial.eval_zero_map (centerΓEquiv R m).toRingHom a
  exact h.trans hev

/-- The normal-coordinate identification retains the original zero section of the normal bundle. -/
theorem coordinateNormalBundleIso_zeroSection :
    Scheme.Modules.vectorBundleZeroSection Z (conormalSheafDegreeOne i) ≫
      (coordinateNormalBundleIso R m n p).hom = i := by
  let e₀ := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)))
  let f := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom q))
  let e := (coordinateDeformationPolynomialIso R m n).hom
  let eZ := (coordinateSupportPolynomialIso R m).hom
  have : IsClosedImmersion e₀ :=
    IsClosedImmersion.spec_of_surjective _ (fun a => ⟨Polynomial.C a, Polynomial.eval_C⟩)
  have hq : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : B))) ≫ f = i ≫ e₀ := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  apply (cancel_mono e₀).mp
  calc
    _ = Scheme.Modules.vectorBundleZeroSection Z (conormalSheafDegreeOne i) ≫
          normalBundleToDeformation i p ≫ e :=
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        (coordinateNormalBundleToDeformation_polynomialIso R m n p).symm)
    _ = deformationZeroSectionBot Z ≫ deformationSupportMap i ≫ e := by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ e) (deformationZeroSectionBot_comp_deformationSupportMap i p).symm) |>.trans
          (Category.assoc _ _ _)
    _ = (deformationZeroSectionBot Z ≫ eZ) ≫ f :=
      (congrArg (deformationZeroSectionBot Z ≫ ·)
        (coordinateDeformationSupportMap_polynomialIso R m n)).trans (Category.assoc _ _ _).symm
    _ = i ≫ e₀ :=
      (congrArg (· ≫ f) (coordinateSupportZeroSection_polynomialIso R m)).trans hq

end Normal

local notation "baseMap" => Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* A))

/-- The deformation cylinder isomorphism is over the original coefficient base. -/
theorem coordinateDeformationPolynomialIso_over :
    (coordinateDeformationPolynomialIso R m n).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C.comp (MvPolynomial.C : R →+* A))) =
    deformationSpaceToBase I ≫ (i).coborderRange.ι ≫ baseMap := by
  apply ext_toSpec_of_ringHom
  intro r
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, specMap_appTop_ΓSpecIso_inv,
    coordinateDeformationPolynomialIso, affineRingIsoSpec_appTop]
  have hC : coordinatePolynomialRingEquiv R m n (MvPolynomial.C r) =
      MvPolynomial.C (MvPolynomial.C r) := by
    simp [coordinatePolynomialRingEquiv, MvPolynomial.sumRingEquiv_C]
  change F ((Polynomial.C (MvPolynomial.C r)).map _) = _
  rw [Polynomial.map_C]
  refine (congrArg (fun a => F (Polynomial.C a)) hC).trans ?_
  rw [coordinateClosedPairPolynomialEquiv_C_C, MvPolynomial.rename_C]
  have hbase : (baseMap).appTop ((ΓSpecIso (.of R)).inv r) =
      gammaEquiv R m n (MvPolynomial.C r) :=
    specMap_appTop_ΓSpecIso_inv _ _
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hbase]

section NormalBase

variable (p : Spec (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) ⟶
    Spec (CommRingCat.of R))
  [Smooth p] [Smooth (coordinateEmbedding R m n ≫ p)]

/-- The normal-coordinate identification is over the original coefficient base. -/
theorem coordinateNormalBundleIso_toBase :
    (coordinateNormalBundleIso R m n p).hom ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* A)) =
      normalBundleToBase i ≫ i ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* A)) := by
  have hs := congrArg (· ≫ Spec.map (CommRingCat.ofHom (Polynomial.C.comp
    (MvPolynomial.C : R →+* A)))) (coordinateNormalBundleToDeformation_polynomialIso R m n p)
  simp only [Category.assoc, coordinateDeformationPolynomialIso_over] at hs
  have hAmbient := congrArg (· ≫ (baseMap)) (normalBundleToDeformation_toAmbient i p)
  simp only [Category.assoc] at hAmbient
  rw [hAmbient] at hs
  rw [← Spec.map_comp] at hs
  have hEval : CommRingCat.ofHom (Polynomial.C.comp (MvPolynomial.C : R →+* A)) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : A)) =
      CommRingCat.ofHom (MvPolynomial.C : R →+* A) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact Polynomial.eval_C
  rw [hEval] at hs
  exact hs.symm

end NormalBase

end PolynomialModel

section NativeCylinder

variable (R : Type u) [Field R] (m n : ℕ)

local notation "A" => MvPolynomial (Fin m ⊕ Fin n) R
local notation "B" => MvPolynomial (Fin m) R
local notation "Y" => Spec (CommRingCat.of A)
local notation "Z" => Spec (CommRingCat.of B)
local notation "i" => coordinateEmbedding R m n
local notation "I" => coborderIdeal i
local notation "D" => deformationSpace I
local notation "D₀" => deformationSpace (⊥ : Scheme.IdealSheafData Z)
local notation "q" => coordinateProjection R m n

local instance : IsClosedImmersion i := coordinateEmbedding_isClosedImmersion R m n

open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
open _root_.AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent

local notation "Xₛ" => affineSite R A
local notation "Zₛ" => affineSite R B
local notation "S₀" => Spec (CommRingCat.of R)

/-- The coordinate embedding uses the actual projection of coefficient algebras. -/
@[expose] def coordinateProjectionAlgHom : A →ₐ[R] B :=
  MvPolynomial.aeval (fun j => Sum.elim MvPolynomial.X (fun _ => 0) j)

private theorem lineCylinderIso_eval
    {T : Type u} [CommRing T] [Algebra R T] [Algebra.Smooth R T] (r : R) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (algebraMap R T r))) ≫
        (lineCylinderIso (k := R) (R := T)).hom.left =
      (nativeAffineSection (.of R) (affineSite R T) r).left := by
  let X := affineSite R T
  let j : X ⟶ lineSite (k := R) (R := T) := homMk
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (algebraMap R T r)))) (by
      change Spec.map _ ≫ (Spec.map _ ≫ _) = _
      rw [← Category.assoc, ← Spec.map_comp]
      have h : CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T) ≫
          CommRingCat.ofHom (Polynomial.evalRingHom (algebraMap R T r)) = 𝟙 _ := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        exact Polynomial.eval_C
      rw [h, Spec.map_id, Category.id_comp]
      rfl)
  change (j ≫ (lineCylinderIso (k := R) (R := T)).hom).left = _
  have hm : j ≫ (lineCylinderIso (k := R) (R := T)).hom = nativeAffineSection (.of R) X r := by
    apply (cancel_mono (affineCylinderPolynomialIso (.of R) X).hom).mp
    dsimp only [lineCylinderIso, Iso.trans_hom, Iso.symm_hom]
    change (j ≫ (linePolynomialProductIso (k := R) (R := T)).hom ≫
        (affineCylinderPolynomialIso (.of R) X).inv) ≫
        (affineCylinderPolynomialIso (.of R) X).hom = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      nativeAffineSection_polynomialIso]
    apply product_hom_ext
    · rw [Category.assoc, linePolynomialProductIso_projection, polynomialAffineSection,
        productLift_fst]
      apply MorphismProperty.Over.Hom.ext
      change Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp]
      have h : CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T) ≫
          CommRingCat.ofHom (Polynomial.evalRingHom (algebraMap R T r)) = 𝟙 _ := by
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro a
        exact Polynomial.eval_C
      rw [h, Spec.map_id]
    · simp only [Category.assoc, polynomialAffineSection, productLift_snd]
      apply MorphismProperty.Over.Hom.ext
      change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (algebraMap R T r))) ≫
        (ambientIso (algebraMap R T)).hom ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R T)))
            (polynomialProjection (.of R)) =
          Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫
            Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom r))
      rw [ambientIso_snd, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
  exact congrArg (fun f : X ⟶ affineLineCylinder.obj X => f.left) hm

/-- The actual coordinate deformation identified with the native affine-line cylinder. -/
@[expose] def coordinateDeformationCylinderIso : D ≅ (affineLineCylinder.obj Xₛ).left :=
  coordinateDeformationPolynomialIso R m n ≪≫
    (forgetScheme S₀).mapIso (lineCylinderIso (k := R) (R := A))

/-- The native cylinder comparison preserves the original centre coordinates. -/
theorem coordinateDeformationCylinderIso_centre :
    (coordinateDeformationCylinderIso R m n).hom ≫
        (((projection (additiveGroupObject S₀)).app Xₛ).left ≫
          coordinateCentreProjection R m n) =
      deformationSpaceToBase I ≫ (i).coborderRange.ι ≫ coordinateCentreProjection R m n := by
  have h := congrArg (fun f => f.left) (lineCylinderIso_projection (k := R) (R := A))
  change (lineCylinderIso (k := R) (R := A)).hom.left ≫
      ((projection (additiveGroupObject S₀)).app Xₛ).left =
    Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) at h
  change ((coordinateDeformationPolynomialIso R m n).hom ≫
      (lineCylinderIso (k := R) (R := A)).hom.left) ≫ _ = _
  rw [Category.assoc, ← Category.assoc (lineCylinderIso (k := R) (R := A)).hom.left, h]
  exact coordinateDeformationPolynomialIso_centre R m n

/-- The actual support identified with the native affine-line cylinder of the centre. -/
@[expose] def coordinateSupportCylinderIso : D₀ ≅ (affineLineCylinder.obj Zₛ).left :=
  coordinateSupportPolynomialIso R m ≪≫
    (forgetScheme S₀).mapIso (lineCylinderIso (k := R) (R := B))

/-- The support-cylinder comparison preserves the original projection to its centre. -/
theorem coordinateSupportCylinderIso_projection :
    (coordinateSupportCylinderIso R m).hom ≫
        ((projection (additiveGroupObject S₀)).app Zₛ).left =
      deformationSpaceToBase (⊥ : Scheme.IdealSheafData Z) := by
  have h := congrArg (fun f => f.left) (lineCylinderIso_projection (k := R) (R := B))
  change (lineCylinderIso (k := R) (R := B)).hom.left ≫
    ((projection (additiveGroupObject S₀)).app Zₛ).left =
      Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) at h
  change ((coordinateSupportPolynomialIso R m).hom ≫
      (lineCylinderIso (k := R) (R := B)).hom.left) ≫ _ = _
  rw [Category.assoc, h, coordinateSupportPolynomialIso_projection]

/-- The support map is the original coordinate embedding on native affine cylinders. -/
theorem coordinateDeformationSupportMap_cylinderIso :
    deformationSupportMap i ≫ (coordinateDeformationCylinderIso R m n).hom =
      (coordinateSupportCylinderIso R m).hom ≫
        (affineLineCylinder.map (affineMorphism (coordinateProjectionAlgHom R m n))).left := by
  have h := congrArg (fun f => f.left) (lineCylinderIso_naturality
    (coordinateProjectionAlgHom R m n))
  change Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom q)) ≫
      (lineCylinderIso (k := R) (R := A)).hom.left =
    (lineCylinderIso (k := R) (R := B)).hom.left ≫
      (affineLineCylinder.map (affineMorphism (coordinateProjectionAlgHom R m n))).left at h
  change deformationSupportMap i ≫ (coordinateDeformationPolynomialIso R m n).hom ≫
      (lineCylinderIso (k := R) (R := A)).hom.left =
    ((coordinateSupportPolynomialIso R m).hom ≫
      (lineCylinderIso (k := R) (R := B)).hom.left) ≫ _
  rw [← Category.assoc, coordinateDeformationSupportMap_polynomialIso, Category.assoc, h,
    Category.assoc]

/-- The original ambient fibre at one becomes the native constant-one section. -/
theorem coordinateClosedPairOneSection_cylinderIso :
    closedPairOneSection i ≫ (coordinateDeformationCylinderIso R m n).hom =
      (nativeAffineSection (.of R) Xₛ 1).left := by
  change closedPairOneSection i ≫ (coordinateDeformationPolynomialIso R m n).hom ≫
    (lineCylinderIso (k := R) (R := A)).hom.left = _
  rw [← Category.assoc, coordinateClosedPairOneSection_polynomialIso]
  simpa only [map_one] using lineCylinderIso_eval R (T := A) 1

variable (p : Spec (CommRingCat.of (MvPolynomial (Fin m ⊕ Fin n) R)) ⟶
    Spec (CommRingCat.of R))
  [Smooth p] [Smooth (coordinateEmbedding R m n ≫ p)]

/-- The actual normal-bundle fibre becomes the native constant-zero section. -/
theorem coordinateNormalBundleToDeformation_cylinderIso :
    normalBundleToDeformation i p ≫ (coordinateDeformationCylinderIso R m n).hom =
      (coordinateNormalBundleIso R m n p).hom ≫ (nativeAffineSection (.of R) Xₛ 0).left := by
  change normalBundleToDeformation i p ≫ (coordinateDeformationPolynomialIso R m n).hom ≫
    (lineCylinderIso (k := R) (R := A)).hom.left = _
  rw [← Category.assoc, coordinateNormalBundleToDeformation_polynomialIso, Category.assoc]
  have h := lineCylinderIso_eval R (T := A) 0
  rw [map_zero] at h
  rw [h]

end NativeCylinder

end Stacks.Deformation

end
