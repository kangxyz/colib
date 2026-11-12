/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointSupport
public import Colib.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamily
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.DedekindBase

/-! # Flatness of the original principal support over the polynomial parameter -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor.PrincipalOrder

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
open PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  [IsAffine X.left] [IsIntegral X.left] {C V B : Scheme.{u}}
  [IsIntegral C] [IsNoetherian C] [V.IsQuasiAffine]
  (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (W : C.Opens) (r : Γ(C, W)) (b : B ⟶ W.toScheme)
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ W.ι)) (hb : b.appTop (W.topIso.inv r) = 1)

set_option quotPrecheck false in
local notation "t" => (q ≫ X.hom)
set_option quotPrecheck false in
local notation "U" => ambientUnitOpen (q ≫ X.hom) W.ι (W.topIso.inv r)

include hcover hb in
/-- The finite original support dominates the source cylinder, so its actual
parameter map to the polynomial spectrum is flat. -/
theorem familySupport_parameterFlat [Nonempty U] (z : parameterSpace t)
    (hz : principalCycle (parameterSpace t)
      (ambientRationalFunction t W.ι (W.topIso.inv r)) z ≠ 0) :
    Flat ((integralComponentAt z).subschemeι ≫ parameterProjection t) := by
  let L := SmoothSite.product X (polynomialAffineLine (.of k))
  let q' : parameterSpace t ⟶ L.left := parameterMap X.hom q
  let j' := parameterMap t j
  let : IsProper q' := MorphismProperty.of_isPullback
    (parameterMap_isPullback X.hom q) inferInstance
  let hAffine : IsAffine (parameterSpace X.hom) :=
    isAffine_of_isAffineHom (X := parameterSpace X.hom) (Y := X.left) (projection X.hom)
  let : IsAffine L.left := hAffine
  let : IsIntegral ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsIntegral X.left)
  let pX : X.left ⟶ Spec (.of k) := X.hom
  let : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    LocallyOfFiniteType.isLocallyNoetherian pX
  let : IsIntegral L.left := parameterSpace_isIntegral X.hom
  let : (parameterSpace (j ≫ t)).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ t))
  let : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion (parameterMap t j))
  let : SmoothOfRelativeDimension 1 (j' ≫ q') := by
    change SmoothOfRelativeDimension 1 (parameterMap t j ≫ parameterMap X.hom q)
    rw [parameterMap_comp]
    exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (parameterMap_isPullback X.hom (j ≫ q)) inferInstance
  let s := ambientUnitSection t W.ι (W.topIso.inv r)
  have hU := complement_subset_ambientUnitOpen t j W.ι b hcover (W.topIso.inv r) hb
  rw [lineMap_eq_parameterMap] at hU
  have hu := isUnit_ambientUnitSection t W.ι (W.topIso.inv r)
  have hd := support_dominates_component (X := L) q' j' U hU s hu z hz
  let d := (integralComponentAt z).subschemeι
  let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hd
  let : Surjective (d ≫ q') := ⟨Set.range_eq_univ.mp hd⟩
  have hsurj : Function.Surjective (⇑pX) :=
    fun y => ⟨genericPoint X.left, Subsingleton.elim (pX (genericPoint X.left)) y⟩
  let : Surjective X.hom := ⟨hsurj⟩
  let : Surjective (parameterProjection X.hom) := inferInstanceAs
    (Surjective (pullback.snd X.hom (Spec.map (CommRingCat.ofHom Polynomial.C))))
  have he : d ≫ parameterProjection t = (d ≫ q') ≫ parameterProjection X.hom :=
    ((congrArg (d ≫ ·) (parameterMap_snd X.hom q).symm).trans (Category.assoc _ _ _).symm)
  let : Surjective (d ≫ parameterProjection t) := he.symm ▸
    inferInstanceAs (Surjective ((d ≫ q') ≫ parameterProjection X.hom))
  have hdom : IsDominant (d ≫ parameterProjection t) := inferInstance
  exact flat_of_genericPoint_map_eq _
    (((tfae_isDominant_of_isIntegral (d ≫ parameterProjection t)).out 1 2).mp hdom)

end AlgebraicGeometry.Cor.PrincipalOrder
