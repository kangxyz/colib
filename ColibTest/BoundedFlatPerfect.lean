/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectQuasiCompact
public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFreeFlat
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ReflexiveFactorization

/-! # Actual Bounded Above Flat Perfect Model Consumers

These signatures retain upper term bounds only, native sheaf complexes, quotient cofibrations,
actual chain maps, constructed cylinders and every connective degree, explicitly including zero.
No relative replacement or K-equivalence hypothesis is present.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry AlgebraicGeometry.RingedSpace StrictlyPerfect
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

example (X : RingedSpace.{u, u}) (K : CochainComplex (OXMod.{u, u, u} X) ℤ) :
    boundedAboveFlatPerfectComplex X K ↔
      IsPerfectComplex K ∧ (∃ b : ℤ, K.IsStrictlyLE b) ∧
        ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (K.X n) := Iff.rfl

example (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (hK : boundedAboveFlatPerfectComplex X.toRingedSpace K) (n : ℤ) :
    ∀ x : X,
      letI : Module (X.presheaf.stalk x) ((K.X n).presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) (K.X n).val x
      Module.Flat (X.presheaf.stalk x) ((K.X n).presheaf.stalk x) :=
  (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf (K.X n)).1 (hK.2.2 n)

example (X : RingedSpace.{u, u})
    {S : ShortComplex (CochainComplex (OXMod.{u, u, u} X) ℤ)} (hS : S.ShortExact)
    (h₁ : boundedAboveFlatPerfectComplex X S.X₁)
    (h₃ : boundedAboveFlatPerfectComplex X S.X₃) : boundedAboveFlatPerfectComplex X S.X₂ :=
  boundedAboveFlatPerfectComplex_of_shortExact hS h₁ h₃

example (X : RingedSpace.{u, u}) {K : CochainComplex (OXMod.{u, u, u} X) ℤ}
    (hK : boundedAboveFlatPerfectComplex X K) (n : ℤ) :
    boundedAboveFlatPerfectComplex X (K⟦n⟧) := boundedAboveFlatPerfectComplex_shift hK n

example (X : RingedSpace.{u, u}) {K L : CochainComplex (OXMod.{u, u, u} X) ℤ}
    (hK : boundedAboveFlatPerfectComplex X K) (hL : boundedAboveFlatPerfectComplex X L)
    (f : K ⟶ L) : boundedAboveFlatPerfectComplex X (CochainComplex.mappingCone f) :=
  boundedAboveFlatPerfectComplex_mappingCone hK hL f

example (X : RingedSpace.{u, u}) :
    ExactStructure (boundedAboveFlatPerfectComplex X).FullSubcategory :=
  boundedAboveFlatPerfectExactStructure X

example (X : RingedSpace.{u, u})
    {K L : (boundedAboveFlatPerfectComplex X).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectWaldhausen X).cof f ↔
      ∃ (Q : CochainComplex (OXMod.{u, u, u} X) ℤ)
        (_ : boundedAboveFlatPerfectComplex X Q) (p : L.obj ⟶ Q) (h : f.hom ≫ p = 0),
        (ShortComplex.mk f.hom p h).ShortExact :=
  boundedAboveFlatPerfectWaldhausen_cof_iff X f

example (X : RingedSpace.{u, u})
    {K L : (boundedAboveFlatPerfectComplex X).FullSubcategory} (f : K ⟶ L) :
    (boundedAboveFlatPerfectWaldhausen X).weq f ↔ QuasiIso f.hom :=
  boundedAboveFlatPerfectWaldhausen_weq_iff X f

example (X : RingedSpace.{u, u})
    {K L : (boundedAboveFlatPerfectComplex X).FullSubcategory} (f : K ⟶ L) :
    ((boundedAboveFlatPerfectInclusion X).map f).hom = f.hom := rfl

example (X : RingedSpace.{u, u}) :
    Waldhausen.IsExact (boundedAboveFlatPerfectWaldhausen X).cof
      (boundedAboveFlatPerfectWaldhausen X).weq
      (perfectComplexesWaldhausen X).cof (perfectComplexesWaldhausen X).weq
      (boundedAboveFlatPerfectInclusion X) := boundedAboveFlatPerfectInclusion_isExact X

example (X : RingedSpace.{u, u})
    (N : Waldhausen.Fibration.NestedWeakEquivalences (boundedAboveFlatPerfectWaldhausen X)) :
    Waldhausen.Fibration.RowFactorization.JointData N := boundedAboveFlatPerfectJointData X N

example (X : RingedSpace.{u, u})
    (N : Waldhausen.Fibration.NestedWeakEquivalences (boundedAboveFlatPerfectWaldhausen X)) :
    Waldhausen.Fibration.RowFactorization.SecondEndpointSection N
      (boundedAboveFlatPerfectJointData X N) :=
  boundedAboveFlatPerfectJointData_secondEndpointSection X N

example (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (hK : IsPerfectComplex (X := X.toRingedSpace) K) (b : ℤ) [K.IsLE b] :
    ∃ (P : CochainComplex X.Modules ℤ) (p : P ⟶ K),
      QuasiIso p ∧ boundedAboveFlatPerfectComplex X.toRingedSpace P ∧ P.IsStrictlyLE b :=
  @exists_boundedAboveFlatPerfectComplex_of_isLE X.toRingedSpace K hK b ‹K.IsLE b›

example (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (hK : IsPerfectComplex (X := X.toRingedSpace) K) (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (P : CochainComplex X.Modules ℤ) (p : P ⟶ K),
      (∀ n, Epi (p.f n)) ∧ QuasiIso p ∧
        boundedAboveFlatPerfectComplex X.toRingedSpace P ∧ P.IsStrictlyLE b :=
  @exists_epi_boundedAboveFlatPerfectComplex_of_isStrictlyLE
    X.toRingedSpace K hK b ‹K.IsStrictlyLE b›

example (X : Scheme.{u}) {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (b : ℤ) [K.IsStrictlyLE b] :
    (@boundedAboveMapToTruncLE X.toRingedSpace K L f b ‹K.IsStrictlyLE b›) ≫
      L.ιTruncLE b = f :=
  @boundedAboveMapToTruncLE_comp X.toRingedSpace K L f b ‹K.IsStrictlyLE b›

example (X : Scheme.{u}) (n : ℕ) :
    X.toRingedSpace.boundedAboveFlatPerfectK n →*
      (perfectComplexesWaldhausen X.toRingedSpace).K n :=
  X.toRingedSpace.boundedAboveFlatPerfectToPerfectKMap n

example (X : Scheme.{u}) :
    X.toRingedSpace.boundedAboveFlatPerfectK 0 →*
      (perfectComplexesWaldhausen X.toRingedSpace).K 0 :=
  X.toRingedSpace.boundedAboveFlatPerfectToPerfectKMap 0

example (X : Scheme.{u}) {K : CochainComplex X.Modules ℤ}
    (hK : boundedFiniteLocallyFreeComplex X K) :
    boundedAboveFlatPerfectComplex X.toRingedSpace K :=
  boundedAboveFlatPerfectComplex_of_boundedFiniteLocallyFree hK

example (X : Scheme.{u}) (n : ℕ) :
    (X.toRingedSpace.boundedAboveFlatPerfectToPerfectKMap n).comp
      (Scheme.boundedFiniteLocallyFreeToFlatKMap X n) =
        Scheme.boundedFiniteLocallyFreeToPerfectKMap X n :=
  Scheme.boundedAboveFlatPerfectToPerfectKMap_comp X n

example (X : Scheme.{u}) :
    (X.toRingedSpace.boundedAboveFlatPerfectToPerfectKMap 0).comp
      (Scheme.boundedFiniteLocallyFreeToFlatKMap X 0) =
        Scheme.boundedFiniteLocallyFreeToPerfectKMap X 0 :=
  Scheme.boundedAboveFlatPerfectToPerfectKMap_comp X 0

example (X : Scheme.{u}) :
    Waldhausen.Fibration.RowFactorization.JointData
      (Waldhausen.Fibration.NestedWeakEquivalences.refl
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) :=
  boundedAboveFlatPerfectJointData X.toRingedSpace _

example (X : RingedSpace.{u, u})
    {K L : (boundedAboveFlatPerfectComplex X).FullSubcategory} (f : K ⟶ L) :
    (perfectComplexesWaldhausen X).weq ((boundedAboveFlatPerfectInclusion X).map f) ↔
      (boundedAboveFlatPerfectWaldhausen X).weq f :=
  boundedAboveFlatPerfectInclusion_weq_iff X f

example (X : Scheme.{u}) [CompactSpace X] (K : CochainComplex X.Modules ℤ)
    (hK : IsPerfectComplex (X := X.toRingedSpace) K) :
    ∃ (P : CochainComplex X.Modules ℤ) (p : P ⟶ K),
      QuasiIso p ∧ boundedAboveFlatPerfectComplex X.toRingedSpace P :=
  exists_boundedAboveFlatPerfectComplex_of_quasiCompact K hK

example (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (hp : IsPerfectComplex (X := X.toRingedSpace) K) (hb : ∃ b : ℤ, K.IsStrictlyLE b)
    (hf : ∀ n : ℤ, ∀ x : X,
      letI : Module (X.presheaf.stalk x) ((K.X n).presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) (K.X n).val x
      Module.Flat (X.presheaf.stalk x) ((K.X n).presheaf.stalk x)) :
    boundedAboveFlatPerfectComplex X.toRingedSpace K :=
  ⟨hp, hb, fun n =>
    (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf (K.X n)).2 (hf n)⟩
