/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.PlusConstruction.UnivSubtype
public import Colib.Topology.PlusConstruction.CommonUniverse
public import Colib.Topology.PlusConstruction.ClassicalCWUniqueness
public import Colib.Topology.CWComplex.UniverseTransport

/-! # Classical CW plus uniqueness in a common coefficient universe

The original spaces and continuous maps may occupy different universes. The
coefficient hypothesis ranges over their displayed common universe. Actual CW
structures and original based certificates are transported by the canonical
ULift and whole-space subtype homeomorphisms; the comparison and its ordinary
uniqueness are then returned to the original spaces.

Adapted from Quillen's `ClassicalCWUniquenessUniverseLift.lean`.
-/
@[expose] public section

open Topology

open FundamentalGroupoid.LocalCoefficients
open Topology.PlusConstruction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v w z
namespace Topology.IsPlusConstruction
open Topology.PlusConstruction

variable {X₀ : Type u} {X₁ : Type v} {X₂ : Type w}
  [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
  [T2Space X₀] [T2Space X₁] [T2Space X₂]
  (A : Set X₀) (B : Set X₁) (C : Set X₂)
  [CWComplex A] [CWComplex B] [CWComplex C]

include A B C in
/-- Comparison on the original CW spaces, using coefficients in the displayed common
universe and no supplied covering, domination or replacement-space data. -/
theorem exists_classicalCWComparison_commonUniverse
    (f : C(A, B)) (g : C(A, C))
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, v, max u v w z} f γ N)
    (hg : IsPlusConstruction.{u, w, max u v w z} g δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C, (h.toFun.comp f).Homotopic g := by
  let AU := ULift.{max u v w z} A
  let BU := ULift.{max u v w z} B
  let CU := ULift.{max u v w z} C
  let AS : Set AU := Set.univ
  let BS : Set BU := Set.univ
  let CS : Set CU := Set.univ
  let := CWComplex.uliftSubtypeCWComplex.{u, max u v w z} A a
  let := CWComplex.uliftSubtypeCWComplex.{v, max u v w z} B b
  let := CWComplex.uliftSubtypeCWComplex.{w, max u v w z} C c
  let fU : C(AU, BU) := UniverseLift.map.{u, v, max u v w z} f
  let gU : C(AU, CU) := UniverseLift.map.{u, w, max u v w z} g
  let γU := γ.map continuous_uliftUp
  let δU := δ.map continuous_uliftUp
  let NU := N.map (HomotopyGroup.homeomorphPiEquiv
    (Homeomorph.ulift.{max u v w z, u} (X := A)).symm
      (x := a) (y := ULift.up a) rfl 0).toMonoidHom
  have hfU : IsPlusConstruction fU γU NU :=
    CommonUniverse.isPlusConstruction.{u, v, max w z} f γ N hf
  have hgU : IsPlusConstruction gU δU NU :=
    CommonUniverse.isPlusConstruction.{u, w, max v z} g δ N hg
  let fS : TopCat.of AS ⟶ TopCat.of BS := TopCat.ofHom (UnivSubtype.map fU)
  let gS : TopCat.of AS ⟶ TopCat.of CS := TopCat.ofHom (UnivSubtype.map gU)
  obtain ⟨q, Hq⟩ := exists_classicalCWComparison AS BS CS fS gS
    (UnivSubtype.up AU (ULift.up a)) (UnivSubtype.up BU (ULift.up b))
    (UnivSubtype.up CU (ULift.up c)) (UnivSubtype.liftPath fU γU)
    (UnivSubtype.liftPath gU δU) (UnivSubtype.liftSubgroup NU)
    (UnivSubtype.isPlusConstruction fU γU NU hfU)
    (UnivSubtype.isPlusConstruction gU δU NU hgU)
  let eA : AS ≃ₜ A := (Homeomorph.Set.univ AU).trans Homeomorph.ulift
  let eB : BS ≃ₜ B := (Homeomorph.Set.univ BU).trans Homeomorph.ulift
  let eC : CS ≃ₜ C := (Homeomorph.Set.univ CU).trans Homeomorph.ulift
  let h := eB.symm.toHomotopyEquiv.trans (q.trans eC.toHomotopyEquiv)
  refine ⟨h, ⟨?_⟩⟩
  let H' := (ContinuousMap.Homotopy.refl eC.toHomotopyEquiv.toFun).comp Hq.some
  exact (H'.compContinuousMap eA.symm.toHomotopyEquiv.toFun).cast rfl rfl

include A B in
omit [T2Space X₂] [CWComplex C] in
/-- Ordinary cancellation retains the original maps, even when the arbitrary target
space and the two actual CW spaces lie in different universes. -/
def classicalCWHomotopyCancelCommonUniverse
    (f : C(A, B)) (a : A) (b : B) (γ : Path (f a) b)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, v, max u v w z} f γ N)
    {Y : Type w} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f).Homotopy (h₁.comp f)) : h₀.Homotopy h₁ := by
  let AU := ULift.{max u v w z} A
  let BU := ULift.{max u v w z} B
  let YU := ULift.{max u v w z} Y
  let AS : Set AU := Set.univ
  let BS : Set BU := Set.univ
  let := CWComplex.uliftSubtypeCWComplex.{u, max u v w z} A a
  let := CWComplex.uliftSubtypeCWComplex.{v, max u v w z} B b
  let fU : C(AU, BU) := UniverseLift.map.{u, v, max u v w z} f
  let γU := γ.map continuous_uliftUp
  let NU := N.map (HomotopyGroup.homeomorphPiEquiv
    (Homeomorph.ulift.{max u v w z, u} (X := A)).symm
      (x := a) (y := ULift.up a) rfl 0).toMonoidHom
  have hfU : IsPlusConstruction fU γU NU :=
    CommonUniverse.isPlusConstruction.{u, v, max w z} f γ N hf
  let fS : TopCat.of AS ⟶ TopCat.of BS := TopCat.ofHom (UnivSubtype.map fU)
  let eA : AS ≃ₜ A := (Homeomorph.Set.univ AU).trans Homeomorph.ulift
  let eB : BS ≃ₜ B := (Homeomorph.Set.univ BU).trans Homeomorph.ulift
  let h₀S : C(BS, YU) := (UniverseLift.up Y).comp (h₀.comp eB.toHomotopyEquiv.toFun)
  let h₁S : C(BS, YU) := (UniverseLift.up Y).comp (h₁.comp eB.toHomotopyEquiv.toFun)
  let HU := (ContinuousMap.Homotopy.refl (UniverseLift.up Y)).comp H
  have HS : (h₀S.comp fS.hom).Homotopy (h₁S.comp fS.hom) :=
    (HU.compContinuousMap eA.toHomotopyEquiv.toFun).cast rfl rfl
  let K := classicalCWHomotopyCancel AS BS fS
    (UnivSubtype.up AU (ULift.up a)) (UnivSubtype.up BU (ULift.up b))
    (UnivSubtype.liftPath fU γU) (UnivSubtype.liftSubgroup NU)
    (UnivSubtype.isPlusConstruction fU γU NU hfU) h₀S h₁S HS
  let K' := (ContinuousMap.Homotopy.refl (UniverseLift.down Y)).comp K
  exact (K'.compContinuousMap eB.symm.toHomotopyEquiv.toFun).cast rfl rfl

include A B in
omit [T2Space X₂] [CWComplex C] in
/-- Comparisons under the original source are ordinarily homotopic in the original
arbitrary target; no extra regularity or CW structure on that target is used. -/
theorem homotopic_classicalCWComparisons_commonUniverse
    (f : C(A, B)) (a : A) (b : B) (γ : Path (f a) b)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, v, max u v w z} f γ N)
    {Y : Type w} [TopologicalSpace Y] (g : C(A, Y)) (h₀ h₁ : C(B, Y))
    (H₀ : (h₀.comp f).Homotopic g) (H₁ : (h₁.comp f).Homotopic g) :
    h₀.Homotopic h₁ :=
  ⟨classicalCWHomotopyCancelCommonUniverse A B f a b γ N hf h₀ h₁
    (H₀.some.trans H₁.some.symm)⟩

include A B C in
/-- Plus uniqueness for differently sized actual CW spaces with the displayed common
coefficient universe, returned as an equivalence and ordinary homotopies of original maps. -/
theorem classicalCWPlusUnique_commonUniverse
    (f : C(A, B)) (g : C(A, C))
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, v, max u v w z} f γ N)
    (hg : IsPlusConstruction.{u, w, max u v w z} g δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f).Homotopic g ∧
        ∀ k : C(B, C), (k.comp f).Homotopic g → k.Homotopic h.toFun := by
  obtain ⟨h, H⟩ := exists_classicalCWComparison_commonUniverse A B C f g a b c γ δ N hf hg
  exact ⟨h, H, fun k Hk ↦
    homotopic_classicalCWComparisons_commonUniverse A B f a b γ N hf g k h.toFun Hk H⟩

end Topology.IsPlusConstruction

namespace Topology.IsPlusConstruction

/-- The original successor-universe certificate yields uniqueness on the original
source and target CW subtypes, with no supplied geometric data. -/
theorem classicalCWPlusUnique_successor
    {X₀ : Type u} {X₁ X₂ : Type (u + 1)}
    [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
    [T2Space X₀] [T2Space X₁] [T2Space X₂]
    (A : Set X₀) (B : Set X₁) (C : Set X₂)
    [CWComplex A] [CWComplex B] [CWComplex C]
    (f : C(A, B)) (g : C(A, C))
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u + 1, u + 1} f γ N)
    (hg : IsPlusConstruction.{u, u + 1, u + 1} g δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f).Homotopic g ∧
        ∀ k : C(B, C), (k.comp f).Homotopic g → k.Homotopic h.toFun :=
  classicalCWPlusUnique_commonUniverse.{u, u + 1, u + 1, 0} A B C f g a b c γ δ N hf hg

end Topology.IsPlusConstruction
