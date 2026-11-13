/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.NisnevichSingleCoproduct
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.NisnevichDerived
import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology

/-! # Bounded lifts along exact Nisnevich sheafification -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "a" => nisnevichSheafify k
set_option quotPrecheck false in
local notation "aD" => (a).mapDerivedCategory
local notation "U" => forgetDerivedFunctor k

/-- The actual upper truncation, regarded as a bounded-above derived object. -/
abbrev boundedTruncation (K : DerivedCategory PST) (b : ℤ) :
    DerivedCategory.Minus PST :=
  ⟨(DerivedCategory.TStructure.t.truncLE b).obj K, b, inferInstance⟩

variable [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

private theorem isIso_sheafification_truncation_forget (K : DerivedCategory.Minus NST)
    (b : ℤ) (hb : K.obj.IsLE b) :
    IsIso ((aD).map ((DerivedCategory.TStructure.t.truncLEι b).app ((U).obj K.obj))) := by
  let R := (U).obj K.obj
  let f := (DerivedCategory.TStructure.t.truncLEι b).app R
  let A := (aD)
  apply (DerivedCategory.isIso_iff _ (A.map f)).2
  intro i
  by_cases hi : i ≤ b
  · let : IsIso ((DerivedCategory.homologyFunctor PST i).map f) :=
      Stacks.TruncationLevel.isIso_homologyMap_truncLEι_app b i hi R
    exact ((a).isIso_homologyFunctor_map_mapDerivedCategory_map_iff f i).2 inferInstance
  · let e : A.obj R ≅ K.obj := asIso ((nisnevichDerivedAdjunction k).counit.app K.obj)
    let t := DerivedCategory.TStructure.t (C := NST)
    let : K.obj.IsLE b := hb
    have hT : (A.obj R).IsLE b := t.isLE_of_iso e.symm b
    let L := (boundedTruncation k R b).obj
    have hL : (A.obj L).IsLE b := by
      apply (DerivedCategory.isLE_iff _ b).2
      intro n hn
      exact ((a).map_isZero
        (DerivedCategory.isZero_of_isLE L b n hn)).of_iso
          (((a).mapDerivedCategoryHomologyIso n).app L)
    exact ((DerivedCategory.isLE_iff _ b).1 hL i (by omega)).isIso
      ((DerivedCategory.isLE_iff _ b).1 hT i (by omega)) _

/-- A bounded-above lift to transfer presheaves obtained by truncating derived sections. -/
def presheafLift (K : DerivedCategory.Minus NST) : DerivedCategory.Minus PST :=
  boundedTruncation k ((U).obj K.obj) K.property.choose

/-- Exact sheafification of the lift recovers the original sheaf complex. -/
@[no_expose]
def sheafificationPresheafLiftIso (K : DerivedCategory.Minus NST) :
    (derivedNisnevichSheafification k).obj (presheafLift k K) ≅ K := by
  let b := K.property.choose
  let f := (DerivedCategory.TStructure.t.truncLEι b).app ((U).obj K.obj)
  let : IsIso ((aD).map f) := isIso_sheafification_truncation_forget k K b K.property.choose_spec
  let e := asIso ((aD).map f) ≪≫ asIso ((nisnevichDerivedAdjunction k).counit.app K.obj)
  exact (ObjectProperty.fullyFaithfulι _).preimageIso e

/-- A sheaf complex with cohomology in degrees at most `b` admits a lift
to transfer presheaves with that same bound. -/
theorem exists_presheafLift_of_isLE (K : DerivedCategory.Minus NST) (b : ℤ)
    (hb : K.obj.IsLE b) :
    ∃ P : DerivedCategory.Minus PST, P.obj.IsLE b ∧
      Nonempty ((derivedNisnevichSheafification k).obj P ≅ K) := by
  let P := boundedTruncation k ((U).obj K.obj) b
  let f := (DerivedCategory.TStructure.t.truncLEι b).app ((U).obj K.obj)
  let : IsIso ((aD).map f) := isIso_sheafification_truncation_forget k K b hb
  let e := asIso ((aD).map f) ≪≫ asIso ((nisnevichDerivedAdjunction k).counit.app K.obj)
  exact ⟨P, inferInstanceAs (P.obj.IsLE b),
    ⟨(ObjectProperty.fullyFaithfulι _).preimageIso e⟩⟩

end AlgebraicGeometry.MotivicHomotopy
