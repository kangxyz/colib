/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedAdjunction
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModelCounit
import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Exact Nisnevich sheafification on the derived categories with transfers

The exact sheafification is left adjoint to the total right derived
inclusion of transfer sheaves. The counit is invertible, as is seen
on the original termwise counit on a K-injective resolution.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.DerivedModel

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "a" => nisnevichSheafify k
local notation "U" => SheafWithTransfers.forgetDerivedFunctor k
local notation "c" => ComplexShape.up ℤ

set_option quotPrecheck false in
local notation "Qp" =>
  (DerivedCategory.Q (C := SheafWithTransfers.LargePresheaves k))

set_option quotPrecheck false in
local notation "Qs" =>
  (DerivedCategory.Q (C := SheafWithTransfers.LargeSheaves k))

/-- The Nisnevich adjunction in the native arbitrary-model presentation. -/
def nisnevichDerivedAdjunctionAux :
    derivedFunctorOfExact a Qs Qp ⊣ U :=
  adjunctionOfExact a Qs Qp (nisnevichSheafificationAdjunction k)
    U (SheafWithTransfers.forgetDerivedUnit k)

/-- The arbitrary-model homotopy localization agrees with the native quotient. -/
def homotopyLocalizationQIso {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] :
    homotopyLocalization (DerivedCategory.Q (C := A)) ≅ DerivedCategory.Qh := by
  let Q := DerivedCategory.Q (C := A)
  let q := HomotopyCategory.quotient A c
  let h := homotopyLocalization Q
  let h' := DerivedCategory.Qh (C := A)
  let r := homotopic A c
  exact CategoryTheory.Quotient.natIsoLift r (show q ⋙ h ≅ q ⋙ h' from
    homotopyLocalizationQuotientIso Q ≪≫ (DerivedCategory.quotientCompQhIso A).symm)

/-- The exact derived left adjoint in the native standard presentation. -/
def nisnevichDerivedLeftIso :
    derivedFunctorOfExact a Qs Qp ≅ (a).mapDerivedCategory := by
  let P := PresheafWithTransfers.{u + 1} k
  let L := homotopyLocalization Qp
  let F := (a).mapHomotopyCategory c
  let eP : L ≅ DerivedCategory.Qh (C := P) := homotopyLocalizationQIso
  let G := derivedFunctorOfExact a Qs Qp
  letI : Localization.Lifting (DerivedCategory.Qh (C := P))
      (HomotopyCategory.quasiIso P c) (L ⋙ G) G :=
    ⟨Functor.isoWhiskerRight eP.symm G⟩
  exact Localization.liftNatIso DerivedCategory.Qh (HomotopyCategory.quasiIso P c)
    (L ⋙ derivedFunctorOfExact a Qs Qp) (F ⋙ DerivedCategory.Qh)
    (derivedFunctorOfExact a Qs Qp) (a).mapDerivedCategory
    (derivedFunctorOfExactFac a Qs Qp ≪≫
      Functor.isoWhiskerLeft F homotopyLocalizationQIso)

/-- Exact Nisnevich sheafification is left adjoint to the original total
right-derived inclusion of transfer sheaves. -/
def nisnevichDerivedAdjunction : (a).mapDerivedCategory ⊣ U :=
  (nisnevichDerivedAdjunctionAux k).ofNatIsoLeft (nisnevichDerivedLeftIso k)

instance : (SheafWithTransfers.forgetDerivedFunctor k).Additive :=
  (nisnevichDerivedAdjunction k).right_adjoint_additive

private theorem isIso_nisnevichDerivedAdjunctionAux_counit_app
    (K : DerivedCategory (SheafWithTransfers.{u + 1} k)) :
    IsIso ((nisnevichDerivedAdjunctionAux k).counit.app K) := by
  let A := SheafWithTransfers.{u + 1} k
  let J := (Qs).objPreimage K
  obtain ⟨I, f, hI, hf⟩ :=
    Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A J
  let : QuasiIso f := hf
  let e : (Qs).obj I ≅ K := (asIso ((Qs).map f)).symm ≪≫ (Qs).objObjPreimageIso K
  let adj := nisnevichSheafificationAdjunction k
  let ε := (Adjunction.mapHomologicalComplexAdjunction adj c).counit.app I
  let : ∀ i, IsIso (ε.f i) := fun i => by
    change IsIso (adj.counit.app (I.X i))
    infer_instance
  let : IsIso ε := HomologicalComplex.Hom.isIso_of_components ε
  have h : IsIso ((nisnevichDerivedAdjunctionAux k).counit.app ((Qs).obj I)) :=
    (isIso_adjunctionOfExact_counit_app_iff a Qs Qp adj U
      (SheafWithTransfers.forgetDerivedUnit k) I hI).2 (by infer_instance)
  exact (NatTrans.isIso_app_iff_of_iso _ e).1 h

instance : IsIso (nisnevichDerivedAdjunction k).counit := by
  let : ∀ K, IsIso ((nisnevichDerivedAdjunction k).counit.app K) := fun K => by
    let : IsIso ((nisnevichDerivedAdjunctionAux k).counit.app K) :=
      isIso_nisnevichDerivedAdjunctionAux_counit_app k K
    change IsIso ((nisnevichDerivedLeftIso k).inv.app ((U).obj K) ≫
      (nisnevichDerivedAdjunctionAux k).counit.app K)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.MotivicHomotopy
