/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Cohomology.Coefficient
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReducedTorusObject
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Contraction
public import Colib.CategoryTheory.Triangulated.Stabilization.Stages
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Contraction against effective Lefschetz powers

The derived reduced torus of an effective single coefficient is its
ordinary contraction. A Lefschetz factor combines the actual reduced
torus tensor adjunction with one cohomological shift.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "NST" => LargeSheaves k
local notation "E" => EffectiveMotivesMinus k
local notation "J" => effectiveMotivesMinusToDerived k
local notation "B" => effectiveReducedTorusSectionsFunctor k
local notation "L" => effectiveLefschetzTwistFunctor k
local notation "K" => effectiveHICoefficient k

/-- Use the native abelian instance for the shift and reduced adjunction. -/
local instance lefschetzCohomologyAbelian : Abelian NST := SheafWithTransfers.abelian k

/-- Derived reduced torus sections of an effective single recover the original contraction. -/
def effectiveReducedTorusSectionsHICoefficientIso (F : NST) (hF : F.obj.IsA1Invariant) :
    (B).obj (K F hF) ≅ K (contraction F hF) (contraction_isA1Invariant F hF) :=
  (Functor.FullyFaithful.ofFullyFaithful (J)).preimageIso
    (((effectiveReducedTorusSectionsToDerivedIso k).app (K F hF)) ≪≫
      reducedTorusSectionsDerivedContractionIso k F hF)

/-- This effective comparison commutes with the actual Laurent contraction maps. -/
@[reassoc]
theorem effectiveReducedTorusSectionsHICoefficientIso_naturality {F G : NST}
    (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant) (f : F ⟶ G) :
    (B).map (effectiveHICoefficientMap k hF hG f) ≫
        (effectiveReducedTorusSectionsHICoefficientIso k G hG).hom =
      (effectiveReducedTorusSectionsHICoefficientIso k F hF).hom ≫
        effectiveHICoefficientMap k (contraction_isA1Invariant F hF)
          (contraction_isA1Invariant G hG) (contractionMap k hF hG f) := by
  let v := Functor.FullyFaithful.ofFullyFaithful (J)
  let e := effectiveReducedTorusSectionsToDerivedIso k
  let D := reducedTorusSectionsDerivedFunctor k
  let S := DerivedCategory.singleFunctor NST 0
  let a := effectiveHICoefficientMap k hF hG f
  have he (P : NST) (hP : P.obj.IsA1Invariant) :
      (J).map (effectiveReducedTorusSectionsHICoefficientIso k P hP).hom =
        (e.app (K P hP)).hom ≫ (reducedTorusSectionsDerivedContractionIso k P hP).hom :=
    v.map_preimage _
  have hn : (J).map ((B).map a) ≫ (e.app (K G hG)).hom =
      (e.app (K F hF)).hom ≫ D.map (S.map f) := e.hom.naturality a
  have hc := reducedTorusSectionsDerivedContractionIso_naturality k hF hG f
  apply (J).map_injective
  rw [(J).map_comp, (J).map_comp, he G hG, he F hF]
  change (J).map ((B).map a) ≫ (e.app (K G hG)).hom ≫
      (reducedTorusSectionsDerivedContractionIso k G hG).hom =
    ((e.app (K F hF)).hom ≫ (reducedTorusSectionsDerivedContractionIso k F hF).hom) ≫
      S.map (contractionMap k hF hG f)
  rw [← Category.assoc ((J).map ((B).map a)), hn, Category.assoc, hc, Category.assoc]

/-- The iterated Laurent contraction with its inherited homotopy invariance. -/
def iteratedHIContraction :
    ℕ → (F : NST) → F.obj.IsA1Invariant → {G : NST // G.obj.IsA1Invariant}
  | 0, F, hF => ⟨F, hF⟩
  | c + 1, F, hF => iteratedHIContraction c (contraction F hF) (contraction_isA1Invariant F hF)

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

private def postcompIso {A C D : E} (e : C ≅ D) : (A ⟶ C) ≃+ (A ⟶ D) :=
  AddEquiv.mk' e.homToEquiv (fun x y => Preadditive.add_comp _ _ _ x y e.hom)

private def lefschetzTwistAdjunction :
    L ⊣ shiftFunctor E (-1 : ℤ) ⋙ (B) :=
  (effectiveReducedTorusTensorAdjunction k).comp ((shiftEquiv E (1 : ℤ)).toAdjunction)

private def lefschetzTwistCoefficientIso (F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ) :
    (B).obj ((K F hF)⟦n⟧⟦(-1 : ℤ)⟧) ≅
      (K (contraction F hF) (contraction_isA1Invariant F hF))⟦n - 1⟧ :=
  (B).mapIso ((shiftFunctorAdd' E n (-1) (n - 1) (by omega)).app (K F hF)).symm ≪≫
    ((B).commShiftIso (n - 1)).app (K F hF) ≪≫
    (shiftFunctor E (n - 1)).mapIso (effectiveReducedTorusSectionsHICoefficientIso k F hF)

/-- Mapping out of one Lefschetz twist contracts the coefficient and lowers the degree by one. -/
@[no_expose]
def effectiveLefschetzTwistCohomologyEquiv (A : E) (F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ) :
    ((L).obj A ⟶ (K F hF)⟦n⟧) ≃+
      (A ⟶ (K (contraction F hF) (contraction_isA1Invariant F hF))⟦n - 1⟧) :=
  let (p : ℤ) : (shiftFunctor E p).Additive := inferInstance
  let : (effectiveReducedTorusTensorFunctor k).Additive := inferInstance
  ((lefschetzTwistAdjunction k).homAddEquiv A ((K F hF)⟦n⟧)).trans
    (postcompIso k (lefschetzTwistCoefficientIso k F hF n))

/-- The single Lefschetz comparison respects precomposition by the original source map. -/
theorem effectiveLefschetzTwistCohomologyEquiv_precomp {A A' : E} (a : A ⟶ A')
    (F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ)
    (x : (L).obj A' ⟶ (K F hF)⟦n⟧) :
    effectiveLefschetzTwistCohomologyEquiv k A F hF n ((L).map a ≫ x) =
      a ≫ effectiveLefschetzTwistCohomologyEquiv k A' F hF n x := by
  let adj := lefschetzTwistAdjunction k
  let b := (lefschetzTwistCoefficientIso k F hF n).hom
  change adj.homEquiv A ((K F hF)⟦n⟧) ((L).map a ≫ x) ≫ b =
    a ≫ adj.homEquiv A' ((K F hF)⟦n⟧) x ≫ b
  rw [adj.homEquiv_naturality_left, Category.assoc]

private def contractionDegreeZeroIso (F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ) :
    (K F hF)⟦n⟧ ≅ (K F hF)⟦n - ((0 : ℕ) : ℤ)⟧ :=
  eqToIso (congrArg (fun p : ℤ => (K F hF)⟦p⟧) (by simp))

private def contractionDegreeSuccIso (F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ) (c : ℕ) :
    (K F hF)⟦n - 1 - c⟧ ≅ (K F hF)⟦n - ((c + 1 : ℕ) : ℤ)⟧ :=
  eqToIso (congrArg (fun p : ℤ => (K F hF)⟦p⟧) (by omega))

/-- Mapping out of a Lefschetz power gives the iterated contraction in the difference degree. -/
@[no_expose]
def effectiveLefschetzPowerCohomologyEquiv (A : E) :
    (c : ℕ) → (F : NST) → (hF : F.obj.IsA1Invariant) → (n : ℤ) →
    ((Stabilization.iterate L c).obj A ⟶ (K F hF)⟦n⟧) ≃+
      (A ⟶ (K (iteratedHIContraction k c F hF).1
        (iteratedHIContraction k c F hF).2)⟦n - c⟧)
  | 0, F, hF, n => postcompIso k (contractionDegreeZeroIso k F hF n)
  | c + 1, F, hF, n =>
    let G := contraction F hF
    let hG := contraction_isA1Invariant F hF
    let H := iteratedHIContraction k c G hG
    (effectiveLefschetzTwistCohomologyEquiv k ((Stabilization.iterate L c).obj A) F hF n).trans
      ((effectiveLefschetzPowerCohomologyEquiv A c G hG (n - 1)).trans
        (postcompIso k (contractionDegreeSuccIso k H.1 H.2 n c)))

set_option maxHeartbeats 500000 in
-- The recursive degree comparison reduces the selected iterated coefficient and shift.
/-- The iterated Lefschetz comparison is natural in the original source. -/
theorem effectiveLefschetzPowerCohomologyEquiv_precomp {A A' : E} (a : A ⟶ A')
    (c : ℕ) (F : NST) (hF : F.obj.IsA1Invariant) (n : ℤ)
    (x : (Stabilization.iterate L c).obj A' ⟶ (K F hF)⟦n⟧) :
    effectiveLefschetzPowerCohomologyEquiv k A c F hF n ((Stabilization.iterate L c).map a ≫ x) =
      a ≫ effectiveLefschetzPowerCohomologyEquiv k A' c F hF n x := by
  induction c generalizing F n with
  | zero =>
    change (a ≫ x) ≫ (contractionDegreeZeroIso k F hF n).hom =
      a ≫ x ≫ (contractionDegreeZeroIso k F hF n).hom
    exact Category.assoc _ _ _
  | succ c ih =>
    let T := Stabilization.iterate L c
    let G := contraction F hF
    let hG := contraction_isA1Invariant F hF
    let C := iteratedHIContraction k c G hG
    let s := (contractionDegreeSuccIso k C.1 C.2 n c).hom
    let x' : (L).obj (T.obj A') ⟶ (K F hF)⟦n⟧ := x
    change effectiveLefschetzPowerCohomologyEquiv k A c G hG (n - 1)
        (effectiveLefschetzTwistCohomologyEquiv k (T.obj A) F hF n ((L).map (T.map a) ≫ x')) ≫ s =
      a ≫ effectiveLefschetzPowerCohomologyEquiv k A' c G hG (n - 1)
        (effectiveLefschetzTwistCohomologyEquiv k (T.obj A') F hF n x') ≫ s
    have hw := effectiveLefschetzTwistCohomologyEquiv_precomp k (T.map a) F hF n x'
    rw [hw, ih, Category.assoc]

end AlgebraicGeometry.MotivicHomotopy
