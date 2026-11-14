/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneKummerCompatibility
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.MilnorDiagonal
public import Colib.AlgebraicGeometry.EtaleCohomology.MilnorKummerOne

/-! # The original finite Milnor diagonal comparison agrees with the native Kummer symbol -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType CochainComplex.finiteCoefficients
open Stacks.Cohomology.FreeYonedaUnivLE Stacks.Cohomology.Corepresented
universe u wN wE wS
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable [HasDerivedCategory.{wN}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{wE}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [hSmall : HasDerivedCategory.{wS}
  (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]

@[reducible] local instance : HasDerivedCategory.{wS}
    (Sheaf (base (Spec (.of k))).left.smallEtaleTopology AddCommGrpCat.{u + 1}) := hSmall

local instance : HasExt.{u + 1}
    (Sheaf (base (Spec (.of k))).left.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstanceAs (HasExt.{u + 1}
    (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}))

set_option maxRecDepth 4096 in
-- The native Milnor quotient transport crosses the actual coefficient-forgetting Ext equivalence.
/-- The original motivic comparison and original module Kummer symbol agree in degree one. -/
lemma weightOneFiniteEtaleCohomologyMap_motivicFiniteEquiv
    (n : ℕ) [NeZero n] (hunit : IsUnit (n : Γ(Spec (.of k), ⊤)))
    (a : FiniteMilnorDiagonal.milnorModulo k 1 n) :
    weightOneFiniteEtaleCohomologyMap k (base (Spec (.of k))) 1 n (NeZero.ne n) hunit
      (FiniteMilnorDiagonal.motivicFiniteEquiv k 1 n a) =
    Stacks.Kummer.rootsOfUnityModuleExtEquiv (Spec (.of k)) n 1
      (EtaleCohomology.MilnorKummer.milnorOneKummerModuleClass k n hunit a) := by
  refine Quotient.inductionOn a ?_
  intro x
  rw [FiniteMilnorDiagonal.motivicFiniteEquiv_one_mk]
  have hn : motivicNorm k (milnorEquiv k x) = milnorKTheoryOneAddEquiv k x := by
    change weightOneEquiv k ((weightOneEquiv k).symm (milnorKTheoryOneAddEquiv k x)) = _
    exact AddEquiv.apply_symm_apply _ _
  have hu : Additive.ofMul (specGlobalUnit (motivicNorm k (milnorEquiv k x)).toMul) =
      EtaleCohomology.MilnorKummer.milnorOneGlobalUnitsEquiv k x := by
    rw [hn]
    rfl
  have h := weightOneFiniteEtaleCohomologyMap_integral_norm k n (NeZero.ne n) hunit
    (milnorEquiv k x)
  have hc := congrArg (Stacks.Kummer.unitKummerClass.{u + 1, u, 0}
    (Spec (.of k)) (NeZero.ne n) hunit) hu
  exact h.trans (hc.trans
    (EtaleCohomology.MilnorKummer.milnorOneKummerModuleClass_mk k n hunit x).symm)

end AlgebraicGeometry.MotivicCohomology.WeightOne
