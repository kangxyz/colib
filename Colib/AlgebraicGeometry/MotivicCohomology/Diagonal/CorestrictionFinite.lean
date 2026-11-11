/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.Corestriction
public import Colib.AlgebraicGeometry.MotivicCohomology.FieldTopDegree

/-!
# Finite coefficients for diagonal corestriction

Integral corestriction descends through the original top-degree reduction,
using its comparison with the quotient by coefficient multiples. The
construction works over every finite field extension and at every natural
coefficient level.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers FieldTopDegree

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The actual integral transfer on the quotient by coefficient multiples. -/
def integralModuloCorestriction (q n : ℕ) :
    integralModulo E q n →+ integralModulo k q n :=
  QuotientAddGroup.map (integralMultiples E q n) (integralMultiples k q n)
    (integralCorestriction (k := k) (E := E) q) (by
      intro x hx
      obtain ⟨y, rfl⟩ := (mem_integralMultiples E q n x).mp hx
      change integralCorestriction (k := k) q (n • y) ∈ integralMultiples k q n
      exact (mem_integralMultiples k q n _).mpr
        ⟨integralCorestriction (k := k) q y,
          (map_nsmul (integralCorestriction (k := k) (E := E) q) n y).symm⟩)

private theorem integralModuloCorestriction_mk (q n : ℕ)
    (x : motivicCohomology E q q (SmoothSite.base (Spec (.of E)))) :
    integralModuloCorestriction (k := k) q n (QuotientAddGroup.mk x) =
      (QuotientAddGroup.mk (integralCorestriction (k := k) q x) : integralModulo k q n) :=
  rfl

/-- The original diagonal corestriction with finite coefficients. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/CorestrictionFinite.lean:45-70"
  "adaptation" "Corestriction through the actual top-degree finite coefficient quotient"]
def finiteCorestriction (q n : ℕ) :
    motivicFiniteCohomology E q q n (SmoothSite.base (Spec (.of E))) →+
      motivicFiniteCohomology k q q n (SmoothSite.base (Spec (.of k))) :=
  (topDegreeFiniteEquiv k q n).symm.toAddMonoidHom.comp
    ((integralModuloCorestriction (k := k) (E := E) q n).comp
      (topDegreeFiniteEquiv E q n).toAddMonoidHom)

/-- The actual integral coefficient reduction intertwines the two corestrictions. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/WeightTwo/CorestrictionFinite.lean:72-85"
  "adaptation" "The literal integral reduction square with finite coefficients"]
theorem finiteCorestriction_integralReduction (q n : ℕ)
    (x : motivicCohomology E q q (SmoothSite.base (Spec (.of E)))) :
    finiteCorestriction (k := k) q n (motivicBaseIntegralReduction E q q n x) =
      motivicBaseIntegralReduction k q q n (integralCorestriction (k := k) q x) := by
  have hin := topDegreeFiniteEquiv_integralReduction E q n x
  have hmk := integralModuloCorestriction_mk (k := k) q n x
  have hout := topDegreeFiniteEquiv_symm_mk k q n (integralCorestriction (k := k) q x)
  simp only [finiteCorestriction, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    hin, hmk, hout]

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction
