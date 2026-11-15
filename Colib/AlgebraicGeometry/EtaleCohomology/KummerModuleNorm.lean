/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerModuleTraceNaturality
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleMultiplicativeTraceNorm

/-! # Norm specialization of the actual Kummer unit corestriction

Here A is an arbitrary finite étale commutative algebra over
a field, not necessarily a field, a domain, or split. Both ΓSpec transports are
retained. The determinant norm comparison is reused, not reproved.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.SplitAffinePullback
universe u
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
  Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal
namespace Stacks.EtaleCohomology
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [Module.Finite k A] [Etale (sourceMap (k := k) (A := A))]
  [IsFinite (sourceMap (k := k) (A := A))]

set_option backward.isDefEq.respectTransparency false in
/-- The existing unit-valued norm comparison, transported back to global sections. -/
theorem kummerTraceUnits_spec_eq_norm (t : Aˣ) :
    finiteEtaleMultiplicativeTraceUnits (sourceMap (k := k) (A := A))
      (Scheme.Etale.mk (𝟙 (Spec (.of k))))
      (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom t) =
    Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom
      (Units.map (Algebra.norm k) t) := by
  have hleft (v : Γ(Spec (.of k), ⊤)ˣ) :
      Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom v) = v := by
    apply Units.ext
    exact congrArg (fun f => f.hom v.val) (Scheme.ΓSpecIso (.of k)).hom_inv_id
  have h := congrArg (Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom)
    (finiteEtaleMultiplicativeTraceUnits_eq_unitsMap_norm t)
  rw [hleft] at h
  exact h

end Stacks.EtaleCohomology
namespace Stacks.Kummer
open Stacks.EtaleCohomology
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [Module.Finite k A] [Etale (sourceMap (k := k) (A := A))]
  [IsFinite (sourceMap (k := k) (A := A))]
  (n : ℕ) [NeZero n] (hX : IsUnit (n : Γ(Spec (.of k), ⊤)))
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})]

set_option backward.isDefEq.respectTransparency false in
/-- The actual unit-source corestriction of the original Kummer class of t is
the original Kummer class of its algebra norm, with canonical ΓSpec transports. -/
theorem kummerModuleNorm_unitClass (t : Aˣ) :
    finiteEtaleZModUnitCorestriction n (sourceMap (k := k) (A := A))
      (rootsOfUnityModule.{u, 0} (Spec (.of k)) n) 1
      ((kummerModuleUnitClass n
        (isUnit_natCast_of_hom (sourceMap (k := k) (A := A)) hX)
        (QuotientAddGroup.mk (Additive.ofMul
          (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom t)))).comp
        (Ext.mk₀ (rootsOfUnityModuleInverseImageIso
          (sourceMap (k := k) (A := A)) n hX).inv) (add_zero 1)) =
    kummerModuleUnitClass n hX (QuotientAddGroup.mk (Additive.ofMul
      (Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom
        (Units.map (Algebra.norm k) t)))) := by
  rw [kummerModuleTraceNaturality_unitClass, kummerTraceUnits_spec_eq_norm]

end Stacks.Kummer
end
