/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.OrderedMilnorKummer
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorEquivalence

/-!
# A generator criterion for the ordinary diagonal Kummer comparison

A homomorphism out of the actual integral motivic diagonal agrees with the ordinary
Milnor Kummer symbol precisely when it has the ordered Kummer values on the original
rational graph classes. Such a comparison is unique. In positive degrees the same
criterion proves annihilation by n and hence descent through n multiples.

These are criteria for an independently constructed realization, not a construction
of the etale realization or its comparison with the motivic Tate complex.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
universe w u

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules

namespace AlgebraicGeometry.EtaleCohomology.MilnorKummer

open _root_.AlgebraicGeometry.Scheme
open MotivicCohomology PresheafWithTransfers
open MotivicCohomology.DiagonalMilnorSymbol
open MotivicCohomology.DiagonalMilnorEquivalence
open MotivicCohomology.DiagonalCycleSymbols

variable (k : Type u) [Field k] (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Checking the original rational graphs suffices for the entire diagonal comparison. -/
@[colib_tag "COL-1300"]
theorem diagonalKummerComparison_iff (q : ℕ)
    (r : motivicCohomology k q q (SmoothSite.base (Spec (.of k))) →+
      Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n q) :
    r.comp (motivicSymbol k q) = (milnorKummerSymbol k n q).toAddMonoidHom ↔
      ∀ a : Fin q → kˣ,
        r ((motivicRawBaseEvaluationComparison k q q).symm (graphSymbol k q a)) =
          orderedFieldKummerCup k n q a := by
  constructor
  · intro h a
    have ha := DFunLike.congr_fun h (milnorKTupleSymbol a)
    simpa only [AddMonoidHom.comp_apply, motivicSymbol_symbol,
      LinearMap.toAddMonoidHom_coe, milnorKummerSymbol_tuple] using ha
  · intro h
    apply milnorKTheory_addHom_ext
    intro a
    change r (motivicSymbol k q (milnorKTupleSymbol a)) =
      milnorKummerSymbol k n q (milnorKTupleSymbol a)
    rw [motivicSymbol_symbol, milnorKummerSymbol_tuple]
    exact h a

/-- The graph comparison determines an actual realization on the entire integral diagonal. -/
theorem diagonalKummerComparison_unique (q : ℕ)
    (r s : motivicCohomology k q q (SmoothSite.base (Spec (.of k))) →+
      Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n q)
    (hr : r.comp (motivicSymbol k q) = (milnorKummerSymbol k n q).toAddMonoidHom)
    (hs : s.comp (motivicSymbol k q) = (milnorKummerSymbol k n q).toAddMonoidHom) :
    r = s := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (motivicEquiv k q).surjective x
  exact DFunLike.congr_fun (hr.trans hs.symm) y

/-- Any actual positive-degree diagonal comparison is annihilated by n. -/
theorem diagonalKummerComparison_nsmul (q : ℕ)
    (r : motivicCohomology k (q + 1) (q + 1) (SmoothSite.base (Spec (.of k))) →+
      Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n (q + 1))
    (hr : r.comp (motivicSymbol k (q + 1)) =
      (milnorKummerSymbol k n (q + 1)).toAddMonoidHom)
    (x : motivicCohomology k (q + 1) (q + 1) (SmoothSite.base (Spec (.of k)))) :
    n • r x = 0 := by
  obtain ⟨y, rfl⟩ := (motivicEquiv k (q + 1)).surjective x
  change n • r (motivicSymbol k (q + 1) y) = 0
  rw [show r (motivicSymbol k (q + 1) y) = milnorKummerSymbol k n (q + 1) y from
    DFunLike.congr_fun hr y]
  exact nsmul_milnorKummerSymbol k n q y

/-- An independently constructed positive diagonal comparison descends through n multiples. -/
def diagonalModuloKummerComparison (q : ℕ)
    (r : motivicCohomology k (q + 1) (q + 1) (SmoothSite.base (Spec (.of k))) →+
      Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n (q + 1))
    (hr : r.comp (motivicSymbol k (q + 1)) =
      (milnorKummerSymbol k n (q + 1)).toAddMonoidHom) :
    (motivicCohomology k (q + 1) (q + 1) (SmoothSite.base (Spec (.of k))) ⧸
      (n • AddMonoidHom.id _).range) →+
      Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n (q + 1) :=
  QuotientAddGroup.lift _ r (by
    rintro x ⟨y, rfl⟩
    change r (n • y) = 0
    rw [map_nsmul]
    exact diagonalKummerComparison_nsmul k n q r hr y)

/-- Descent retains the original graph values, not a newly chosen symbol convention. -/
theorem diagonalModuloKummerComparison_symbol (q : ℕ)
    (r : motivicCohomology k (q + 1) (q + 1) (SmoothSite.base (Spec (.of k))) →+
      Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n (q + 1))
    (hr : r.comp (motivicSymbol k (q + 1)) =
      (milnorKummerSymbol k n (q + 1)).toAddMonoidHom)
    (a : Fin (q + 1) → kˣ) :
    diagonalModuloKummerComparison k n q r hr
        (QuotientAddGroup.mk (motivicSymbol k (q + 1) (milnorKTupleSymbol a))) =
      orderedFieldKummerCup k n (q + 1) a := by
  change r (motivicSymbol k (q + 1) (milnorKTupleSymbol a)) = _
  exact (DFunLike.congr_fun hr (milnorKTupleSymbol a)).trans
    (milnorKummerSymbol_tuple k n (q + 1) a)

end AlgebraicGeometry.EtaleCohomology.MilnorKummer
end
