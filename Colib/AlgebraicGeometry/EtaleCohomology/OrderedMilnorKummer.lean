/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.OrderedKummerSteinberg
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Descent

/-!
# Native Milnor descent of the ordinary ordered Kummer cup

The actual multilinear Kummer tuple map satisfies every adjacent Steinberg
relation. Its existing native Milnor universal property gives the symbol map.
In positive degrees it factors through the quotient by n multiples. This
constructs the map, not a norm-residue isomorphism or a motivic Tate comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MonoidalCategory
universe u
set_option maxRecDepth 4096
attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules
namespace AlgebraicGeometry.EtaleCohomology.MilnorKummer
variable (k : Type u) [Field k] (n : ℕ) [NeZero n] [NeZero (n : k)]
  [HasExt.{u + 1} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The original ordered field Kummer cup satisfies the native Milnor symbol conditions. -/
theorem orderedFieldKummerCup_isSymbolMap (q : ℕ) :
    IsMilnorKSymbolMap (orderedFieldKummerCup k n q) :=
  ⟨orderedFieldKummerCup_update_mul k n q, orderedFieldKummerCup_steinberg k n q⟩

/-- The actual ordered Kummer cup descends to the native homogeneous Milnor group. -/
@[colib_tag "COL-1300"]
def milnorKummerSymbol (q : ℕ) : MilnorKTheory k q →ₗ[ℤ]
    Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n q :=
  (orderedFieldKummerCup_isSymbolMap k n q).lift

/-- The descended map retains the original ordered tuple values. -/
theorem milnorKummerSymbol_tuple (q : ℕ) (a : Fin q → kˣ) :
    milnorKummerSymbol k n q (milnorKTupleSymbol a) = orderedFieldKummerCup k n q a :=
  (orderedFieldKummerCup_isSymbolMap k n q).lift_symbol a

/-- Every positive-degree value of the actual Milnor symbol is killed by n. -/
theorem nsmul_milnorKummerSymbol (q : ℕ) (x : MilnorKTheory k (q + 1)) :
    n • milnorKummerSymbol k n (q + 1) x = 0 := by
  have h : n • (milnorKummerSymbol k n (q + 1)).toAddMonoidHom = 0 := by
    apply milnorKTheory_addHom_ext
    intro a
    change n • milnorKummerSymbol k n (q + 1) (milnorKTupleSymbol a) = 0
    rw [milnorKummerSymbol_tuple]
    exact Stacks.Kummer.nsmul_orderedKummerCup _ _ _ _ _
  exact DFunLike.congr_fun h x

/-- The positive-degree ordinary Kummer symbol on the native quotient by n multiples. -/
@[colib_tag "COL-1300"]
def milnorModuloKummerSymbol (q : ℕ) :
    (MilnorKTheory k (q + 1) ⧸ (n • AddMonoidHom.id (MilnorKTheory k (q + 1))).range) →+
      Stacks.Kummer.rootsOfUnityPowerTarget (X := Spec (.of k)) n (q + 1) :=
  QuotientAddGroup.lift _ (milnorKummerSymbol k n (q + 1)).toAddMonoidHom (by
    rintro x ⟨y, rfl⟩
    change milnorKummerSymbol k n (q + 1) (n • y) = 0
    rw [map_nsmul, nsmul_milnorKummerSymbol])

/-- Reduction modulo n preserves the actual ordinary ordered cup of the field units. -/
theorem milnorModuloKummerSymbol_tuple (q : ℕ) (a : Fin (q + 1) → kˣ) :
    milnorModuloKummerSymbol k n q (QuotientAddGroup.mk (milnorKTupleSymbol a)) =
      orderedFieldKummerCup k n (q + 1) a :=
  milnorKummerSymbol_tuple k n (q + 1) a

end AlgebraicGeometry.EtaleCohomology.MilnorKummer
end
