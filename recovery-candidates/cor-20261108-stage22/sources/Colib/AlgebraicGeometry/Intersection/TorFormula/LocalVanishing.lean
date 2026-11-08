module

public import Mathlib.Order.Interval.Finset.Nat
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafMultiplicity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafVanishing

/-!
# Local eventual vanishing of Tor sheaf multiplicities

At a fixed point with regular local ring, the stalk lengths of the actual Tor sheaves vanish
above a natural-number bound. Their support as a function of the homological degree is finite,
as is the support of the integer multiplicities and their alternating signs.

The bound is the Krull dimension of this one local ring. No coherence assumption on the two
modules, global regularity, or finite bound on the dimension of the scheme is required. This
asserts eventual zero length; it does not assert finite length for the remaining low degrees.

The native Stacks 0AZT stalk comparison identifies the actual Tor sheaf stalk length with the
Tor length over the ambient scheme stalk. The regular-local-ring vanishing theorem then applies
there, with no change to a surrogate module or an assumed comparison map.

Recovery status: newly reconstructed on 2026-11-08 from the pinned native sources. This file has
not been compiled or otherwise validated in the current recovery. It is not an exact-byte
recovery of the historical file, and no historical successful check is inherited.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TorFormula

/-- The local Krull dimension at a regular point is a natural number. The case analysis follows
the corresponding step in the native `isZero_Tor_of_isRegularLocalRing` proof. -/
private theorem exists_nat_stalk_ringKrullDim_eq (X : Scheme.{u}) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] :
    ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) := by
  have htop : ringKrullDim (X.presheaf.stalk x) ≠ ⊤ := ringKrullDim_ne_top
  cases hx : ringKrullDim (X.presheaf.stalk x) with
  | bot => exact (ringKrullDim_ne_bot hx).elim
  | coe y =>
    cases y with
    | top => exact (htop (by simpa using hx)).elim
    | coe n => exact ⟨n, by simp⟩

/-- The length of the actual Tor sheaf stalk vanishes above a bound for the dimension of the
regular ambient local ring. -/
theorem length_stalk_torSheaf_eq_zero_of_lt (X : Scheme.{u}) (F G : X.Modules) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] (d p : ℕ)
    (hdim : ringKrullDim (X.presheaf.stalk x) ≤ (d : WithBot ℕ∞)) (hdp : d < p) :
    Module.length (X.presheaf.stalk x) ((torSheaf X F G p).presheaf.stalk x) = 0 := by
  rw [length_stalk_torSheaf_eq_length_tor_stalk]
  exact Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
    (isZero_Tor_of_isRegularLocalRing
      (stalkModuleCat X F x) (stalkModuleCat X G x) d p hdim hdp))

/-- The integer multiplicity of the actual Tor sheaf at a regular point vanishes above a bound
for the dimension of that point's ambient local ring. -/
theorem sheafMultiplicity_torSheaf_eq_zero_of_lt (X : Scheme.{u}) (F G : X.Modules) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] (d p : ℕ)
    (hdim : ringKrullDim (X.presheaf.stalk x) ≤ (d : WithBot ℕ∞)) (hdp : d < p) :
    Stacks.Chow.sheafMultiplicity (torSheaf X F G p) x = 0 := by
  simp [Stacks.Chow.sheafMultiplicity,
    length_stalk_torSheaf_eq_zero_of_lt X F G x d p hdim hdp]

/-- A fixed regular point admits a single degree bound, independent of the two modules, above
which all Tor sheaf stalk lengths vanish. -/
theorem exists_bound_length_stalk_torSheaf_eq_zero (X : Scheme.{u}) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] :
    ∃ d : ℕ, ∀ (F G : X.Modules) (p : ℕ), d < p →
      Module.length (X.presheaf.stalk x) ((torSheaf X F G p).presheaf.stalk x) = 0 := by
  obtain ⟨d, hd⟩ := exists_nat_stalk_ringKrullDim_eq X x
  exact ⟨d, fun F G p hp ↦ length_stalk_torSheaf_eq_zero_of_lt X F G x d p hd.le hp⟩

/-- The corresponding degree bound for the integer multiplicities is local at the point and
uniform in the two modules. -/
theorem exists_bound_sheafMultiplicity_torSheaf_eq_zero (X : Scheme.{u}) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] :
    ∃ d : ℕ, ∀ (F G : X.Modules) (p : ℕ), d < p →
      Stacks.Chow.sheafMultiplicity (torSheaf X F G p) x = 0 := by
  obtain ⟨d, hd⟩ := exists_nat_stalk_ringKrullDim_eq X x
  exact ⟨d, fun F G p hp ↦ sheafMultiplicity_torSheaf_eq_zero_of_lt X F G x d p hd.le hp⟩

private theorem finite_support_of_eq_zero_above {A : Type*} [Zero A]
    (f : ℕ → A) (d : ℕ) (h : ∀ p : ℕ, d < p → f p = 0) :
    (Function.support f).Finite := by
  refine (Set.finite_Iic d).subset ?_
  intro p hp
  change p ≤ d
  exact le_of_not_gt fun hdp ↦ hp (h p hdp)

/-- At a fixed regular point, only finitely many homological degrees have nonzero Tor sheaf
stalk length. This is finite support in the degree variable, not finite support on the scheme.
-/
theorem finite_support_length_stalk_torSheaf (X : Scheme.{u}) (F G : X.Modules) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] :
    (Function.support fun p : ℕ ↦
      Module.length (X.presheaf.stalk x) ((torSheaf X F G p).presheaf.stalk x)).Finite := by
  obtain ⟨d, hd⟩ := exists_bound_length_stalk_torSheaf_eq_zero X x
  exact finite_support_of_eq_zero_above _ d (hd F G)

/-- The integer multiplicities of the actual Tor sheaves at a regular point have finite support
in their homological degree. -/
theorem finite_support_sheafMultiplicity_torSheaf (X : Scheme.{u}) (F G : X.Modules) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] :
    (Function.support fun p : ℕ ↦
      Stacks.Chow.sheafMultiplicity (torSheaf X F G p) x).Finite := by
  obtain ⟨d, hd⟩ := exists_bound_sheafMultiplicity_torSheaf_eq_zero X x
  exact finite_support_of_eq_zero_above _ d (hd F G)

/-- The alternating Tor sheaf multiplicities at a regular point have finite support, so the
local alternating multiplicity uses only finitely many homological degrees. -/
theorem finite_support_signed_sheafMultiplicity_torSheaf
    (X : Scheme.{u}) (F G : X.Modules) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] :
    (Function.support fun p : ℕ ↦
      (-1 : ℤ) ^ p * Stacks.Chow.sheafMultiplicity (torSheaf X F G p) x).Finite := by
  refine (finite_support_sheafMultiplicity_torSheaf X F G x).subset ?_
  intro p hp hzero
  apply hp
  rw [hzero, mul_zero]

end AlgebraicGeometry.TorFormula

end
