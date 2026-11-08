/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductNormalizedEndpoint

/-! Whole supplied Theta/null data, both original cancellations and moving endpoint transports. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory.Waldhausen.Product SSet
open CategoryTheory CategoryTheory.Limits Topology CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Additivity CategoryTheory.Waldhausen.Fibration
open CompactCoproductEndpoint
open scoped Topology
universe u v
namespace ColibTest.CompactCoproductNormalizedEndpoint
variable {C : Type u} [Category.{v} C] (W : Structure C)
  (NW : NestedWeakEquivalences W) [HasBinaryCoproducts C] (n : ℕ)
local notation "GE" => GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint
local notation "F" => coproductChangeWeakCubeMap W NW n
variable {a q c d0 d : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}

/-- The original initial path and whole first Theta cylinder precede the actual unitor. -/
theorem original_gamma (A0 : Path a d0)
    (T0 : Path d0 (coproductCube W n GenLoop.const q)) :
    gamma W n A0 T0 = A0.trans (T0.trans (coproductLeftUnitPath W n q)) := rfl

/-- The fine return retains the complete gamma and the actual fine cancellation. -/
theorem original_fine_return (A0 : Path a d0)
    (T0 : Path d0 (coproductCube W n GenLoop.const q)) :
    nu W n A0 T0 =
      ((gamma W n A0 T0).symm.map (GenLoopPrefix.inversePrefix n a).continuous).trans
        (GenLoopPrefix.cancellation n a) := rfl

/-- The whole fine delta uses the supplied second Theta and original inverse-associator tail. -/
theorem original_delta (A0 : Path a d0)
    (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (T1 : Path d (coproductCube W n c q)) :
    delta W n A0 T0 T1 =
      (((T1.trans (coproductSeparationPath n W c q)).map
        (GenLoopPrefix.inversePrefix n a).continuous).trans
          (GenLoopPrefix.tail n (GenLoop.symmAt 0 a) q c (nu W n A0 T0))) := rfl

omit [HasBinaryCoproducts C] in
/-- The coarse null retains its complete reversed word, cancellation and forward source cast. -/
theorem original_normalized_source_cast (A0 : Path a d0) (Z : Path (F d0) (F d)) :
    normalizedNull W NW n A0 Z =
      (((Z.symm.trans (A0.map (F).continuous).symm).map
        (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
          (GenLoopPrefix.cancellation n (F a))).cast (prefix_source W NW n a d) rfl := rfl

/-- Both actual moving-source transports are displayed in whole fine-delta naturality. -/
theorem original_whole_delta_naturality (A0 : Path a d0)
    (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (T1 : Path d (coproductCube W n c q)) :
    ((delta W n A0 T0 T1).map (F).continuous).cast
      (prefix_source W NW n a d).symm rfl = coarseDelta W NW n A0 T0 T1 :=
  delta_map W NW n A0 T0 T1

variable (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q))
  (T1 : Path d (coproductCube W n c q))
  (N : Path (coproductChangeWeakCubeMap W NW n c) GenLoop.const)
  (Z : Path (coproductChangeWeakCubeMap W NW n d0) (coproductChangeWeakCubeMap W NW n d))
  (Jtheta : Z.symm.Homotopy ((thetaOne W NW n T1).trans
    ((coproductCubePath NW.coarse n N
      (Path.refl (coproductChangeWeakCubeMap W NW n q))).trans
        (thetaZero W NW n T0).symm)))

/-- The whole data-valued result consumes the exact supplied geometric comparison. -/
def original_whole_endpoint :
    (normalizedNull W NW n A0 Z).Homotopy ((delta W n A0 T0 T1).map (F).continuous |>.trans N) :=
  normalizedNullHomotopy W NW n A0 T0 T1 N Z Jtheta

/-- The final homotopy time retains the entire original null path and exact parentheses. -/
theorem original_entire_null (t : unitInterval) :
    normalizedNullHomotopy W NW n A0 T0 T1 N Z Jtheta (1, t) =
      ((delta W n A0 T0 T1).map (F).continuous |>.trans N) t :=
  (normalizedNullHomotopy W NW n A0 T0 T1 N Z Jtheta).apply_one t

/-- Every homotopy/path time pair retains the complete original spatial boundary. -/
theorem original_whole_boundary (s t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    normalizedNullHomotopy W NW n A0 T0 T1 N Z Jtheta (s, t) z = NW.coarse.kBasepoint :=
  normalizedNullHomotopy_boundary W NW n A0 T0 T1 N Z Jtheta s t z hz

/-- A one-coordinate input retains both cancellations and the entire supplied Theta/null data. -/
def original_degree_zero
    {a₀ q₀ c₀ d₀ d₁ : GenLoop (Fin 1) W.Delooping W.kBasepoint}
    (A : Path a₀ d₀) (T₀ : Path d₀ (coproductCube W 0 GenLoop.const q₀))
    (T₁ : Path d₁ (coproductCube W 0 c₀ q₀))
    (P : Path (coproductChangeWeakCubeMap W NW 0 c₀) GenLoop.const)
    (Q : Path (coproductChangeWeakCubeMap W NW 0 d₀)
      (coproductChangeWeakCubeMap W NW 0 d₁))
    (J : Q.symm.Homotopy ((thetaOne W NW 0 T₁).trans
      ((coproductCubePath NW.coarse 0 P
        (Path.refl (coproductChangeWeakCubeMap W NW 0 q₀))).trans
          (thetaZero W NW 0 T₀).symm))) :
    (normalizedNull W NW 0 A Q).Homotopy
      ((delta W 0 A T₀ T₁).map (coproductChangeWeakCubeMap W NW 0).continuous |>.trans P) :=
  normalizedNullHomotopy W NW 0 A T₀ T₁ P Q J

end ColibTest.CompactCoproductNormalizedEndpoint
