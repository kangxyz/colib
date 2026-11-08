/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductNullCoherence
public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductSeparationNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopPrefixNullCoherence
public import Colib.Topology.Path.Homotopy.ThetaWord

public import Colib.Util.References

/-! # The actual normalized compact endpoint from a supplied whole Theta square

All geometric paths and the entire Theta comparison are explicit inputs. The result retains
both original inverse-prefix cancellations and the complete supplied null path, including
one-coordinate inputs. No geometric square is selected by this construction.
-/
/-! Adapted from `Quillen/Waldhausen/Additivity/CompactCoproductNormalizedEndpoint.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original universes, canonical maps,
coordinates and boundaries are retained. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology SSet
open CategoryTheory.Waldhausen.Product
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u v w
namespace CategoryTheory.Waldhausen.Additivity.CompactCoproductEndpoint
open Fibration

variable {C : Type u} [Category.{v} C] (W : Structure C)
  (NW : NestedWeakEquivalences W) [HasBinaryCoproducts C] (n : ℕ)
local notation "GE" => GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint
local notation "GB" => GenLoop (Fin (n + 1)) NW.coarse.Delooping NW.coarse.kBasepoint
local notation "F" => coproductChangeWeakCubeMap W NW n
variable {a q c d0 d : GenLoop (Fin (n + 1)) W.Delooping W.kBasepoint}

/-- The actual zero-left endpoint comparison includes the original constant-cube transport. -/
theorem zeroLeft_map (q : GE) :
    F (coproductCube W n GenLoop.const q) =
      coproductCube NW.coarse n GenLoop.const (F q) := by
  rw [coproductCube_changeWeak, coproductChangeWeakCubeMap_const]

/-- The original first Theta path with its exact target transport. -/
def thetaZero (T0 : Path d0 (coproductCube W n GenLoop.const q)) :
    Path (F d0) (coproductCube NW.coarse n GenLoop.const (F q)) :=
  (T0.map (F).continuous).cast rfl (zeroLeft_map W NW n q).symm

/-- The original second Theta path with its exact compact-coproduct target transport. -/
def thetaOne (T1 : Path d (coproductCube W n c q)) :
    Path (F d) (coproductCube NW.coarse n (F c) (F q)) :=
  (T1.map (F).continuous).cast rfl (coproductCube_changeWeak W NW n c q).symm

/-- The initial path, original first Theta cylinder and actual zero-left unitor all remain. -/
def gamma (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q)) :
    Path a q := A0.trans (T0.trans (coproductLeftUnitPath W n q))

/-- The original fine inverse-prefix return includes the complete initial path and cancellation. -/
def nu (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q)) :
    Path (GenLoopPrefix.inversePrefix n a q) GenLoop.const :=
  ((gamma W n A0 T0).symm.map (GenLoopPrefix.inversePrefix n a).continuous).trans
    (GenLoopPrefix.cancellation n a)

/-- The second Theta cylinder followed by the original q-first compact separation. -/
def separation (T1 : Path d (coproductCube W n c q)) :
    Path d (GenLoop.transAt 0 q c) := T1.trans (coproductSeparationPath n W c q)

/-- The actual fine path retains the inverse associator, whole return and original unit removal. -/
def delta (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (T1 : Path d (coproductCube W n c q)) :
    Path (GenLoopPrefix.inversePrefix n a d) c :=
  ((separation W n T1).map (GenLoopPrefix.inversePrefix n a).continuous).trans
    (GenLoopPrefix.tail n (GenLoop.symmAt 0 a) q c (nu W n A0 T0))

omit [HasBinaryCoproducts C] in
/-- Both reversed original edges end at the moving image of the initial cube. -/
def terminal (A0 : Path a d0) (Z : Path (F d0) (F d)) : Path (F d) (F a) :=
  Z.symm.trans (A0.map (F).continuous).symm

omit [HasBinaryCoproducts C] in
/-- The exact source comparison for the two original inverse-prefix maps. -/
theorem prefix_source (a d : GE) :
    F (GenLoopPrefix.inversePrefix n a d) = GenLoopPrefix.inversePrefix n (F a) (F d) :=
  GenLoopPrefix.inversePrefix_map n (changeWeakMap NW) (changeWeakMap_basepoint NW) a d

omit [HasBinaryCoproducts C] in
/-- The whole reversed terminal path keeps its coarse cancellation and explicit source cast. -/
def normalizedNull (A0 : Path a d0) (Z : Path (F d0) (F d)) :
    Path (F (GenLoopPrefix.inversePrefix n a d)) GenLoop.const :=
  (((terminal W NW n A0 Z).map (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
    (GenLoopPrefix.cancellation n (F a))).cast (prefix_source W NW n a d) rfl

/-- The original fine gamma is exactly its whole mapped Theta/unitor word. -/
theorem gamma_map (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q)) :
    (gamma W n A0 T0).map (F).continuous =
      (A0.map (F).continuous).trans
        ((thetaZero W NW n T0).trans (coproductLeftUnitPath NW.coarse n (F q))) := by
  apply Path.ext
  funext t
  unfold gamma
  rw [Path.map_trans]
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · rfl
  · rw [Path.map_trans, Path.trans_apply, Path.trans_apply]
    split_ifs
    · rfl
    · exact coproductLeftUnitCubeMap_changeWeak W NW n q _

/-- Both compact separation endpoint casts are retained by the whole mapped path. -/
theorem separation_map (T1 : Path d (coproductCube W n c q)) :
    ((separation W n T1).map (F).continuous).cast rfl
      (coproductChangeWeakCubeMap_transAt W NW n q c).symm =
        (thetaOne W NW n T1).trans (coproductSeparationPath n NW.coarse (F c) (F q)) := by
  apply Path.ext
  funext t
  change F ((T1.trans (coproductSeparationPath n W c q)) t) = _
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · rfl
  · exact coproductSeparationPath_changeWeak_apply W NW n c q _

/-- The coarse return retains the entire mapped fine gamma and the original coarse cancellation. -/
def coarseNu (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q)) :
    Path (GenLoopPrefix.inversePrefix n (F a) (F q)) GenLoop.const :=
  (((gamma W n A0 T0).map (F).continuous).symm.map
    (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
      (GenLoopPrefix.cancellation n (F a))

/-- Every original return time commutes with the full inverse-prefix cancellation. -/
theorem nu_map_apply (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (t : unitInterval) : F (nu W n A0 T0 t) = coarseNu W NW n A0 T0 t := by
  unfold nu coarseNu
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact prefix_source W NW n a _
  · exact congrArg (fun P : Path (GenLoopPrefix.inversePrefix n (F a) (F a))
      (GenLoop.const : GB) ↦ P _) (GenLoopPrefix.cancellation_map n
        (changeWeakMap NW) (changeWeakMap_basepoint NW) a)

/-- The complete coarse tail uses the same original return and supplied spatial factors. -/
def coarseTail (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q)) :
    Path (GenLoopPrefix.inversePrefix n (F a) (GenLoop.transAt 0 (F q) (F c))) (F c) :=
  GenLoopPrefix.tail n (GenLoop.symmAt 0 (F a)) (F q) (F c) (coarseNu W NW n A0 T0)

omit [HasBinaryCoproducts C] in
/-- The full inverse associator is natural before any concatenation parameter is substituted. -/
theorem inverseAssociator_map_apply (a q c : GE) (t : unitInterval) :
    F (GenLoopPrefix.associator n (GenLoop.symmAt 0 a) q c t) =
      GenLoopPrefix.associator n (GenLoop.symmAt 0 (F a)) (F q) (F c) t := by
  have hs : F (GenLoop.symmAt 0 a) = GenLoop.symmAt 0 (F a) :=
    GenLoopPrefix.symm_map n (changeWeakMap NW) (changeWeakMap_basepoint NW) a
  calc
    _ = GenLoopPrefix.associator n (F (GenLoop.symmAt 0 a)) (F q) (F c) t := by
      ext z
      exact GenLoopPrefix.associator_map_apply n (changeWeakMap NW)
        (changeWeakMap_basepoint NW) (GenLoop.symmAt 0 a) q c t z
    _ = _ := congrArg (fun r : GB ↦ GenLoopPrefix.associator n r (F q) (F c) t) hs

/-- The actual fine tail is natural at every original path and spatial coordinate. -/
theorem tail_map_apply (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (t : unitInterval) :
    F (GenLoopPrefix.tail n (GenLoop.symmAt 0 a) q c (nu W n A0 T0) t) =
      coarseTail W NW n (c := c) A0 T0 t := by
  unfold coarseTail GenLoopPrefix.tail
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact inverseAssociator_map_apply W NW n a q c _
  · rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · change F (GenLoop.transAt 0 (nu W n A0 T0 _) c) =
        GenLoop.transAt 0 (coarseNu W NW n A0 T0 _) (F c)
      rw [coproductChangeWeakCubeMap_transAt, nu_map_apply]
    · ext z
      exact GenLoopPrefix.leftUnit_map_apply n (changeWeakMap NW)
        (changeWeakMap_basepoint NW) c _ z

/-- The entire fine delta after mapping, with the inverse source transport displayed. -/
def coarseDelta (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (T1 : Path d (coproductCube W n c q)) :
    Path (GenLoopPrefix.inversePrefix n (F a) (F d)) (F c) :=
  ((((separation W n T1).map (F).continuous).cast rfl
    (coproductChangeWeakCubeMap_transAt W NW n q c).symm).map
      (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
        (coarseTail W NW n A0 T0)

/-- Whole delta naturality retains its exact moving source and both original paths. -/
theorem delta_map (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (T1 : Path d (coproductCube W n c q)) :
    ((delta W n A0 T0 T1).map (F).continuous).cast
      (prefix_source W NW n a d).symm rfl = coarseDelta W NW n A0 T0 T1 := by
  apply Path.ext
  funext t
  change F (delta W n A0 T0 T1 t) = coarseDelta W NW n A0 T0 T1 t
  unfold delta coarseDelta
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact prefix_source W NW n a _
  · exact tail_map_apply W NW n A0 T0 _

/-- The supplied whole Theta comparison and original compact-null coherence determine the word. -/
def terminalHomotopy
    (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (T1 : Path d (coproductCube W n c q)) (N : Path (F c) GenLoop.const)
    (Z : Path (F d0) (F d))
    (Jtheta : Z.symm.Homotopy ((thetaOne W NW n T1).trans
      ((coproductCubePath NW.coarse n N (Path.refl (F q))).trans
        (thetaZero W NW n T0).symm))) :
    (terminal W NW n A0 Z).Homotopy
      ((((separation W n T1).map (F).continuous).cast rfl
        (coproductChangeWeakCubeMap_transAt W NW n q c).symm).trans
          (((genLoopLeftConcatPath NW.coarse n (F q) N).trans
            (genLoopRightUnitPath n (F q))).trans
              ((gamma W n A0 T0).map (F).continuous).symm)) := by
  have H := Path.Homotopy.thetaWord (A0.map (F).continuous) (thetaZero W NW n T0)
    (thetaOne W NW n T1) (coproductCubePath NW.coarse n N (Path.refl (F q)))
    (coproductLeftUnitPath NW.coarse n (F q))
    (coproductSeparationPath n NW.coarse (F c) (F q))
    ((genLoopLeftConcatPath NW.coarse n (F q) N).trans (genLoopRightUnitPath n (F q)))
    Z Jtheta (coproductSeparationNullCoherence NW.coarse n N (F q))
  exact H.cast rfl (by rw [separation_map, gamma_map])

/-- The complete normalized endpoint homotopy consumes the entire supplied geometric square. -/
def normalizedNullHomotopy
    (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (T1 : Path d (coproductCube W n c q)) (N : Path (F c) GenLoop.const)
    (Z : Path (F d0) (F d))
    (Jtheta : Z.symm.Homotopy ((thetaOne W NW n T1).trans
      ((coproductCubePath NW.coarse n N (Path.refl (F q))).trans
        (thetaZero W NW n T0).symm))) :
    (normalizedNull W NW n A0 Z).Homotopy ((delta W n A0 T0 T1).map (F).continuous |>.trans N) := by
  let V := GenLoopPrefix.inversePrefix n (F a)
  let T := ((separation W n T1).map (F).continuous).cast rfl
    (coproductChangeWeakCubeMap_transAt W NW n q c).symm
  let B := (genLoopLeftConcatPath NW.coarse n (F q) N).trans
    (genLoopRightUnitPath n (F q))
  let G := ((gamma W n A0 T0).map (F).continuous).symm.map V.continuous
  let K := GenLoopPrefix.cancellation n (F a)
  have H0 : (((terminal W NW n A0 Z).map V.continuous).trans K).Homotopy
      (((T.map V.continuous).trans ((B.map V.continuous).trans G)).trans K) := by
    simpa only [T, B, G, Path.map_trans] using
      ((terminalHomotopy W NW n A0 T0 T1 N Z Jtheta).map V).hcomp (Path.Homotopy.refl K)
  have H1 := (Path.Homotopy.transAssoc (T.map V.continuous)
    ((B.map V.continuous).trans G) K).trans
      ((Path.Homotopy.refl (T.map V.continuous)).hcomp
        (Path.Homotopy.transAssoc (B.map V.continuous) G K))
  have H2 : ((B.map V.continuous).trans (G.trans K)).Homotopy
      ((coarseTail W NW n A0 T0).trans N) :=
    GenLoopPrefix.nullCoherence n (GenLoop.symmAt 0 (F a)) (F q) (F c) N
      (coarseNu W NW n A0 T0)
  have H3 := ((Path.Homotopy.refl (T.map V.continuous)).hcomp H2).trans
    (Path.Homotopy.transAssoc (T.map V.continuous) (coarseTail W NW n A0 T0) N).symm
  have H := (H0.trans (H1.trans H3)).pathCast (prefix_source W NW n a d) rfl
  refine H.cast rfl ?_
  apply Path.ext
  funext t
  have hd := delta_map W NW n A0 T0 T1
  change (coarseDelta W NW n A0 T0 T1).trans N t = _
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact (congrArg (fun P : Path (GenLoopPrefix.inversePrefix n (F a) (F d)) (F c) ↦
      P _) hd).symm
  · rfl

/-- All independent homotopy, path and original spatial boundary coordinates remain present. -/
theorem normalizedNullHomotopy_boundary
    (A0 : Path a d0) (T0 : Path d0 (coproductCube W n GenLoop.const q))
    (T1 : Path d (coproductCube W n c q)) (N : Path (F c) GenLoop.const)
    (Z : Path (F d0) (F d))
    (Jtheta : Z.symm.Homotopy ((thetaOne W NW n T1).trans
      ((coproductCubePath NW.coarse n N (Path.refl (F q))).trans
        (thetaZero W NW n T0).symm)))
    (s t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    normalizedNullHomotopy W NW n A0 T0 T1 N Z Jtheta (s, t) z = NW.coarse.kBasepoint :=
  (normalizedNullHomotopy W NW n A0 T0 T1 N Z Jtheta (s, t)).property z hz


attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductNormalizedEndpoint.lean:222-233" "adaptation"
    "Original normalized endpoint under its supplied whole Theta comparison; \
      no geometric comparison premise is manufactured"]
  delta_map

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductNormalizedEndpoint.lean:258-297" "adaptation"
    "Original normalized endpoint under its supplied whole Theta comparison; \
      no geometric comparison premise is manufactured"]
  normalizedNullHomotopy

attribute [colib_tag "COL-0302",
  colib_ref "quillen"
    "Quillen/Waldhausen/Additivity/CompactCoproductNormalizedEndpoint.lean:300-310" "adaptation"
    "Original normalized endpoint under its supplied whole Theta comparison; \
      no geometric comparison premise is manufactured"]
  normalizedNullHomotopy_boundary

end CategoryTheory.Waldhausen.Additivity.CompactCoproductEndpoint
