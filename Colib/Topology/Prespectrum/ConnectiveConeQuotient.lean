/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.ConeStableCokernel
public import Colib.Topology.Prespectrum.ConeLinearExcision
public import Colib.Topology.Prespectrum.ConeFiniteGrowth
public import Colib.Topology.Prespectrum.StrictSquarePointHEP
public import Colib.Topology.Prespectrum.PushoutVanishing
public import Colib.Topology.Prespectrum.StableVanishing

/-!
# Degree-zero quotients of the original connective square cones

Point HEP and offset-zero all-point growth pass through the actual unlooped
span and cone without a loss. Their original degree-zero target inclusions are
epimorphisms and annihilate both original chart arrows. No parameter-loop or
integer-degree transport is needed for these assertions.

Adapted from the original construction in
`Quillen/Topology/Prespectrum/ConnectiveConeQuotient.lean`.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum

/-- Actual well-based levels and the offset-zero linear vanishing bound. -/
structure LinearZeroGrowth (E : LoopPrespectrum.{u}) : Prop where
  point : ∀ n, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n)))
  vanishing : ∀ n (x : E.space (n + 2)) k, k < n + 2 →
    Subsingleton (HomotopyGroup.Pi k (E.space (n + 2)) x)

namespace LinearZeroGrowth
variable {E F : LoopPrespectrum.{u}}

/-- The original signed degree-minus-one colimit vanishes at every actual stage. -/
theorem negativeOne (h : LinearZeroGrowth E) :
    Subsingleton (stableHomotopyGroup E (-1)) := by
  apply stableHomotopyGroup_subsingleton_of_stages E (-1)
  intro n
  let := h.vanishing ((-(-1 : ℤ)).toNat + n)
    (E.point ((-(-1 : ℤ)).toNat + n + 2)) ((-1 : ℤ).toNat + n + 2) (by omega)
  exact inferInstanceAs (Subsingleton (Additive (HomotopyGroup.Pi
    ((-1 : ℤ).toNat + n + 2) (E.space ((-(-1 : ℤ)).toNat + n + 2))
    (E.point ((-(-1 : ℤ)).toNat + n + 2)))))

/-- The actual linear growth discharges the genuine cone-to-fiber excision. -/
theorem excision (hE : LinearZeroGrowth E) (hF : LinearZeroGrowth F) (f : E ⟶ F) :
    IsStableEquivalence (mappingConeFiberComparison f) :=
  mappingConeFiberComparison_isStableEquivalence_of_linearGrowth f 0
    (fun n => hE.point (n + 2)) (fun n => hF.point (n + 2))
    hE.vanishing hF.vanishing

variable (S : Arrow (Arrow LoopPrespectrum.{u}))
  (hA : LinearZeroGrowth S.left.left) (hB : LinearZeroGrowth S.left.right)
  (hC : LinearZeroGrowth S.right.left) (hD : LinearZeroGrowth S.right.right)

include hA hB hC in
/-- The original reduced span has the same zero-offset growth and actual point HEP. -/
theorem span : LinearZeroGrowth (StrictSquare.span S) where
  point n := StrictSquare.span_point_homotopyExtensionProperty S n
    (hA.point n) (hB.point n) (hC.point n)
  vanishing n x k hk := HomotopyPushout.homotopyGroup_subsingleton
    S.left.hom S.hom.left (n + 2) n (hA.point _) (hB.point _) (hC.point _)
    (hA.vanishing n) (hB.vanishing n) (hC.vanishing n) x k hk

include hA hB hC hD

/-- The actual unlooped cone preserves the bound without changing its offset. -/
theorem cone : LinearZeroGrowth (mappingCone (StrictSquare.comparison S)) where
  point n := StrictSquare.cone_point_homotopyExtensionProperty S n
    (hA.point n) (hB.point n) (hC.point n) (hD.point n)
  vanishing := mappingCone_growth (StrictSquare.comparison S) 0
    (fun n => (span S hA hB hC).point (n + 2)) (fun n => hD.point (n + 2))
    (span S hA hB hC).vanishing hD.vanishing

/-- Every original zero-degree cone class has an original Laurent-corner representative. -/
theorem inclusion_epi : Epi ((stableHomotopyFunctor 0).map
    (mappingConeInclusion (StrictSquare.comparison S))) := by
  let := (span S hA hB hC).negativeOne
  exact (AddCommGrpCat.epi_iff_surjective _).mpr
    (stableMappingConeInclusion_zero_surjective (StrictSquare.comparison S)
      ((span S hA hB hC).excision hD (StrictSquare.comparison S)))

private theorem comparison_zero :
    (stableHomotopyFunctor 0).map (StrictSquare.comparison S) ≫
      (stableHomotopyFunctor 0).map
        (mappingConeInclusion (StrictSquare.comparison S)) = 0 := by
  let := (span S hA hB hC).negativeOne
  exact (stableMappingConeZeroShortComplex (StrictSquare.comparison S)
    ((span S hA hB hC).excision hD (StrictSquare.comparison S))).zero

/-- The first actual chart dies under the original zero-degree inclusion. -/
@[reassoc]
theorem left_zero : (stableHomotopyFunctor 0).map S.hom.right ≫
    (stableHomotopyFunctor 0).map
      (mappingConeInclusion (StrictSquare.comparison S)) = 0 := by
  let i : S.left.right ⟶ StrictSquare.span S :=
    HomotopyPushout.inl S.left.hom S.hom.left
  have h : i ≫ StrictSquare.comparison S = S.hom.right :=
    HomotopyPushout.inl_desc _ _ _ _ _
  rw [← h, (stableHomotopyFunctor 0).map_comp, Category.assoc,
    comparison_zero S hA hB hC hD, comp_zero]

/-- The second actual chart dies under the original zero-degree inclusion. -/
@[reassoc]
theorem right_zero : (stableHomotopyFunctor 0).map S.right.hom ≫
    (stableHomotopyFunctor 0).map
      (mappingConeInclusion (StrictSquare.comparison S)) = 0 := by
  let i : S.right.left ⟶ StrictSquare.span S :=
    HomotopyPushout.inr S.left.hom S.hom.left
  have h : i ≫ StrictSquare.comparison S = S.right.hom :=
    HomotopyPushout.inr_desc _ _ _ _ _
  rw [← h, (stableHomotopyFunctor 0).map_comp, Category.assoc,
    comparison_zero S hA hB hC hD, comp_zero]

end LinearZeroGrowth
end Topology.LoopPrespectrum
