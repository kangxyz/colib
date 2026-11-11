/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedTwistedFiber
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedFullFiber
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProducts

/-! # The original current-stage full-open fiber lift at the integer Spec row

The existing fine localization theorem is transported through the actual original
seed-iterate, twisted, and current-stage comparisons, preserving the selected full null.
The support category and the current-stage scalar seed are unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology AlgebraicGeometry Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

/-- The actual current-stage same-null full-open lift is stable on the integral Spec row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterCurrentFullFiber.lean:27"
  "adaptation" "Original actual full-open fiber lift through the same selected null."]
theorem currentLift_spec_isStableEquivalence
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (currentLift f.left (specUnder.obj a)) :=
  (current_twisted_lift_stable_iff f.left (specUnder.obj a)).mpr
    ((iterated_twisted_lift_stable_iff f.left (specUnder.obj a)).mp
      (iteratedLift_spec_isStableEquivalence f a))

/-- At the actual integer basepoint the same current-stage lift is stable for the original pair. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterCurrentFullFiber.lean:37"
  "adaptation" "Original actual full-open fiber lift through the same selected null."]
theorem currentLift_integer_isStableEquivalence {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] :
    IsStableEquivalence (currentLift f (op (Spec (CommRingCat.of (ULift.{u} ℤ))))) := by
  let g : Over.mk (specULiftZIsTerminal.from P) ⟶ Over.mk (specULiftZIsTerminal.from Q) :=
    Over.homMk f (specULiftZIsTerminal.hom_ext _ _)
  let : IsOpenImmersion g.left := by change IsOpenImmersion f; infer_instance
  let : CompactSpace (Over.mk (specULiftZIsTerminal.from P)).left := by
    change CompactSpace P
    infer_instance
  let : CompactSpace (Over.mk (specULiftZIsTerminal.from Q)).left := by
    change CompactSpace Q
    infer_instance
  let : QuasiSeparatedSpace (Over.mk (specULiftZIsTerminal.from Q)).left := by
    change QuasiSeparatedSpace Q
    infer_instance
  exact currentLift_spec_isStableEquivalence g (Under.mk (𝟙 _))

/-- Every signed stable homotopy degree sees the same current-stage lift as an iso. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterCurrentFullFiber.lean:55"
  "adaptation" "Original actual full-open fiber lift through the same selected null."]
theorem currentLift_integer_signed_isIso {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]
    (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (currentLift f (op (Spec (CommRingCat.of (ULift.{u}
      ℤ)))))) :=
  currentLift_integer_isStableEquivalence f d

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull

attribute [colib_tag "COL-0598"]
  currentLift_integer_isStableEquivalence

attribute [colib_tag "COL-0598"]
  currentLift_spec_isStableEquivalence

attribute [colib_tag "COL-0598"]
  currentLift_integer_signed_isIso

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
