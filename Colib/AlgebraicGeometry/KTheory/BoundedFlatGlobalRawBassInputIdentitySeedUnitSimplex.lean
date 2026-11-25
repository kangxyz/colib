/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitPrismEvaluation

/-!
# The two six-reference Laurent unit families

The old family uses the forward Laurent coordinate of the source scheme and the new family
uses the forward coordinate of the target scheme. The two normalized geometric pullbacks in
each family retain their original exact unit isomorphisms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedUnitSimplex

open CategoryTheory.Waldhausen.SmallWaldhausenCategory

private theorem id_mp_heq {A B : Sort u} (p : A = B) (x : A) :
    HEq (id (p.mp x)) x := by
  cases p
  rfl

private theorem target_transport_lift {V W : WideSubcategory preservesZero.{u}}
    (S : ModelSimplex V W 5)
    {a b : StdSimplex ℝ (Fin 6)} {p q : Path a b} (J : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K K' : Homotopy f g} (e : K = K')
    (M : H.RelHomotopy K) (M' : H.RelHomotopy K') (hM : HEq M' M)
    (h : HomotopyLift S J M) : HomotopyLift S J M' := by
  subst K'
  cases eq_of_heq hM
  exact h

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The old six references use the forward Laurent unit on the source fiber. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalRawBassInputIdentitySeedUnitSimplex.lean:50"
  "adaptation" "The original normalized geometric source-fiber simplex"]
def oldSimplex :=
  UnitTrackPostcompSimplex.simplex
    (laurent.map g) (laurentProjection.app Y) (laurentScalar (op Y))

/-- The new six references use the actual forward unit on the target fiber. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalRawBassInputIdentitySeedUnitSimplex.lean:55"
  "adaptation" "The original normalized geometric target-fiber simplex"]
def newSimplex :=
  UnitTrackPrecompSimplex.simplex
    (laurentProjection.app X) g (laurentScalar (op X))

private theorem old_target_eq :
    ((boundedAboveFlatPerfectUnitHomotopy
      (laurent.map g ≫ laurentProjection.app Y)
      (Units.map (laurent.map g).appTop.hom.toMonoidHom
        (laurentScalar (op Y)))).trans
      (InputUnit.oldComposition g)) =
    ((InputUnit.commonUnit g).trans
      (InputUnit.oldComposition g)) := by
  unfold InputUnit.commonUnit
  rw [laurentUnit_map]

private theorem old_comparison_heq :
    HEq (InputUnit.oldComparison g)
      (boundedAboveFlatPerfectUnitTrackPostcomp
        (laurent.map g) (laurentProjection.app Y)
        (laurentScalar (op Y))) := by
  unfold InputUnit.oldComparison
  exact id_mp_heq _ _

/-- Every point of the existing old comparison has its whole six-reference lift.
The actual Laurent-unit equality only transports the original target track. -/
theorem old_comparison_lift :
    HomotopyLift (oldSimplex g) UnitPrismParameters.parameter
      (InputUnit.oldComparison g) :=
  target_transport_lift (oldSimplex g) UnitPrismParameters.parameter
    (old_target_eq g) _ _ (old_comparison_heq g)
    (UnitTrackPostcompSimplex.native_lift
      (laurent.map g) (laurentProjection.app Y)
      (laurentScalar (op Y)))

/-- Every point of the existing new comparison retains its original ofLevels transport.
The actual scheme-square equality and its original unit-track congrArg remain in that record. -/
theorem new_comparison_lift :
    HomotopyLift (newSimplex g) UnitPrismParameters.parameter
      (InputUnit.newComparison g) := by
  unfold InputUnit.newComparison
  exact HomotopyLift.ofLevels (newSimplex g)
    (UnitTrackPrecompSimplex.native_lift (laurentProjection.app X) g
      (laurentScalar (op X))) _ _ _ _

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedUnitSimplex
