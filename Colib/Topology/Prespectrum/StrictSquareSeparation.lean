/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StrictSquareCone
public import Colib.Topology.Prespectrum.HomotopyPushoutSeparation
public import Colib.Topology.Prespectrum.ConeLoopSeparation

/-!
# T1 separation of the actual strict-square Bass value

The existing reduced double cylinder, cone and compact-open parameter loop retain T1
separation at every original level, including zero. No point HEP assertion is made.

Implementation provenance: T1 clauses of `Quillen/Topology/Prespectrum/StrictSquareTopology.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable (S : Arrow (Arrow LoopPrespectrum.{u})) (n : ℕ)

/-- T1 separation passes through the original double cylinder. -/
instance spanSpaceT1Space [T1Space (S.left.left.space n)] [T1Space (S.left.right.space n)]
    [T1Space (S.right.left.space n)] : T1Space ((span S).space n) :=
  HomotopyPushout.prespectrumSpaceT1Space S.left.hom S.hom.left n

/-- T1 separation passes through the unchanged cone and parameter loop. -/
instance loopedConeSpaceT1Space [T1Space (S.left.left.space n)]
    [T1Space (S.left.right.space n)] [T1Space (S.right.left.space n)]
    [T1Space (S.right.right.space n)] :
    T1Space ((strictSquareLoopedConeFunctor.obj S).space n) := by
  change T1Space ((parameterLooping (mappingCone (comparison S))).space n)
  infer_instance

end Topology.LoopPrespectrum.StrictSquare
