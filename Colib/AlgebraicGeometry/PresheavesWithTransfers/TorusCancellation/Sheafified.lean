/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Suslin
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Sheafification
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# The sheafified cochain comparison for Suslin cancellation

The signed cancellation map remains a quasi-isomorphism after placement in
cochain degrees at most zero and exact transfer-preserving Nisnevich
sheafification. The coefficient map is the original reduced torus comparison.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The original comparison on the actual Nisnevich singular cochain complexes. -/
def torusCancellationSheafCochainMap (Y : Cor k) :
    singularSheafCochainComplex k ((representableLarge k).obj Y) 0 ⟶
      singularSheafCochainComplex k (torusCancellationTarget k Y) 0 :=
  (singularSheafCochainFunctor k 0).map (torusCancellationMap k Y)

/-- The placed and sheafified original comparison is a quasi-isomorphism. -/
theorem torusCancellationSheafCochainMap_quasiIso (Y : Cor k) :
    QuasiIso (torusCancellationSheafCochainMap k Y) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let f := torusCancellationChainMap k Y
  let : QuasiIso f := torusCancellationChainMap_quasiIso k Y
  let g := HomologicalComplex.extendMap f e
  let : QuasiIso g := (HomologicalComplex.quasiIso_extendMap_iff f e).2
    (torusCancellationChainMap_quasiIso k Y)
  change QuasiIso (((nisnevichSheafify k).mapHomologicalComplex (.up ℤ)).map g)
  infer_instance

end AlgebraicGeometry.PresheafWithTransfers
