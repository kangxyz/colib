/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumCompositionHomotopy
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIsoNaturality
public import Colib.Topology.Prespectrum.SelfTrackRelativeHomotopy
public import Colib.Topology.Prespectrum.SelfTrackStableConcatenation

/-!
# Stable operations of the native strict-zero automorphism tracks

The actual transformation-composition triangle identifies the stable operation of a composite
strict-zero automorphism with the reversed sum. In particular, the actual inverse automorphism has
the negative stable operation. These statements use native strict chosen-zero morphisms,
without transporting through normalized exact functors or changing the Laurent track.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/ModelSelfTrackStableOperation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology.LoopPrespectrum
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology SSet
variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- The original strict-zero composition triangle gives the actual reversed stable sum. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ModelSelfTrackStableOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem prespectrumIsoHomotopy_stableOperation_comp
    (e e' : F.hom.toFunctor ≅ F.hom.toFunctor) (d : ℤ) :
    (prespectrumIsoHomotopy F (e ≪≫ e')).stableOperation d =
      (prespectrumIsoHomotopy F e').stableOperation d +
        (prespectrumIsoHomotopy F e).stableOperation d :=
  ((prespectrumTransformationCompositionHomotopy e.hom e'.hom
    (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ W.obj.waldhausen.weq_iso _ inferInstance)).stableOperation_eq d).trans
      (Homotopy.stableOperation_trans _ _ d)

/-- The original identity automorphism induces zero on the integer-graded stable operation. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ModelSelfTrackStableOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem prespectrumIsoHomotopy_stableOperation_refl (d : ℤ) :
    (prespectrumIsoHomotopy F (Iso.refl F.hom.toFunctor)).stableOperation d = 0 := by
  have h := prespectrumIsoHomotopy_stableOperation_comp F
    (Iso.refl F.hom.toFunctor) (Iso.refl F.hom.toFunctor) d
  simp only [Iso.refl_trans] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- The actual inverse strict-zero automorphism gives the negative original stable operation. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ModelSelfTrackStableOperation.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem prespectrumIsoHomotopy_stableOperation_symm
    (e : F.hom.toFunctor ≅ F.hom.toFunctor) (d : ℤ) :
    (prespectrumIsoHomotopy F e.symm).stableOperation d =
      -(prespectrumIsoHomotopy F e).stableOperation d := by
  have h := prespectrumIsoHomotopy_stableOperation_comp F e e.symm d
  rw [Iso.self_symm_id, prespectrumIsoHomotopy_stableOperation_refl] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end CategoryTheory.Waldhausen.IteratedS
