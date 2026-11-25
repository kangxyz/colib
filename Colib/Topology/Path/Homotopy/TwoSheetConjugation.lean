/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# The literal conjugation word between two sheets with independent endpoints

Adapted from Quillen's `Aglib/Topology/Path/TwoSheetConjugation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

For paths in any topological space, the stated unit homotopy and the two null-comparison
homotopies construct the literal conjugation comparison between the independently named tips.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Path.Homotopy.TwoSheetConjugation
variable {X : Type u} [TopologicalSpace X]
  {a₀ a₁ b₀ b₁ c₀ c₁ : X}

/-- The scalar reverse cancellation retains its proof-only double-reversal cast. -/
theorem reverseCancellation_apply (L : Path a₀ b₀) (r s : I) :
    Path.Homotopy.reflSymmTrans L (r, s) =
      Path.Homotopy.reflTransSymm L.symm (r, s) := rfl

/-- Retype only the reversed-concatenation source, retaining the whole comparison. -/
def retypeSource (L : Path a₀ b₀) (N : Path b₀ c₀) (W : Path a₀ c₁)
    (Z : Path c₀ c₁) (J : ((N.symm.trans L.symm).trans W).Homotopy Z) :
    ((L.trans N).symm.trans W).Homotopy Z :=
  J.cast (congrArg (fun p ↦ p.trans W) (Path.trans_symm L N).symm) rfl

/-- The source transport preserves both original time coordinates. -/
theorem retypeSource_apply (L : Path a₀ b₀) (N : Path b₀ c₀) (W : Path a₀ c₁)
    (Z : Path c₀ c₁) (J : ((N.symm.trans L.symm).trans W).Homotopy Z) (r s : I) :
    retypeSource L N W Z J (r, s) = J (r, s) := rfl

/-- Two unit and null comparisons give the original conjugation word between distinct tips. -/
def comparison (U : Path a₀ a₁) (V : Path b₀ b₁)
    (L₀ : Path a₀ b₀) (L₁ : Path a₁ b₁)
    (N₀₀ : Path a₀ c₀) (N₀₁ : Path a₁ c₁)
    (N₁₀ : Path b₀ c₀) (N₁₁ : Path b₁ c₁)
    (JU : (U.trans L₁).Homotopy (L₀.trans V))
    (JN₀ : N₀₀.Homotopy (L₀.trans N₁₀))
    (JN₁ : N₀₁.Homotopy (L₁.trans N₁₁)) :
    (N₀₀.symm.trans (U.trans N₀₁)).Homotopy
      (N₁₀.symm.trans (V.trans N₁₁)) := by
  let T := V.trans N₁₁
  have JU' : (U.trans (L₁.trans N₁₁)).Homotopy (L₀.trans T) :=
    (Path.Homotopy.transAssoc U L₁ N₁₁).symm.trans
      ((JU.hcomp (Path.Homotopy.refl N₁₁)).trans
        (Path.Homotopy.transAssoc L₀ V N₁₁))
  have JC : (L₀.symm.trans (L₀.trans T)).Homotopy T :=
    (Path.Homotopy.transAssoc L₀.symm L₀ T).symm.trans
      (((Path.Homotopy.reflSymmTrans L₀).symm.hcomp
        (Path.Homotopy.refl T)).trans (Path.Homotopy.reflTrans T))
  have J : ((L₀.trans N₁₀).symm.trans (U.trans (L₁.trans N₁₁))).Homotopy
      (N₁₀.symm.trans T) :=
    retypeSource L₀ N₁₀ (U.trans (L₁.trans N₁₁)) (N₁₀.symm.trans T)
      ((Path.Homotopy.transAssoc N₁₀.symm L₀.symm (U.trans (L₁.trans N₁₁))).trans
        ((Path.Homotopy.refl N₁₀.symm).hcomp
          (((Path.Homotopy.refl L₀.symm).hcomp JU').trans JC)))
  exact (JN₀.symm₂.hcomp ((Path.Homotopy.refl U).hcomp JN₁)).trans J

end Path.Homotopy.TwoSheetConjugation
