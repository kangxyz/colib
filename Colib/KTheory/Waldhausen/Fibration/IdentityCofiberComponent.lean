/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.GrothendieckComparison.IdentityCofiberSuffix
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.LeftComponentTranslation

/-!
# Component translation using the actual identity-cofiber triangle

The suffix path is the original identity-cofiber triangle, with its literal chosen-zero
quotient. Its localization keeps every original comparison and loop coordinate. The resulting
component equivalence is explicitly matched to that prism face; no equality with the standard
suffix-removal path or final Laurent boundary normalization is asserted here.
-/
/-! Implementation provenance: Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Only `identityCofiberComponentEquiv` from
`Quillen/Waldhausen/Fibration/IdentityCofiberComponent.lean:62-67`.
The pending identity-cofiber suffix is imported unchanged; no change-weak results are added.
Independent category universes and all original hypotheses are preserved.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
open CategoryTheory.Waldhausen.QuotientRows
open scoped Topology Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (W : Structure C) (A : C)

/-- Left prefix followed by the actual identity triangle gives the prism-matched equivalence. -/
def identityCofiberComponentEquiv (n : ℕ) :
    HomotopyGroup.Pi n (Path W.kBasepoint W.kBasepoint) (Path.refl W.kBasepoint) ≃
      HomotopyGroup.Pi n (Path W.kBasepoint W.kBasepoint) (W.kZeroObjectLoop A) :=
  (loopLeftTranslationHomotopyEquiv (W.kZeroObjectLoop A) n).trans
    (pathTransport (W.identityCofiberSuffixPath A) n)

attribute [colib_tag "COL-0297"] identityCofiberComponentEquiv

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/IdentityCofiberComponent.lean:62-67" "adaptation"
  "The degree-n constructor is left translation followed by transport along the prescribed
    identity-cofiber suffix; this construction does not assert normalization in every degree"]
  identityCofiberComponentEquiv

end CategoryTheory.Waldhausen.Structure
