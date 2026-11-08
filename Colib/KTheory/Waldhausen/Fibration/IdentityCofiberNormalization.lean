/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Fibration.IdentityCofiberComponent

/-!
# Normalization of the original identity-cofiber component translation

The actual identity-cofiber triangle and the existing standard suffix-removal path give
identical maps on the first homotopy group of the loop space. This follows from the already
proved path naturality of the original component equivalences. Neither path is replaced in
its defining continuous family. Comparison with the normalized Laurent unit remains separate.
-/
/-! Implementation provenance: Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Both degree-one comparisons from
`Quillen/Waldhausen/Fibration/IdentityCofiberNormalization.lean:25-46`.
They compare induced maps, not paths, and assert no Laurent or boundary sign.
Independent category universes and all original hypotheses are preserved.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (W : Structure C) (A : C)

/-- The original identity triangle and standard suffix removal induce the same degree-one map. -/
theorem identityCofiberSuffixPath_transport_eq
    (b : HomotopyGroup.Pi 1 (Path W.kBasepoint W.kBasepoint)
      ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint))) :
    pathTransport (W.identityCofiberSuffixPath A) 1 b =
      pathTransport (loopRightUnitPath (W.kZeroObjectLoop A)) 1 b := by
  obtain ⟨a, rfl⟩ := (loopComponentHomotopyEquiv
    ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint)) 1).surjective b
  exact (loopComponentHomotopyEquiv_pathTransport
    (W.identityCofiberSuffixPath A) 1 a).trans
      (loopComponentHomotopyEquiv_pathTransport
        (loopRightUnitPath (W.kZeroObjectLoop A)) 1 a).symm

/-- The prism-matched equivalence agrees with the original standard left-component normalization.
-/
theorem identityCofiberComponentEquiv_eq :
    W.identityCofiberComponentEquiv A 1 =
      loopLeftComponentHomotopyEquiv (W.kZeroObjectLoop A) 1 := by
  apply Equiv.ext
  intro a
  exact W.identityCofiberSuffixPath_transport_eq A
    (loopLeftTranslationHomotopyEquiv (W.kZeroObjectLoop A) 1 a)

attribute [colib_tag "COL-0297"] identityCofiberSuffixPath_transport_eq
  identityCofiberComponentEquiv_eq

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/Fibration/IdentityCofiberNormalization.lean:25-46" "adaptation"
  "The prescribed identity-cofiber suffix and standard right-unit path induce equal
    degree-one transport, and the component equivalence agrees with standard left-component
    normalization in degree one; neither equality of the suffix paths nor a sign is asserted"]
  identityCofiberSuffixPath_transport_eq identityCofiberComponentEquiv_eq

end CategoryTheory.Waldhausen.Structure
