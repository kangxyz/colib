/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeFiberComparison

/-!
# Naturality of the original cone descent with its whole null track

A strict source square, the original target square and equality of every specified null-track
value give a literal square of the original quotient cone descents. Endpoints alone do not
supply the whole-track hypothesis. No equivalence or excision is used in this construction.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u
namespace Topology.LoopPrespectrum
variable {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B)
    {G H : LoopPrespectrum.{u}} (g : A.right ⟶ G) (h : B.right ⟶ H) (c : G ⟶ H)
    (J : Homotopy (A.hom ≫ g) (zeroHom A.left G))
    (K : Homotopy (B.hom ≫ h) (zeroHom B.left H))

/-- The actual target square and entire original cylinder give literal naturality of descent. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/ConeDescNaturality.lean:30-40"
  "adaptation" "Literal naturality of the original cone descents with the entire specified track"]
theorem mappingConeDesc_naturality (hg : sq.right ≫ h = g ≫ c)
    (hJ : ∀ n s x, c.map n (J.level n (s, x)) = K.level n (s, sq.left.map n x)) :
    mappingConeMap sq ≫ mappingConeDesc B.hom h K = mappingConeDesc A.hom g J ≫ c := by
  have hs : sq.right ≫ mappingConeInclusion B.hom =
      mappingConeInclusion A.hom ≫ mappingConeMap sq := (mappingConeInclusionSquare sq).w
  apply mappingCone_hom_ext A.hom
  · rw [← Category.assoc, ← hs, Category.assoc,
      mappingConeInclusion_desc, hg, ← Category.assoc, mappingConeInclusion_desc]
  · intro n s x
    exact (hJ n s x).symm

end Topology.LoopPrespectrum
