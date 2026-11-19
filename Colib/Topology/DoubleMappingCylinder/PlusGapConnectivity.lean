/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.GapConnectivity
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.PiOneSurjective
public import Colib.Topology.PlusConstruction.DisplayedComparisonFundamentalGroup

/-!
# The genuine degree-one gap range for original plus maps

The actual Pi one surjections of two plus maps imply one-connectivity by the
pointed-set fiber sequence. Homotopy excision then gives a one-connected gap
into the actual homotopy pullback of the two double-cylinder legs. In
particular the gap is surjective on Pi one and bijective on Pi zero.

This does not yet compute either leg's fundamental-group kernel. Equal kernels
are not needed for this range statement; the ensuing low-degree kernel chase
is a separate step and is not supplied as a premise or certificate here.
-/

/-! Adapted from `Quillen/Topology/DoubleMappingCylinder/PlusGapConnectivity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory Topology
universe u w

namespace TopCat.DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)

/-- The original double-cylinder gap is one-connected from the two genuine
plus certificates, with no assumed comparison or fundamental-group pushout. -/
theorem plus_gap_isHomotopyConnectedMap_one
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N M : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, w} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, w} g.hom δ M) :
    IsHomotopyConnectedMap (gap f g sq) 1 := by
  let := hf.sourcePathConnected
  let := hf.targetPathConnected
  let := hg.targetPathConnected
  apply gap_isHomotopyConnectedMap f g sq 1 1 1 (by omega)
  · exact isHomotopyConnectedMap_one_of_piOne_surjective f.hom a
      ((basedPiOneMap_surjective_iff f.hom γ).mp hf.surjective)
  · exact isHomotopyConnectedMap_one_of_piOne_surjective g.hom a
      ((basedPiOneMap_surjective_iff g.hom δ).mp hg.surjective)

/-- The degree-one endpoint of the actual excision range is surjectivity,
not injectivity; it retains the original stored cylinder path at the basepoint. -/
theorem plus_gap_piOne_surjective
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N M : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, w} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, w} g.hom δ M) :
    Function.Surjective (HomotopyGroup.piMap 0 (gap f g sq) (x := a) rfl) :=
  (plus_gap_isHomotopyConnectedMap_one f g sq a b c γ δ N M hf hg).homotopyGroupMap_surjective
    a 1 (by omega)

/-- Degree zero is genuinely bijective, including actual target components. -/
theorem plus_gap_piZero_bijective
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N M : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, w} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, w} g.hom δ M) :
    Function.Bijective (HomotopyGroup.map (N := Fin 0) (gap f g sq) (x := a) rfl) :=
  (plus_gap_isHomotopyConnectedMap_one f g sq a b c γ δ N M hf hg).homotopyGroupMap_bijective
    a 0 (by omega)

end TopCat.DoubleCylinder
