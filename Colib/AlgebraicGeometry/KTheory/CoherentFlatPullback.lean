/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Coherent.Pullback
public import Colib.AlgebraicGeometry.KTheory.Restriction
public import Colib.KTheory.Quillen.SmallModel.Functoriality

/-!
# Flat pullback on the original coherent G-groups

The actual native coherent pullback induces the map on the existing public
G-groups. Its identity, composition and open-restriction laws retain the
original geometric natural isomorphisms. Flatness is required; no arbitrary
underived pullback on coherent G-theory is asserted.

Implementation source: `Quillen/AlgebraicGeometry/Scheme/FlatPullback.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd` (the original G-map clauses).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme
variable {X Y Z : Scheme.{u}}

/-- The original flat geometric pullback on public coherent G-theory. -/
def pullbackG [IsLocallyNoetherian X] (f : X ⟶ Y) [Flat f] (n : ℕ) :
    G Y n →* G X n :=
  (Modules.coherentExactPullback f).smallKMap.{u + 1} n

/-- The public map is induced by the literal coherent pullback exact functor. -/
theorem pullbackG_eq_smallKMap [IsLocallyNoetherian X] (f : X ⟶ Y) [Flat f] (n : ℕ) :
    pullbackG f n = (Modules.coherentExactPullback f).smallKMap.{u + 1} n := rfl

/-- Pullback along the identity is the identity on the unchanged public group. -/
@[simp high]
theorem pullbackG_id (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    pullbackG (𝟙 X) n = MonoidHom.id (G X n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso.{u + 1}
    (F := Modules.coherentExactPullback (𝟙 X))
    (G := ExactFunctor.id (Modules.coherentExactStructure X))
    (Modules.coherentPullbackIdIso X) n).trans (ExactFunctor.smallKMap_id _ n)

/-- Actual flat pullback is contravariantly functorial on the original G-groups. -/
@[simp high]
theorem pullbackG_comp [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (n : ℕ) :
    pullbackG (f ≫ g) n = (pullbackG f n).comp (pullbackG g n) := by
  exact (ExactFunctor.smallKMap_eq_of_natIso.{u + 1}
    (F := Modules.coherentExactPullback (f ≫ g))
    (G := (Modules.coherentExactPullback g).comp (Modules.coherentExactPullback f))
    (Modules.coherentPullbackCompIso f g) n).trans (ExactFunctor.smallKMap_comp _ _ n)

/-- Flat pullback agrees with the original geometric open restriction. -/
theorem pullbackG_eq_restrictG [IsLocallyNoetherian X]
    (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    pullbackG j n = restrictG j n :=
  ExactFunctor.smallKMap_eq_of_natIso.{u + 1}
    (F := Modules.coherentExactPullback j) (G := Modules.coherentRestrictionExact j)
    (Modules.coherentRestrictIsoPullback j).symm n

end AlgebraicGeometry.Scheme
