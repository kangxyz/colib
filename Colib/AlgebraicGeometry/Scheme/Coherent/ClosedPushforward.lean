/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Coherent.Exact
public import StacksFrontier.AlgebraicGeometry.CoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison

/-!
# Actual coherent direct image along a closed immersion

The literal native sheaf pushforward restricts to coherent sheaves on locally
Noetherian schemes. Its exactness is inherited from the original module
pushforward. Stacks' Tag 087T identifies its essential image with the actual
modules annihilated by the defining ideal; it does not identify this image
with all modules supported on the closed subset.

References: the Stacks Project, Tag 087T. Implementation source:
`Quillen/AlgebraicGeometry/Scheme/Coherent/ClosedImmersion/Devissage.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd` (the original pushforward factor).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [IsLocallyNoetherian Z] [IsLocallyNoetherian X]

/-- The original closed sheaf pushforward on the existing native coherent categories. -/
def closedPushforward : SheafOfModules.CoherentModules Z.ringCatSheaf ⥤
    SheafOfModules.CoherentModules X.ringCatSheaf :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward i) (by
    intro M
    have : M.obj.IsCoherent := M.property
    have : M.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent M.obj
    exact Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
      i M.obj)

instance closedPushforward_additive : (closedPushforward i).Additive where
  map_add {M N f g} := by
    apply ObjectProperty.hom_ext
    exact (Scheme.Modules.pushforward i).map_add

/-- The closed pushforward is exact for the native coherent exact structures. -/
def closedPushforwardExact :
    ExactFunctor (coherentExactStructure Z) (coherentExactStructure X) where
  toFunctor := closedPushforward i
  map_conflation S hS := by
    apply (coherent_shortExact_iff_map X _).2
    exact ((coherent_shortExact_iff_map Z S).1 hS).map_of_exact (Scheme.Modules.pushforward i)

omit [IsLocallyNoetherian Z] in
/-- The original closed direct image remains literal after forgetting coherence. -/
theorem closedPushforward_comp_inclusion :
    closedPushforward i ⋙ ObjectProperty.ι (fun M : X.Modules => M.IsCoherent) =
      ObjectProperty.ι (fun M : Z.Modules => M.IsCoherent) ⋙ Scheme.Modules.pushforward i := rfl

omit [IsLocallyNoetherian Z] in
/-- Actual closed pushforward factors through the annihilated coherent modules of Tag 087T. -/
theorem closedPushforward_factorization :
    Stacks.AlgebraicGeometry.Tag087TCoherentImage.coherentPushforward i ⋙
      ObjectProperty.ιOfLE (show (fun M : X.Modules =>
          M.IsCoherent ∧ Stacks.AlgebraicGeometry.Tag087TCoherentImage.AnnihilatedByKer i M) ≤
          (fun M : X.Modules => M.IsCoherent) from fun _ h => h.1) =
      closedPushforward i := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent
