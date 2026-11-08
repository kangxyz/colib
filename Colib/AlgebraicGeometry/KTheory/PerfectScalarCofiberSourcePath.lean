/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberChangeWeak
public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectSquareTrack
public import Colib.KTheory.Waldhausen.Fibration.BisimplexChangeWeak

/-!
# The prescribed fine scalar-cofiber source path

The original cofiber triangle followed by the actual fine projection square gives a specified
path from the source-plus-quotient object loop to the source object loop. Its localization
retains both original pieces and their literal half-interval parameters. This supplies the
fine component path for the boundary calculation; the final boundary identity is separate.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSourcePath.lean:36-79`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native perfect complexes retain
ambient monomorphism cofibrations, quasi-isomorphisms, and the actual signed cone.
The original maps, path coordinates, basepoints, and signs are unchanged. -/

@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology HomotopyGroup unitInterval
open CategoryTheory.Waldhausen.Fibration
open scoped Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original fine weak projection supplies its whole prescribed square track. -/
def perfectScalarProjectionObjectTrack (X : Scheme.{u}) (r : Γ(X, ⊤)) (K :
  ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    Path.Homotopy
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop
        ((ExtensionCategory.middle (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
          (perfectScalarExtension X r K)))
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop K) :=
  (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weakObjectSquareTrack
    (perfectScalarProjection X r K)
    (perfectScalarProjection_weak X r K)

/-- The actual triangle and actual projection square form the specified fine source path. -/
def perfectScalarCofiberSourceTrack (X : Scheme.{u}) (r : Γ(X, ⊤)) (K :
  ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    Path.Homotopy (((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop
      K).trans
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop
        ((ExtensionCategory.cofiber (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
          (perfectScalarExtension X r K))))
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectLoop K) :=
  (perfectScalarCofiberObjectTrack X r K).trans (perfectScalarProjectionObjectTrack X r K)

/-- The original localization map retains every point of the fine projection square. -/
theorem perfectScalarProjectionObjectTrack_changeWeak
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r : Γ(X, ⊤)) (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace))) (s t : unitInterval) :
    changeWeakMap (perfectOpenNested j) (perfectScalarProjectionObjectTrack X r K (s, t)) =
      (perfectOpenNested j).coarse.weakObjectSquareTrack (perfectScalarProjection X r K)
        ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K)) (s, t) :=
  weakObjectSquare_changeWeak (perfectOpenNested j) (perfectScalarProjection X r K)
    (perfectScalarProjection_weak X r K) _ _

/-- The original source track localizes to its exact prism face and fine projection halves. -/
theorem perfectScalarCofiberSourceTrack_changeWeak
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) (s t
      : unitInterval) :
    changeWeakMap (perfectOpenNested j) (perfectScalarCofiberSourceTrack X r K (s, t)) =
      if h : (s : ℝ) ≤ 1 / 2 then
        perfectOpenScalarCofiberCompositionCube j r q hq K
          (⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩, 1, t)
      else
        (perfectOpenNested j).coarse.weakObjectSquareTrack (perfectScalarProjection X r K)
          ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))
          (⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩, t) := by
  unfold perfectScalarCofiberSourceTrack
  rw [Path.Homotopy.trans_apply]
  split_ifs with h
  · exact perfectScalarCofiberObjectTrack_prism_face j r q hq K _ t
  · exact perfectScalarProjectionObjectTrack_changeWeak j r K _ t

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSourcePath.lean:36-79" "adaptation"
  "The original fine cofiber triangle followed by its actual weak projection square, with both
    half-interval parameters retained"]
  perfectScalarCofiberSourceTrack_changeWeak

end AlgebraicGeometry.Scheme.Modules
