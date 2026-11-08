/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstHomologyEuler
public import Colib.RingTheory.Koszul.MappedRegularLength

/-!
# Finite remaining homology of each actual first-stage homology module

The ring map is the original closed-support stalk map from the first-diagonal
ambient to the full first-stage exterior. The regular remaining list is taken
in that actual ambient and generates its original remaining-diagonal ideal.
Cartesian stalk-kernel base change proves that its image is the full remaining
kernel. At an original generic triple point that ideal is an ideal of definition.

Each actual first-stage homology module is finite over the full first-stage
stalk. The nonflat Koszul restriction comparison and native regular Tor
annihilation then give finite length of every remaining homology degree.
There is no caller-supplied Artinian quotient, finite-length condition or action
comparison. The original middle lists can be used through their already proved
regularity and kernel generation in this first-diagonal ambient; no regularity
of their images in the nonreduced first-stage ring is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual first-diagonal ambient stalk at the image of the first-stage point. -/
abbrev correspondenceRemainingFirstAmbientStalk
    (x : correspondenceTripleIncidence f g h i z w v) :=
  (correspondenceFirstDiagonal f g h i).presheaf.stalk
    (correspondenceLeftIntermediateSupportInclusion f g h i z w v
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x))

/-- The original closed-support stalk map, with no invented coefficient-ring action. -/
abbrev correspondenceRemainingFirstAmbientStalkMap
    (x : correspondenceTripleIncidence f g h i z w v) :
    correspondenceRemainingFirstAmbientStalk f g h i z w v x →+*
      correspondenceRemainingOriginalStalk f g h i z w v x :=
  ((correspondenceLeftIntermediateSupportInclusion f g h i z w v).stalkMap
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x)).hom

/-- The actual remaining kernel is the image of the remaining diagonal ideal
in the original first-diagonal ambient, not merely an equality of supports. -/
theorem correspondenceRemainingOriginalStalkIdeal_eq_map_firstAmbient [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v) :
    correspondenceRemainingOriginalStalkIdeal f g h i z w v x =
      (IdealSheafData.stalk (correspondenceSecondDiagonalInclusion f g h i).ker
        (correspondenceLeftIntermediateSupportInclusion f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x))).map
            (correspondenceRemainingFirstAmbientStalkMap f g h i z w v x) := by
  let H := (correspondenceTripleIncidence_firstDiagonal_isPullback f g h i z w v).flip
  have hp := congrArg (fun m => m x) H.w.symm
  simp only [Scheme.Hom.comp_apply] at hp
  have hk := Stacks.Flatness.ker_stalkMap_of_isPullback H x hp
  rw [ker_stalkMap_eq_idealStalk_ker, CommRingCat.hom_comp, ← Ideal.map_map] at hk
  have htransport {p q : correspondenceFirstDiagonal f g h i} (e : p = q) :
      (IdealSheafData.stalk (correspondenceSecondDiagonalInclusion f g h i).ker p).map
        ((correspondenceFirstDiagonal f g h i).presheaf.stalkCongr
          (Inseparable.of_eq e)).hom.hom =
        IdealSheafData.stalk (correspondenceSecondDiagonalInclusion f g h i).ker q := by
    subst q
    simp [TopCat.Presheaf.stalkCongr]
  rw [htransport hp] at hk
  exact hk

/-- Geometric finite colength of a regular remaining list in its actual ambient.
The full generic triple stalk supplies the ideal-of-definition conclusion. -/
theorem isIdealOfDefinition_correspondenceRemainingFirstAmbientList [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → correspondenceRemainingFirstAmbientStalk f g h i z w v x.1)
    (hs : IdealSheafData.stalk (correspondenceSecondDiagonalInclusion f g h i).ker
      (correspondenceLeftIntermediateSupportInclusion f g h i z w v
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    IsIdealOfDefinition (Ideal.span (Set.range (fun j =>
      correspondenceRemainingFirstAmbientStalkMap f g h i z w v x.1 (s j)))) := by
  let := (correspondenceRemainingFirstAmbientStalkMap f g h i z w v x.1).toAlgebra
  have hi := isIdealOfDefinition_correspondenceRemainingOriginalStalkIdeal f g h i z w v x
  rw [correspondenceRemainingOriginalStalkIdeal_eq_map_firstAmbient, hs,
    ModuleCat.map_span_range_algebraMap] at hi
  exact hi

/-- Every remaining homology of every actual first-stage homology module has
finite length at the original generic triple label. Higher first-stage Tor
modules and their genuine first-stage scalar action are retained. -/
theorem length_correspondenceRemainingFirstHomology_ne_top [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v))
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1))
    (htreg : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList t)
    {r : ℕ} (s : Fin r → correspondenceRemainingFirstAmbientStalk f g h i z w v x.1)
    (hsreg : RingTheory.Sequence.IsRegular
      (correspondenceRemainingFirstAmbientStalk f g h i z w v x.1) (List.ofFn s))
    (hs : IdealSheafData.stalk (correspondenceSecondDiagonalInclusion f g h i).ker
      (correspondenceLeftIntermediateSupportInclusion f g h i z w v
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x.1)) =
          Ideal.span (Set.range s)) (b a : ℕ) :
    Module.length (correspondenceRemainingOriginalStalk f g h i z w v x.1)
      ((Koszul.seqComplexTensor
        (fun j => correspondenceRemainingFirstAmbientStalkMap f g h i z w v x.1 (s j))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t htreg ht b)).homology a) ≠
          ⊤ := by
  let := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceLeftIntermediateAmbientInclusion f g h i z w v)
  let := (correspondenceRemainingFirstAmbientStalkMap f g h i z w v x.1).toAlgebra
  exact Koszul.length_seqComplexTensor_map_ne_top_of_isRegular s hsreg _
    (isIdealOfDefinition_correspondenceRemainingFirstAmbientList f g h i z w v x s hs) a

end Stacks.Chow
