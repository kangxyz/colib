/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Incidence
public import Colib.AlgebraicGeometry.Chow.FinitePushforward
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# The actual common triple incidence

The two parenthesizations of three actual integral supports are the literal
iterated pullbacks. Their isomorphism is Mathlib's native `pullbackAssoc`, not a
second associator. It respects every support projection and the common outer
source-target map. That output map is finite for three finite correspondences
and a separated final target. The projection onto the right pair is not asserted
finite. No incidence scheme is reduced, and no Tor coefficient is assigned.

Finite native cycle pushforward is unchanged under the actual associator. This
is a geometric transport identity, not equality of the two iterated Tor cycles
and not associativity of finite-correspondence composition.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Associativity/Incidence.lean`,
Git blob `899403be62a10dbb7971d39c9c91ac69530b4fe0`. Its explicit associator is
replaced by the existing native pullback associator. Stacks 02R5 is used only for
the finite pushforward composition identity, not for a Tor associativity claim.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
variable (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The left-parenthesized actual triple incidence, with full scheme structure. -/
abbrev correspondenceTripleIncidence : Scheme.{u} :=
  pullback (correspondenceIncidenceRight f g h z w)
    ((integralComponentAt v).subschemeι ≫ pullback.fst h i)

/-- The right-parenthesized actual triple incidence, with full scheme structure. -/
abbrev correspondenceRightTripleIncidence : Scheme.{u} :=
  pullback ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    (correspondenceIncidenceLeft g h i w v)

/-- The literal projection to the first pair incidence. -/
abbrev correspondenceTripleIncidenceFst :
    correspondenceTripleIncidence f g h i z w v ⟶ correspondenceIncidence f g h z w :=
  pullback.fst _ _

/-- The literal projection to the third integral support. -/
abbrev correspondenceTripleIncidenceSnd :
    correspondenceTripleIncidence f g h i z w v ⟶ (integralComponentAt v).subscheme :=
  pullback.snd _ _

/-- The triple incidence's original-source map. -/
abbrev correspondenceTripleIncidenceSource : correspondenceTripleIncidence f g h i z w v ⟶ X :=
  correspondenceTripleIncidenceFst f g h i z w v ≫ correspondenceIncidenceLeft f g h z w

/-- The triple incidence's final-target map. -/
abbrev correspondenceTripleIncidenceTarget : correspondenceTripleIncidence f g h i z w v ⟶ W :=
  correspondenceTripleIncidenceSnd f g h i z w v ≫
    (integralComponentAt v).subschemeι ≫ pullback.snd h i

/-- The actual three-support associator is the native pullback associator itself. -/
def correspondenceTripleIncidenceAssoc :
    correspondenceTripleIncidence f g h i z w v ≅
      correspondenceRightTripleIncidence f g h i z w v :=
  pullbackAssoc ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    ((integralComponentAt w).subschemeι ≫ pullback.fst g h)
    ((integralComponentAt w).subschemeι ≫ pullback.snd g h)
    ((integralComponentAt v).subschemeι ≫ pullback.fst h i)

/-- The associator preserves the first actual support projection. -/
@[reassoc (attr := simp)]
theorem correspondenceTripleIncidenceAssoc_fst :
    (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫ pullback.fst _ _ =
      correspondenceTripleIncidenceFst f g h i z w v ≫ pullback.fst _ _ :=
  pullbackAssoc_hom_fst _ _ _ _

/-- The associator preserves the middle actual support projection. -/
@[reassoc (attr := simp)]
theorem correspondenceTripleIncidenceAssoc_snd_fst :
    (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫
        pullback.snd _ _ ≫ pullback.fst _ _ =
      correspondenceTripleIncidenceFst f g h i z w v ≫ pullback.snd _ _ :=
  pullbackAssoc_hom_snd_fst _ _ _ _

/-- The associator preserves the third actual support projection. -/
@[reassoc (attr := simp)]
theorem correspondenceTripleIncidenceAssoc_snd_snd :
    (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫
        pullback.snd _ _ ≫ pullback.snd _ _ =
      correspondenceTripleIncidenceSnd f g h i z w v :=
  pullbackAssoc_hom_snd_snd _ _ _ _

/-- Both actual outer maps agree over the original base. -/
@[reassoc]
theorem correspondenceTripleIncidence_condition :
    correspondenceTripleIncidenceSource f g h i z w v ≫ f =
      correspondenceTripleIncidenceTarget f g h i z w v ≫ i := by
  calc
    _ = correspondenceTripleIncidenceFst f g h i z w v ≫
        (correspondenceIncidenceLeft f g h z w ≫ f) := Category.assoc _ _ _
    _ = correspondenceTripleIncidenceFst f g h i z w v ≫
        (correspondenceIncidenceRight f g h z w ≫ h) := by
      rw [correspondenceIncidence_condition]
    _ = correspondenceTripleIncidenceSnd f g h i z w v ≫
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h) := by
      simpa only [Category.assoc] using congrArg (fun e => e ≫ h)
        (pullback.condition (f := correspondenceIncidenceRight f g h z w)
          (g := (integralComponentAt v).subschemeι ≫ pullback.fst h i))
    _ = _ := by simp only [correspondenceTripleIncidenceTarget, Category.assoc,
      pullback.condition (f := h) (g := i)]

/-- The literal outer source-target map from the actual common incidence. -/
def correspondenceTripleIncidenceMap :
    correspondenceTripleIncidence f g h i z w v ⟶ pullback f i :=
  pullback.lift (correspondenceTripleIncidenceSource f g h i z w v)
    (correspondenceTripleIncidenceTarget f g h i z w v)
    (correspondenceTripleIncidence_condition f g h i z w v)

@[reassoc (attr := simp)]
theorem correspondenceTripleIncidenceMap_fst :
    correspondenceTripleIncidenceMap f g h i z w v ≫ pullback.fst f i =
      correspondenceTripleIncidenceSource f g h i z w v := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceTripleIncidenceMap_snd :
    correspondenceTripleIncidenceMap f g h i z w v ≫ pullback.snd f i =
      correspondenceTripleIncidenceTarget f g h i z w v := pullback.lift_snd _ _ _

/-- The right-parenthesized output uses the inverse of the native associator. -/
def correspondenceRightTripleIncidenceMap :
    correspondenceRightTripleIncidence f g h i z w v ⟶ pullback f i :=
  (correspondenceTripleIncidenceAssoc f g h i z w v).inv ≫
    correspondenceTripleIncidenceMap f g h i z w v

/-- The actual output maps commute with the native associator. -/
@[reassoc (attr := simp)]
theorem correspondenceTripleIncidenceAssoc_map :
    (correspondenceTripleIncidenceAssoc f g h i z w v).hom ≫
        correspondenceRightTripleIncidenceMap f g h i z w v =
      correspondenceTripleIncidenceMap f g h i z w v := by
  simp only [correspondenceRightTripleIncidenceMap, Iso.hom_inv_id_assoc]

/-- The right-parenthesized output has the original first-support source projection. -/
@[reassoc (attr := simp)]
theorem correspondenceRightTripleIncidenceMap_fst :
    correspondenceRightTripleIncidenceMap f g h i z w v ≫ pullback.fst f i =
      pullback.fst _ _ ≫ (integralComponentAt z).subschemeι ≫ pullback.fst f g := by
  apply (cancel_epi (correspondenceTripleIncidenceAssoc f g h i z w v).hom).mp
  simp only [correspondenceTripleIncidenceAssoc_map_assoc, correspondenceTripleIncidenceMap_fst,
    correspondenceTripleIncidenceAssoc_fst_assoc]
  rfl

/-- The right-parenthesized output has the original last-support target projection. -/
@[reassoc (attr := simp)]
theorem correspondenceRightTripleIncidenceMap_snd :
    correspondenceRightTripleIncidenceMap f g h i z w v ≫ pullback.snd f i =
      pullback.snd _ _ ≫ correspondenceIncidenceRight g h i w v := by
  apply (cancel_epi (correspondenceTripleIncidenceAssoc f g h i z w v).hom).mp
  simp only [correspondenceTripleIncidenceAssoc_map_assoc, correspondenceTripleIncidenceMap_snd,
    correspondenceIncidenceRight, correspondenceTripleIncidenceAssoc_snd_snd_assoc]

/-- Finiteness of the first triple projection is just base change of the third support. -/
theorem isFinite_correspondenceTripleIncidenceFst
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceTripleIncidenceFst f g h i z w v) := by
  have := hv.1
  infer_instance

/-- The common incidence is finite over the original source. -/
theorem isFinite_correspondenceTripleIncidenceSource
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceTripleIncidenceSource f g h i z w v) := by
  have := hz.1
  have := hw.1
  have := isFinite_correspondenceTripleIncidenceFst f g h i z w v hv
  dsimp [correspondenceTripleIncidenceSource, correspondenceIncidenceLeft]
  infer_instance

/-- The actual common output map is finite, by separated-target cancellation. -/
theorem isFinite_correspondenceTripleIncidenceMap [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceTripleIncidenceMap f g h i z w v) := by
  have := isFinite_correspondenceTripleIncidenceSource f g h i z w v hz hw hv
  have : IsFinite (correspondenceTripleIncidenceMap f g h i z w v ≫ pullback.fst f i) := by
    simpa only [correspondenceTripleIncidenceMap_fst] using
      (inferInstance : IsFinite (correspondenceTripleIncidenceSource f g h i z w v))
  exact IsFinite.of_comp (correspondenceTripleIncidenceMap f g h i z w v) (pullback.fst f i)

/-- Reassociation does not alter the actual weighted finite pushforward.
This transports a given native cycle, not an unproved iterated Tor-cycle equality. -/
theorem finiteCyclePushforward_correspondenceTripleIncidenceAssoc [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (c : AlgebraicCycle (correspondenceTripleIncidence f g h i z w v) ℤ) :
    letI := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
    letI : IsFinite (correspondenceRightTripleIncidenceMap f g h i z w v) :=
      inferInstanceAs (IsFinite ((correspondenceTripleIncidenceAssoc f g h i z w v).inv ≫
        correspondenceTripleIncidenceMap f g h i z w v))
    finiteCyclePushforward (correspondenceRightTripleIncidenceMap f g h i z w v)
        (finiteCyclePushforward (correspondenceTripleIncidenceAssoc f g h i z w v).hom c) =
      finiteCyclePushforward (correspondenceTripleIncidenceMap f g h i z w v) c := by
  let := isFinite_correspondenceTripleIncidenceMap f g h i z w v hz hw hv
  let : IsFinite (correspondenceRightTripleIncidenceMap f g h i z w v) :=
    inferInstanceAs (IsFinite ((correspondenceTripleIncidenceAssoc f g h i z w v).inv ≫
      correspondenceTripleIncidenceMap f g h i z w v))
  simp only [finiteCyclePushforward_comp_apply, correspondenceTripleIncidenceAssoc_map]

end Stacks.Chow
