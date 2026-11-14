/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphComponent
public import Colib.AlgebraicGeometry.Correspondences.Graph.Incidence

/-!
# The retained-source equation on the original incidence scheme

No pointwise
coordinate extensionality is used: every equality is between scheme morphisms.
The incidence scheme is the native one, without reduction or a flatness premise.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {V U Y : SmoothSite (Spec (CommRingCat.of k))}
variable (f : V ⟶ U)

/-- Scheme-level retained-source equality, before native Tor pushforward. -/
theorem incidence_retained_source_eq (s : V.left)
    (z : pullback (C := Scheme) U.hom Y.hom) :
    correspondenceIncidenceMap V.hom U.hom (SmoothSite.product U Y).hom
        (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s)
        (ambientLift k U Y z) ≫
      pullback.snd V.hom (SmoothSite.product U Y).hom ≫ pullback.fst U.hom Y.hom =
    correspondenceIncidenceMap V.hom U.hom (SmoothSite.product U Y).hom
        (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s)
        (ambientLift k U Y z) ≫
      pullback.fst V.hom (SmoothSite.product U Y).hom ≫ f.left := by
  let g := correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s
  let w := ambientLift k U Y z
  let i := (integralComponentAt g).subschemeι
  let j := (integralComponentAt w).subschemeι
  let a := i ≫ pullback.snd V.hom U.hom
  let b := j ≫ pullback.fst U.hom (SmoothSite.product U Y).hom
  change correspondenceIncidenceMap V.hom U.hom (SmoothSite.product U Y).hom g w ≫ _ = _
  rw [correspondenceIncidenceMap_snd_assoc]
  change (pullback.snd a b ≫ j) ≫ pullback.snd U.hom
    (SmoothSite.product U Y).hom ≫ pullback.fst U.hom Y.hom = _
  rw [Category.assoc, image_component_source_eq k U Y z]
  have hmiddle := pullback.condition (f := a) (g := b)
  change pullback.fst a b ≫ (i ≫ pullback.snd V.hom U.hom) =
    pullback.snd a b ≫ (j ≫ pullback.fst U.hom (SmoothSite.product U Y).hom) at hmiddle
  rw [← hmiddle]
  rw [integralComponentAt_graphMap_snd V.hom U.hom f.left
    (MorphismProperty.Over.w f) s]
  simp only [correspondenceIncidenceMap_fst_assoc, correspondenceIncidenceLeft, Category.assoc]
  rfl

end AlgebraicGeometry.Cor.RelativeGraph
