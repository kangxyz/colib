/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Support
public import Colib.AlgebraicGeometry.Correspondences.Incidence

/-!
# The literal product of the original incidence with a parameter

The two coordinates retain the entire native incidence scheme, including its
nilpotents and all components. No cycle, generator type, or reduced replacement
is introduced. This coordinate construction works over any base scheme; neither
admissibility nor geometric integrality is needed.

Adapted from `motivic_source_a6805c4`, Exterior/Identity/Incidence.lean:35-94,243-256.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {S : Scheme.{u}} (X Y Z T : SmoothSite S)
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)

/-- The full original incidence times the parameter, as a literal native pullback. -/
abbrev exteriorIncidenceProduct : Scheme.{u} :=
  pullback (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) T.hom

/-- The first support coordinate uses the shared parameter. -/
def exteriorIncidenceProductFirst : exteriorIncidenceProduct X Y Z T z w ⟶
    exteriorIdentitySupport X Y T (integralComponentAt z) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _) (by
      simpa only [Category.assoc, correspondenceIncidenceLeft,
        exteriorSupportSourceProjection] using
        (pullback.condition
          (f := correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) (g := T.hom)))

/-- The second support coordinate uses the same parameter. -/
def exteriorIncidenceProductSecond : exteriorIncidenceProduct X Y Z T z w ⟶
    exteriorIdentitySupport Y Z T (integralComponentAt w) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (pullback.snd _ _) (by
      have hbase :
          pullback.fst
              (exteriorSupportTargetProjection X Y (integralComponentAt z))
              (exteriorSupportSourceProjection Y Z (integralComponentAt w)) ≫
            (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom) =
          pullback.snd
              (exteriorSupportTargetProjection X Y (integralComponentAt z))
              (exteriorSupportSourceProjection Y Z (integralComponentAt w)) ≫
            (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom) := by
        rw [exteriorSupport_projection_base X Y (integralComponentAt z),
          ← Category.assoc, pullback.condition, Category.assoc]
      rw [Category.assoc, ← hbase]
      simpa only [Category.assoc, correspondenceIncidenceLeft,
        exteriorSupportSourceProjection] using
        (pullback.condition
          (f := correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) (g := T.hom)))

@[reassoc (attr := simp)]
theorem exteriorIncidenceProductFirst_fst :
    exteriorIncidenceProductFirst X Y Z T z w ≫
      pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
        T.hom = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceProductFirst_snd :
    exteriorIncidenceProductFirst X Y Z T z w ≫
      pullback.snd (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
        T.hom = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceProductSecond_fst :
    exteriorIncidenceProductSecond X Y Z T z w ≫
      pullback.fst (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom)
        T.hom = pullback.fst _ _ ≫ pullback.snd _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorIncidenceProductSecond_snd :
    exteriorIncidenceProductSecond X Y Z T z w ≫
      pullback.snd (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom)
        T.hom = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The two coordinates agree as morphisms to the entire middle product. -/
@[reassoc]
theorem exteriorIncidenceProduct_condition :
    exteriorIncidenceProductFirst X Y Z T z w ≫
        exteriorIdentityTarget X Y T (integralComponentAt z) =
      exteriorIncidenceProductSecond X Y Z T z w ≫
        exteriorIdentitySource Y Z T (integralComponentAt w) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, exteriorIdentityTarget_fst, exteriorIdentitySource_fst,
      exteriorIncidenceProductFirst_fst_assoc, exteriorIncidenceProductSecond_fst_assoc]
    exact congrArg (fun f => pullback.fst _ _ ≫ f)
      (pullback.condition
        (f := exteriorSupportTargetProjection X Y (integralComponentAt z))
        (g := exteriorSupportSourceProjection Y Z (integralComponentAt w)))
  · simp only [Category.assoc, exteriorIdentityTarget_snd, exteriorIdentitySource_snd,
      exteriorIncidenceProductFirst_snd, exteriorIncidenceProductSecond_snd]

/-- The full product scheme is determined by its two actual support coordinates. -/
theorem exteriorIncidenceProduct_hom_ext {W : Scheme.{u}}
    {f g : W ⟶ exteriorIncidenceProduct X Y Z T z w}
    (h₁ : f ≫ exteriorIncidenceProductFirst X Y Z T z w =
      g ≫ exteriorIncidenceProductFirst X Y Z T z w)
    (h₂ : f ≫ exteriorIncidenceProductSecond X Y Z T z w =
      g ≫ exteriorIncidenceProductSecond X Y Z T z w) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc, exteriorIncidenceProductFirst_fst] using
        congrArg (fun h => h ≫
          pullback.fst (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
            T.hom) h₁
    · simpa only [Category.assoc, exteriorIncidenceProductSecond_fst] using
        congrArg (fun h => h ≫
          pullback.fst (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom)
            T.hom) h₂
  · simpa only [Category.assoc, exteriorIncidenceProductFirst_snd] using
      congrArg (fun h => h ≫
        pullback.snd (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
          T.hom) h₁

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Incidence.lean:35-94,243-256"
  "adaptation"
  "Full native incidence product coordinates; arbitrary base and no admissibility assumptions"]
  exteriorIncidenceProductFirst exteriorIncidenceProductSecond
  exteriorIncidenceProduct_condition exteriorIncidenceProduct_hom_ext

end Stacks.Chow
