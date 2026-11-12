/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.RefinedOverlap
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedGeneratedGraph
public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
/-! # Literal smooth-site maps for the simultaneously refined diagram -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {k : Type u} [Field k] {S X C Y A T : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine T]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (U : X.Opens) (V : S.Opens)
  [IsAffine V.toScheme] [IsAffine (parameterOpen q U V).toScheme]
  (π : C ⟶ S) (j : Y ⟶ C) [IsOpenImmersion j]
  (p : Y ⟶ X) [Etale p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (v : T ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
  (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)

local instance : IsAffine (sourceBaseOpen π V v).toScheme :=
  sourceBaseOpen_affine π V v (show IsAffineOpen V from ‹IsAffine V.toScheme›)

local instance : Smooth (parameterProjection q U V) :=
  SmoothOfRelativeDimension.smooth 1 _
local instance : Smooth (firstInclusion q U V π j p hq ≫ compactificationProjection π V) :=
  SmoothOfRelativeDimension.smooth 1 _
local instance : Smooth (sourceBaseMap π V v ≫ compactificationProjection π V) :=
  SmoothOfRelativeDimension.smooth 1 _

local notation "π'" => compactificationProjection π V
local notation "j'" => firstInclusion q U V π j p hq
local notation "p'" => firstMap q U V p
local notation "a'" => secondMap q U V a
local notation "q'" => parameterProjection q U V
local notation "α" => pullback.fst p' a'
local notation "β" => pullback.snd p' a'
local notation "v'" => sourceBaseMap π V v
local notation "t'" => V.ι ≫ t

/-- The complete first refined source with its actual structure map. -/
abbrev refinedFirstSite : SmoothSite (Spec (.of k)) := SmoothSite.mk ((j' ≫ π') ≫ t')
/-- The complete second refined source over the same parameter. -/
abbrev refinedSecondSite : SmoothSite (Spec (.of k)) := SmoothSite.mk ((a' ≫ q') ≫ t')
/-- Their literal overlap, with no chosen-point or dense-open substitute. -/
abbrev refinedOverlapSite : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk (commonProjection π' j' α ≫ t')
/-- The original retained target over V, not restricted by U. -/
abbrev refinedTargetSite : SmoothSite (Spec (.of k)) := SmoothSite.mk ((v' ≫ π') ≫ t')

/-- The actual first projection used in the signed restriction difference. -/
def refinedAlpha : refinedOverlapSite t q U V π j p hq a ⟶ refinedFirstSite t q U V π j p hq :=
  SmoothSite.homMk α (by
    change α ≫ ((j' ≫ π') ≫ t') = commonProjection π' j' α ≫ t'
    exact (Category.assoc α (j' ≫ π') t').symm)

/-- The actual independent second projection. -/
def refinedBeta : refinedOverlapSite t q U V π j p hq a ⟶ refinedSecondSite t q U V a :=
  SmoothSite.homMk β (by
    change β ≫ ((a' ≫ q') ≫ t') = commonProjection π' j' α ≫ t'
    have h := commonProjection_fixed q' π' j' p'
      (firstInclusion_projection q U V π j p hq) a' α β pullback.condition
    exact (Category.assoc β (a' ≫ q') t').symm.trans (congrArg (fun f => f ≫ t') h.symm))

/-- The actual map to the original retained target, preserving the original
factorization through the compactification. -/
def refinedGraph : refinedOverlapSite t q U V π j p hq a ⟶ refinedTargetSite t V π v :=
  SmoothSite.homMk (refinedTargetMap q U V π j p hq a v φ hφ) (by
    change refinedTargetMap q U V π j p hq a v φ hφ ≫ ((v' ≫ π') ≫ t') =
      commonProjection π' j' α ≫ t'
    have h := retainedTarget_base π' v' j' α
      (refinedTargetMap q U V π j p hq a v φ hφ)
      (refinedTargetMap_inclusion q U V π j p hq a v φ hφ)
    exact (Category.assoc _ (v' ≫ π') t').symm.trans (congrArg (fun f => f ≫ t') h))

omit [IsSeparated q] [IsOpenImmersion j] in
@[simp]
theorem refinedAlpha_left : (refinedAlpha t q U V π j p hq a).left = α := rfl
omit [IsOpenImmersion j] in
@[simp]
theorem refinedBeta_left : (refinedBeta t q U V π j p hq a).left = β := rfl
omit [IsSeparated q] [IsOpenImmersion j] [IsOpenImmersion v] in
@[simp]
theorem refinedGraph_left :
    (refinedGraph t q U V π j p hq a v φ hφ).left =
      refinedTargetMap q U V π j p hq a v φ hφ := rfl

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
