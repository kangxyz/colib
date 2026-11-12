/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.NativePencilFibers
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeSupport

/-!
# Whole finite-flat spans on a retained polynomial pencil

The source and target legs use the actual paired polynomial support. The
Cartesian and section spans retain the same finite schemes and projections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

private theorem pairedLegs_over_base {A B D S : Scheme.{u}}
    {f : A ⟶ S} {g : B ⟶ S} (m : D ⟶ pullback f g)
    (p : D ⟶ A) (q : D ⟶ B)
    (hp : m ≫ pullback.fst f g = p) (hq : m ≫ pullback.snd f g = q) :
    p ≫ f = q ≫ g := by
  rw [← hp, ← hq]
  simp only [Category.assoc, pullback.condition]

private theorem endpointLegs_over_base {A B C D S : Scheme.{u}}
    (i : A ⟶ B) (f : C ⟶ B) (g : C ⟶ D)
    (a : A ⟶ S) (b : B ⟶ S) (d : D ⟶ S)
    (hi : i ≫ b = a) (hf : f ≫ b = g ≫ d) :
    pullback.fst i f ≫ a = (pullback.snd i f ≫ g) ≫ d := by
  rw [← hi, ← Category.assoc, pullback.condition]
  simp only [Category.assoc, hf]

/-- The whole span on the Cartesian pullback by the specified source map. -/
def cartesianEndpointSpan {A B C D S : Scheme.{u}} [IsNoetherian A]
    (a : A ⟶ S) (c : C ⟶ S) [IsSeparated c] [LocallyOfFiniteType c]
    (σ : A ⟶ B) (f : D ⟶ B) (g : D ⟶ C)
    (hFin : IsFinite f) (hFlat : Flat f)
    (h : pullback.fst σ f ≫ a = (pullback.snd σ f ≫ g) ≫ c) :
    finiteCorrespondences a c :=
  letI : IsFinite f := hFin
  letI : Flat f := hFlat
  ofFiniteFlatSpanRaw a c (pullback.fst σ f) (pullback.snd σ f ≫ g) h

variable {k : Type u} [Field k] {S X V : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) (q : X ⟶ S) (r : V ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  (L : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L] (a c : Γ(L, ⊤))

local notation "U" => SmoothSite.mk (q ≫ t)

/-- The actual source leg of the whole retained pencil on the native cylinder. -/
def nativeRetainedFamilySource :
    (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme ⟶
      (affineLineCylinder.obj U).left :=
  familySource (q ≫ t) (pullback.fst q r) L a c ≫ (nativeParameterIso (.of k) U).inv

local notation "F" => nativeRetainedFamilySource t q r L a c
local notation "G" => retainedFamilyTarget t q r L a c

/-- The original actual native-family legs satisfy the ground-field equation. -/
theorem nativeRetainedFamily_base : F ≫ (affineLineCylinder.obj U).hom = G ≫ (r ≫ t) :=
  pairedLegs_over_base (nativeRetainedFamilyPair t q r L a c) F G
    (nativeRetainedFamilyPair_fst t q r L a c) (nativeRetainedFamilyPair_snd t q r L a c)

/-- Pairing the literal family legs recovers the actual retained family map. -/
theorem nativeRetainedFamilyPair_eq_lift :
    nativeRetainedFamilyPair t q r L a c =
      pullback.lift F G (nativeRetainedFamily_base t q r L a c) := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact nativeRetainedFamilyPair_fst t q r L a c
  · rw [pullback.lift_snd]
    exact nativeRetainedFamilyPair_snd t q r L a c

/-- The actual Cartesian endpoint legs satisfy the same ground-field equation. -/
theorem nativeRetainedEndpoint_base (s : k) :
    pullback.fst (nativeAffineSection (.of k) U s).left F ≫ (q ≫ t) =
      (pullback.snd (nativeAffineSection (.of k) U s).left F ≫ G) ≫ (r ≫ t) :=
  endpointLegs_over_base (nativeAffineSection (.of k) U s).left F G (q ≫ t)
    (affineLineCylinder.obj U).hom (r ≫ t)
    (MorphismProperty.Over.w (nativeAffineSection (.of k) U s))
    (nativeRetainedFamily_base t q r L a c)

omit [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)] in
/-- The original literal zero-scheme source and target maps commute over the field. -/
theorem retainedZero_base (s : Γ(L, ⊤)) :
    ((zeroScheme (pullback q r) L s).subschemeι ≫ pullback.fst q r) ≫ (q ≫ t) =
      ((zeroScheme (pullback q r) L s).subschemeι ≫ pullback.snd q r) ≫ (r ≫ t) := by
  simp only [Category.assoc, pullback.condition_assoc]

variable [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]

/-- The literal zero-scheme span, over the unchanged smooth-site sources. -/
def retainedZeroSpan (s : Γ(L, ⊤))
    (hf : IsFinite ((zeroScheme (pullback q r) L s).subschemeι ≫ pullback.fst q r))
    (hflat : Flat ((zeroScheme (pullback q r) L s).subschemeι ≫ pullback.fst q r)) :
    finiteCorrespondences (q ≫ t) (r ≫ t) :=
  letI : IsNoetherian X := isNoetherian_of_finiteType (q ≫ t)
  letI := hf
  letI := hflat
  ofFiniteFlatSpanRaw (q ≫ t) (r ≫ t)
    ((zeroScheme (pullback q r) L s).subschemeι ≫ pullback.fst q r)
    ((zeroScheme (pullback q r) L s).subschemeι ≫ pullback.snd q r)
    (retainedZero_base t q r L s)

/-- The whole finite-flat span of the literal paired retained family. -/
def nativeRetainedFamilySpan :
    let f := F
    ∀ [_hFamilyFin : IsFinite f] [_hFamilyFlat : Flat f],
      finiteCorrespondences (affineLineCylinder.obj U).hom (r ≫ t) := by
  intro f hFin hFlat
  have hNoeth : IsNoetherian (affineLineCylinder.obj U).left :=
    inferInstanceAs (IsNoetherian (affineLineCylinder.obj U).left)
  have hSep : IsSeparated (r ≫ t) := inferInstance
  have hLFT : LocallyOfFiniteType (r ≫ t) := inferInstance
  have hBase : f ≫ (affineLineCylinder.obj U).hom = G ≫ (r ≫ t) :=
    nativeRetainedFamily_base t q r L a c
  exact @ofFiniteFlatSpanRaw (Spec (.of k)) (affineLineCylinder.obj U).left V
    (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme hNoeth
    (affineLineCylinder.obj U).hom (r ≫ t) hSep hLFT f hFin hFlat G hBase

end AlgebraicGeometry.Cor
