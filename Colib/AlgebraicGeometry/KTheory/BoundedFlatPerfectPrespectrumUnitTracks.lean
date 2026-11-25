/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectNormalizedPullbackUnits
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition
public import Colib.Topology.Prespectrum.HomotopyTransport

/-! # Original unit and composition tracks for native bounded-flat pullback

The original identity and composition tracks include split geometric and chosen-zero normalization
pieces. Both total normalized transformations compare to these actual split tracks by the
original transformation triangles, relative to the whole boundary and the basepoint line.

Implementation provenance: Quillen `BoundedFlat/NormalizedUnitTrack.lean:23-79`,
`BoundedFlat/CompositionTrack.lean:20-34,79-131` and
`Spectrum/BoundedFlatPullback.lean:33-49` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology.LoopPrespectrum
universe u v

namespace CategoryTheory.Waldhausen.IteratedS

private theorem unitHomotopy_transport_level {E F : Topology.LoopPrespectrum.{u}}
    {f g g' : E ⟶ F} (e : g = g') (p : Homotopy f g = Homotopy f g')
    (H : Homotopy f g) (n : ℕ) :
    (p.mp H).level n = H.level n := by
  subst g'
  rfl

/-- The original normalization homotopy realizes the actual inverse rebasing isomorphism. -/
theorem exactOriginalPrespectrumMapIdHomotopy_level
    {C : Type u} [Category.{v} C] (W : Structure C) (n : ℕ) :
    (exactOriginalPrespectrumMapIdHomotopy W).level n =
      (originalPrespectrumTransformationHomotopy W W
        (IsExact.id W.cof W.weq).rebase (IsExact.id W.cof W.weq)
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) rfl
        (CategoryTheory.rebaseFunctorIso (𝟭 C) W.zero W.zero
          (((IsExact.id W.cof W.weq).zero W.isZero).iso W.isZero)).inv
        (fun _ ↦ W.weq_iso _ inferInstance)).level n := by
  unfold exactOriginalPrespectrumMapIdHomotopy
  apply unitHomotopy_transport_level (originalPrespectrumMap_id W)

end CategoryTheory.Waldhausen.IteratedS

namespace AlgebraicGeometry.Scheme.Modules

/-- The original geometric unit includes both the pullback unit and normalization. -/
def boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy (X : Scheme.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (𝟙 X))
      (𝟙 (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) :=
  let W := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  (exactOriginalPrespectrumIsoHomotopy W W
    (boundedAboveFlatPerfectPullback_isExact (𝟙 X))
    (IsExact.id _ _) (boundedAboveFlatPerfectPullbackIdIso X)).trans
      (exactOriginalPrespectrumMapIdHomotopy W)

/-- The total normalized geometric unit with the literal original endpoints. -/
def boundedAboveFlatPerfectNormalizedIdTrack (X : Scheme.{u}) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (𝟙 X))
      (𝟙 (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))) :=
  let W := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  (originalPrespectrumTransformationHomotopy W W
    (boundedAboveFlatPerfectNormalizedPullback_exact (𝟙 X))
    (IsExact.id _ _) (boundedAboveFlatPerfectNormalizedPullback_obj_zero _) rfl
    (boundedAboveFlatPerfectNormalizedPullbackIdIso X).hom
    (fun _ ↦ W.weq_iso _ inferInstance)).cast rfl (originalPrespectrumMap_id W)

/-- The raw original triangle prior to identifying its two whole endpoint tracks. -/
def boundedAboveFlatPerfectNormalizedIdSplitComparison (X : Scheme.{u}) :=
  let W := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  let h := boundedAboveFlatPerfectPullback_isExact (𝟙 X)
  let hI := IsExact.id W.cof W.weq
  let η := normalizedWeakTransformation h hI (boundedAboveFlatPerfectPullbackIdIso X).hom
  let θ := (CategoryTheory.rebaseFunctorIso
    (𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
    W.zero W.zero ((hI.zero W.isZero).iso W.isZero)).inv
  originalPrespectrumTransformationCompositionHomotopy W W
    h.rebase hI.rebase hI
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) rfl
    η θ (normalizedWeakTransformation_weak _ _ _
      (fun _ ↦ W.weq_iso _ inferInstance)) (fun _ ↦ W.weq_iso _ inferInstance)

private theorem originalUnitTransformation_level_congr
    {C : Type u} [Category.{v} C] (W : Structure C) {P Q : C ⥤ C}
    (hP : IsExact W.cof W.weq W.cof W.weq P) (hQ : IsExact W.cof W.weq W.cof W.weq Q)
    (hp : P.obj W.zero = W.zero) (hq : Q.obj W.zero = W.zero)
    {η θ : P ⟶ Q} (hη : ∀ A, W.weq (η.app A)) (hθ : ∀ A, W.weq (θ.app A))
    (e : η = θ) (n : ℕ) :
    (originalPrespectrumTransformationHomotopy W W hP hQ hp hq η hη).level n =
      (originalPrespectrumTransformationHomotopy W W hP hQ hp hq θ hθ).level n := by
  subst θ
  rfl

/-- The normalized identity source has the entire level of the two original split steps. -/
theorem boundedAboveFlatPerfectNormalizedIdSplit_source_level (X : Scheme.{u}) (n : ℕ) :
    (boundedAboveFlatPerfectNormalizedIdTrack X).level n =
      let W := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
      let h := boundedAboveFlatPerfectPullback_isExact (𝟙 X)
      let hI := IsExact.id W.cof W.weq
      let η := normalizedWeakTransformation h hI (boundedAboveFlatPerfectPullbackIdIso X).hom
      let θ := (CategoryTheory.rebaseFunctorIso
        (𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
        W.zero W.zero ((hI.zero W.isZero).iso W.isZero)).inv
      (originalPrespectrumTransformationHomotopy W W h.rebase hI
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) rfl (η ≫ θ)
        (fun A ↦ W.weq.comp_mem _ _
          (normalizedWeakTransformation_weak _ _ _
            (fun _ ↦ W.weq_iso _ inferInstance) A) (W.weq_iso _ inferInstance))).level n := by
  unfold boundedAboveFlatPerfectNormalizedIdTrack
  dsimp only
  rw [Homotopy.cast_level]
  exact originalUnitTransformation_level_congr _ _ _ _ _ _ _
    (boundedAboveFlatPerfectNormalizedPullbackIdIso_hom X) n

/-- The original unit triangle recovers both pieces of the fixed geometric identity track. -/
def boundedAboveFlatPerfectNormalizedIdTrackComparison (X : Scheme.{u}) :
    (boundedAboveFlatPerfectNormalizedIdTrack X).RelHomotopy
      (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X) :=
  (boundedAboveFlatPerfectNormalizedIdSplitComparison X).ofLevels _ _
    (boundedAboveFlatPerfectNormalizedIdSplit_source_level X) (fun n ↦
      Homotopy.trans_level_congr _ _ _ _ n rfl
        (exactOriginalPrespectrumMapIdHomotopy_level
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) n))

-- Keep the endpoint maps abstract here so reduction never expands the unit constructions.
private theorem ofLevels_toContinuousMap {E F : Topology.LoopPrespectrum.{u}}
    {a b a' b' : E ⟶ F} {H K : Homotopy a b}
    (J : H.RelHomotopy K) (H' K' : Homotopy a' b')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n) (n : ℕ) :
    ((J.ofLevels H' K' hH hK).level n).toContinuousMap = (J.level n).toContinuousMap := rfl

/-- Changing the endpoint identifications preserves the original whole unit-triangle value. -/
theorem boundedAboveFlatPerfectNormalizedIdTrackComparison_level (X : Scheme.{u}) (n : ℕ) :
    ((boundedAboveFlatPerfectNormalizedIdTrackComparison X).level n).toContinuousMap =
      ((boundedAboveFlatPerfectNormalizedIdSplitComparison X).level n).toContinuousMap := by
  exact ofLevels_toContinuousMap
    (boundedAboveFlatPerfectNormalizedIdSplitComparison X)
    (boundedAboveFlatPerfectNormalizedIdTrack X)
    (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X)
    (boundedAboveFlatPerfectNormalizedIdSplit_source_level X)
    (fun m ↦ Homotopy.trans_level_congr _ _ _ _ m rfl
      (exactOriginalPrespectrumMapIdHomotopy_level
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) m)) n

/-- The original total normalized geometric comparison with the literal pullback endpoints. -/
def boundedAboveFlatPerfectNormalizedCompTrack {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (f ≫ g))
      (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  let WX := boundedAboveFlatPerfectWaldhausen X.toRingedSpace
  let WY := boundedAboveFlatPerfectWaldhausen Y.toRingedSpace
  let WZ := boundedAboveFlatPerfectWaldhausen Z.toRingedSpace
  (originalPrespectrumTransformationHomotopy WZ WX
    (boundedAboveFlatPerfectNormalizedPullback_exact (f ≫ g))
    ((boundedAboveFlatPerfectNormalizedPullback_exact g).comp
      (boundedAboveFlatPerfectNormalizedPullback_exact f))
    (boundedAboveFlatPerfectNormalizedPullback_obj_zero _)
    ((congrArg (boundedAboveFlatPerfectNormalizedPullback f).obj
      (boundedAboveFlatPerfectNormalizedPullback_obj_zero g)).trans
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero f))
    (boundedAboveFlatPerfectNormalizedPullbackCompIso f g).hom
    (fun _ ↦ WX.weq_iso _ inferInstance)).cast rfl
    (originalPrespectrumMap_comp WZ WY WX
      (boundedAboveFlatPerfectNormalizedPullback_exact g)
      (boundedAboveFlatPerfectNormalizedPullback_exact f)
      (boundedAboveFlatPerfectNormalizedPullback_obj_zero g)
      (boundedAboveFlatPerfectNormalizedPullback_obj_zero f))

/-- The original composition triangle recovers the two fixed binary pullback tracks. -/
def boundedAboveFlatPerfectNormalizedCompTrackComparison {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedAboveFlatPerfectNormalizedCompTrack f g).RelHomotopy
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g) := by
  have J := exactNormalizationCompTrackComparison
    (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
    (boundedAboveFlatPerfectPullback_isExact g)
    (boundedAboveFlatPerfectPullback_isExact f)
    (boundedAboveFlatPerfectPullbackCompIso f g)
  refine J.ofLevels _ _ ?_ (fun _ ↦ rfl)
  intro n
  simp only [boundedAboveFlatPerfectNormalizedCompTrack, Homotopy.cast_level,
    boundedAboveFlatPerfectNormalizedPullbackCompIso_hom]

end AlgebraicGeometry.Scheme.Modules
