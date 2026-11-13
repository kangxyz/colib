/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Iterated.LocalizedFunctoriality
public import Colib.AlgebraicGeometry.KTheory.PerfectPullbackFunctor

/-!
Selection from `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, excluding the separate flat identification.

Arbitrary derived pullback of original perfect spectra on qc schemes in the constructed stable
localization. The actual bounded-flat inclusion is inverted via its proved stable equivalence; flat
maps and original K-groups are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The image of the bounded-flat perfect prespectrum in the stable localization. -/
abbrev boundedAboveFlatLocalizedSpectrum (X : Scheme.{u}) : StableLocalization.{u+1} :=
  localizedSpectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)

/-- The image of the perfect prespectrum in the stable localization. -/
abbrev perfectLocalizedSpectrum (X : Scheme.{u}) : StableLocalization.{u+1} :=
  localizedSpectrum (perfectComplexesWaldhausen X.toRingedSpace)

/-- The morphism in the stable localization induced by bounded-flat pullback. -/
def boundedAboveFlatLocalizedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatLocalizedSpectrum Y ⟶ boundedAboveFlatLocalizedSpectrum X :=
  localizedSpectrumMap _ _ (boundedAboveFlatPerfectPullback_isExact f)

@[simp] theorem boundedAboveFlatLocalizedPullback_id (X : Scheme.{u}) :
    boundedAboveFlatLocalizedPullback (𝟙 X) = 𝟙 _ :=
  (localizedSpectrumMap_iso _ _ (boundedAboveFlatPerfectPullback_isExact (𝟙 X))
    (Waldhausen.IsExact.id _ _) (boundedAboveFlatPerfectPullbackIdIso X)).trans
      (localizedSpectrumMap_id
      _)

@[simp] theorem boundedAboveFlatLocalizedPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y
      ⟶ Z) :
    boundedAboveFlatLocalizedPullback (f ≫ g) = boundedAboveFlatLocalizedPullback g ≫
      boundedAboveFlatLocalizedPullback f :=
  (localizedSpectrumMap_iso _ _ (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
    ((boundedAboveFlatPerfectPullback_isExact g).comp (boundedAboveFlatPerfectPullback_isExact f))
    (boundedAboveFlatPerfectPullbackCompIso f g)).trans (localizedSpectrumMap_comp _ _ _ _ _)

/-- The actual bounded-flat enhanced geometric pullback is a contravariant functor. -/
def boundedAboveFlatLocalizedSpectrumFunctor : Scheme.{u}ᵒᵖ ⥤ StableLocalization.{u+1} where
  obj X := boundedAboveFlatLocalizedSpectrum X.unop
  map f := boundedAboveFlatLocalizedPullback f.unop
  map_id X := boundedAboveFlatLocalizedPullback_id X.unop
  map_comp f g := boundedAboveFlatLocalizedPullback_comp g.unop f.unop

/-- The literal inclusion is inverted only after its actual all-degree K-equivalence was proved. -/
def boundedAboveFlatPerfectSpectrumIso (X : Scheme.{u}) [CompactSpace X] :
    boundedAboveFlatLocalizedSpectrum X ≅ perfectLocalizedSpectrum X :=
  localizedSpectrumMapIso _ _ (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace)
    (boundedAboveFlatPerfectToPerfectKMap_bijective X.toRingedSpace)

@[simp] theorem boundedAboveFlatPerfectSpectrumIso_hom (X : Scheme.{u}) [CompactSpace X] :
    (boundedAboveFlatPerfectSpectrumIso X).hom =
      localizedSpectrumMap _ _ (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace) := rfl

/-- Arbitrary derived pullback as a genuine morphism between original perfect
spectra in the constructed localization. Both ambient schemes are qc. -/
def perfectLocalizedPullback {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) : perfectLocalizedSpectrum Y ⟶ perfectLocalizedSpectrum X :=
  (boundedAboveFlatPerfectSpectrumIso Y).inv ≫ boundedAboveFlatLocalizedPullback f ≫
    (boundedAboveFlatPerfectSpectrumIso X).hom

@[reassoc] theorem perfectLocalizedPullback_representatives {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) :
    (boundedAboveFlatPerfectSpectrumIso Y).hom ≫ perfectLocalizedPullback f =
      boundedAboveFlatLocalizedPullback f ≫ (boundedAboveFlatPerfectSpectrumIso X).hom := by
  simp only [perfectLocalizedPullback, Iso.hom_inv_id_assoc]

theorem perfectLocalizedPullback_unique {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y)
    (a : perfectLocalizedSpectrum Y ⟶ perfectLocalizedSpectrum X)
    (ha : (boundedAboveFlatPerfectSpectrumIso Y).hom ≫ a =
      boundedAboveFlatLocalizedPullback f ≫ (boundedAboveFlatPerfectSpectrumIso X).hom) :
    a = perfectLocalizedPullback f := by
  apply (cancel_epi (boundedAboveFlatPerfectSpectrumIso Y).hom).mp
  exact ha.trans (perfectLocalizedPullback_representatives f).symm

@[simp] theorem perfectLocalizedPullback_id (X : Scheme.{u}) [CompactSpace X] :
    perfectLocalizedPullback (𝟙 X) = 𝟙 _ := by
  simp only [perfectLocalizedPullback, boundedAboveFlatLocalizedPullback_id, Category.id_comp,
    Iso.inv_hom_id]

@[simp] theorem perfectLocalizedPullback_comp {X Y Z : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] [CompactSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    perfectLocalizedPullback (f ≫ g) = perfectLocalizedPullback g ≫ perfectLocalizedPullback f := by
  simp only [perfectLocalizedPullback, boundedAboveFlatLocalizedPullback_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Original perfect spectra form an actual contravariant functor in the
constructed homotopy/stable localization; no strict continuous inverse is asserted. -/
def perfectLocalizedSpectrumFunctor : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤
  StableLocalization.{u+1} where
  obj X := perfectLocalizedSpectrum X.unop.obj
  map f := perfectLocalizedPullback f.unop.hom
  map_id X := perfectLocalizedPullback_id X.unop.obj
  map_comp f g := perfectLocalizedPullback_comp g.unop.hom f.unop.hom

/-- The literal bounded-flat inclusion is the forward component of an actual natural isomorphism. -/
def boundedAboveFlatPerfectSpectrumNatIso :
    AlgebraicGeometry.Scheme.quasiCompactSchemesInclusion.op ⋙
      boundedAboveFlatLocalizedSpectrumFunctor ≅
      perfectLocalizedSpectrumFunctor :=
  NatIso.ofComponents (fun X ↦ boundedAboveFlatPerfectSpectrumIso X.unop.obj)
    (fun f ↦ (perfectLocalizedPullback_representatives f.unop.hom).symm)

/-- In every nonnegative degree, the spectrum-level derived pullback is exactly
the previously defined original perfect K-map, including its K0 group law. -/
theorem perfectLocalizedPullback_originalK_naturality {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) (n : ℕ) (a : (perfectComplexesWaldhausen
      Y.toRingedSpace).K n) :
    originalKStableEquiv (perfectComplexesWaldhausen X.toRingedSpace) n (Additive.ofMul
      (perfectKPullback f n a)) =
      (localizedStableHomotopyFunctor (n : ℤ)).map (perfectLocalizedPullback f)
        (originalKStableEquiv (perfectComplexesWaldhausen Y.toRingedSpace) n (Additive.ofMul
      a)) := by
  obtain ⟨b,rfl⟩ := (boundedAboveFlatPerfectToPerfectKMap_bijective Y.toRingedSpace n).surjective a
  have hY := localizedSpectrumMap_originalK_naturality _ _
      (boundedAboveFlatPerfectInclusion_isExact Y.toRingedSpace) n b
  have hX := localizedSpectrumMap_originalK_naturality _ _
      (boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace) n
    (boundedAboveFlatPerfectKPullback f n b)
  have hF := localizedSpectrumMap_originalK_naturality _ _
      (boundedAboveFlatPerfectPullback_isExact f) n b
  have hs := congrArg ((localizedStableHomotopyFunctor (n : ℤ)).map)
    (perfectLocalizedPullback_representatives f)
  rw [Functor.map_comp,Functor.map_comp] at hs
  have hp := DFunLike.congr_fun (boundedAboveFlatPerfectToPerfectKMap_pullback f n) b
  change perfectKPullback f n (boundedAboveFlatPerfectToPerfectKMap Y.toRingedSpace n b) =
    boundedAboveFlatPerfectToPerfectKMap X.toRingedSpace n (boundedAboveFlatPerfectKPullback f
      n b) at hp
  rw [hp]
  exact hX.trans ((congrArg ((localizedStableHomotopyFunctor (n : ℤ)).map
    (boundedAboveFlatPerfectSpectrumIso X).hom) hF).trans
      ((ConcreteCategory.congr_hom hs
        (originalKStableEquiv (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) n
      (Additive.ofMul b))).symm.trans
        (congrArg ((localizedStableHomotopyFunctor (n : ℤ)).map (perfectLocalizedPullback f))
          hY.symm)))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:29"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatLocalizedSpectrum

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:33"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectLocalizedSpectrum

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:37"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatLocalizedPullback

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:41"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatLocalizedPullback_id

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:47"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatLocalizedPullback_comp

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:55"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatLocalizedSpectrumFunctor

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:62"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatPerfectSpectrumIso

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:67"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatPerfectSpectrumIso_hom

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:73"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectLocalizedPullback

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:78"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectLocalizedPullback_representatives

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:84"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectLocalizedPullback_unique

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:93"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectLocalizedPullback_id

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:98"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectLocalizedPullback_comp

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:106"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectLocalizedSpectrumFunctor

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:114"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatPerfectSpectrumNatIso

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/DerivedPullback.lean:135"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectLocalizedPullback_originalK_naturality


end AlgebraicGeometry.Scheme.Modules
