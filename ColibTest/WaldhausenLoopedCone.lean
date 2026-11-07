/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Colib.KTheory.Waldhausen.Iterated.ConeParameterLooping

/-!
Regressions for whole parameter-looped homotopies, the actual looped cone, strict naturality,
the full fiber transpose, conditional signed boundary transport, explicit linear-growth
excision and its unconditional native iterated-S specialization.
-/

open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
open scoped Topology unitInterval

universe u v

noncomputable section

section WholeHomotopy

variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} (H : Homotopy f g)

example (n : ℕ) (s t : unitInterval) (γ : Path (E.point n) (E.point n)) :
    Path.toContinuousMap (H.parameterLooping.level n (s, γ)) t = H.level n (s, γ t) :=
  H.parameterLooping_apply n s t γ

-- Homotopy time s, structure time t, and loop time r stay independent.
example (n : ℕ) (s t r : unitInterval) (γ : Path (E.point n) (E.point n)) :
    Path.toContinuousMap
        (H.parameterLooping.level (n + 1)
          (s, (parameterLooping E).structureMap n γ t)) r =
      Path.toContinuousMap
        ((parameterLooping F).structureMap n (H.parameterLooping.level n (s, γ)) t) r :=
  congrArg (fun p : Path (F.point (n + 1)) (F.point (n + 1)) ↦ p r)
    (H.parameterLooping.comm n s γ t)

example (s : unitInterval) : H.parameterLooping.at s = parameterLoopingMap (H.at s) :=
  H.parameterLooping_at s

end WholeHomotopy

section ActualComparison

variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F)

example :
    mappingConeInclusion (parameterLoopingMap f) ≫ mappingConeParameterLoopingComparison f =
      parameterLoopingMap (mappingConeInclusion f) :=
  mappingConeParameterLoopingComparison_inclusion f

example (n : ℕ) (s t : unitInterval) (γ : Path (E.point n) (E.point n)) :
    Path.toContinuousMap ((mappingConeParameterLoopingComparison f).map n
      (ReducedMappingCone.cylinder ((parameterLooping E).point n)
        ((parameterLooping F).point n) ((parameterLoopingMap f).map n) (s, γ))) t =
      ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, γ t) :=
  mappingConeParameterLoopingComparison_cylinder f n s t γ

example (g : F ⟶ G) (H : Homotopy (f ≫ g) (zeroHom E G)) :
    mappingConeParameterLoopingComparison f ≫ parameterLoopingMap (mappingConeDesc f g H) =
      mappingConeDesc (parameterLoopingMap f) (parameterLoopingMap g) H.parameterLoopingNull :=
  mappingConeParameterLoopingComparison_desc f g H

example :
    homotopyFiberLift (parameterLoopingMap (mappingConeInclusion f)) (parameterLoopingMap f)
        (mappingConeParameterLoopingHomotopy f) ≫
      (homotopyFiberParameterLoopingIso (mappingConeInclusion f)).hom =
        parameterLoopingMap (mappingConeFiberComparison f) :=
  mappingConeParameterLoopingHomotopy_fiberLift f

example (n : ℕ) (z : (homotopyFiber (parameterLoopingMap f)).space n)
    (t : unitInterval) :
    (Path.toContinuousMap ((homotopyFiberParameterLoopingIso f).hom.map n z) t).1.1 =
      Path.toContinuousMap z.1.1 t :=
  homotopyFiberParameterLoopingIso_hom_source f n z t

example (n : ℕ) (z : (homotopyFiber (parameterLoopingMap f)).space n)
    (s t : unitInterval) :
    (Path.toContinuousMap ((homotopyFiberParameterLoopingIso f).hom.map n z) t).1.2 s =
      Path.toContinuousMap (z.1.2 s) t :=
  homotopyFiberParameterLoopingIso_hom_path f n z t s

example (n : ℕ) (γ : (parameterLooping (homotopyFiber f)).space n)
    (t : unitInterval) :
    Path.toContinuousMap ((homotopyFiberParameterLoopingIso f).inv.map n γ).1.1 t =
      (Path.toContinuousMap γ t).1.1 :=
  homotopyFiberParameterLoopingIso_inv_source f n γ t

example (n : ℕ) (γ : (parameterLooping (homotopyFiber f)).space n)
    (s t : unitInterval) :
    Path.toContinuousMap (((homotopyFiberParameterLoopingIso f).inv.map n γ).1.2 s) t =
      (Path.toContinuousMap γ t).1.2 s :=
  homotopyFiberParameterLoopingIso_inv_path f n γ s t

example :
    (homotopyFiberParameterLoopingIso f).hom ≫
        parameterLoopingMap (homotopyFiberProjection f) =
      homotopyFiberProjection (parameterLoopingMap f) :=
  homotopyFiberParameterLoopingIso_hom_projection f

example {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B) :
    mappingConeMap (parameterLoopingFunctor.mapArrow.map sq) ≫
        mappingConeParameterLoopingComparison B.hom =
      mappingConeParameterLoopingComparison A.hom ≫ parameterLoopingMap (mappingConeMap sq) :=
  mappingConeParameterLoopingComparison_naturality sq

example {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B) :
    homotopyFiberMap (parameterLoopingFunctor.mapArrow.map sq) ≫
        (homotopyFiberParameterLoopingIso B.hom).hom =
      (homotopyFiberParameterLoopingIso A.hom).hom ≫ parameterLoopingMap (homotopyFiberMap sq) :=
  homotopyFiberParameterLoopingIso_hom_naturality sq

example :
    parameterLoopingFunctor.mapArrow ⋙ homotopyFiberFunctor ≅
      homotopyFiberFunctor ⋙ parameterLoopingFunctor :=
  homotopyFiberParameterLoopingNatIso

example (n : ℕ) (hc : IsClosed ({E.point n} : Set (E.space n)))
    (h : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n)))) :
    TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((parameterLooping E).point n))) :=
  parameterLooping_point_homotopyExtensionProperty E n hc h

end ActualComparison

section ConditionalStability

variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F)
  (he : IsStableEquivalence (mappingConeFiberComparison f))
  (hΩe : IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)))

example : IsStableEquivalence (mappingConeParameterLoopingComparison f) :=
  Topology.LoopPrespectrum.mappingConeParameterLoopingComparison_isStableEquivalence f he hΩe

example (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (parameterLoopingMap (mappingConeFiberComparison f))) :=
  parameterLoopingMap_isStableEquivalence (mappingConeFiberComparison f) he d

example (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (mappingConeParameterLoopingComparison f) ≫
        stableFiberConnecting (parameterLoopingMap (mappingConeInclusion f)) d =
      stableMappingConeConnecting (parameterLoopingMap f) hΩe d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (parameterLoopingMap (mappingConeInclusion f))
            (parameterLoopingMap f) (mappingConeParameterLoopingHomotopy f)) :=
  mappingConeParameterLoopingComparison_connecting f hΩe d

example (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (mappingConeParameterLoopingComparison f) ≫
        stableFiberConnecting (parameterLoopingMap (mappingConeInclusion f)) d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberParameterLoopingIso (mappingConeInclusion f)).hom ≫
        (parameterStableHomotopyIso (homotopyFiber (mappingConeInclusion f)) d).hom =
      stableMappingConeConnecting (parameterLoopingMap f) hΩe d ≫
        (parameterStableHomotopyIso E d).hom ≫
        (stableHomotopyFunctor (d + 1)).map (mappingConeFiberComparison f) :=
  mappingConeParameterLoopingComparison_connecting_shift f hΩe d

example (g : F ⟶ G) (H : Homotopy (f ≫ g) (zeroHom E G))
    (hdesc : IsStableEquivalence (mappingConeDesc f g H)) :
    IsStableEquivalence
      (mappingConeDesc (parameterLoopingMap f) (parameterLoopingMap g) H.parameterLoopingNull) :=
  mappingConeDesc_parameterLooping_isStableEquivalence f g H he hΩe hdesc

end ConditionalStability

section LinearGrowth

variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (c : ℕ)
  [∀ m, T1Space (E.space m)] [∀ m, T1Space (F.space m)]
  (hE : ∀ m, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point m))))
  (hF : ∀ m, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point m))))
  (hπE : ∀ n x k, k < n + 2 →
    Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
  (hπF : ∀ n x k, k < n + 2 →
    Subsingleton (HomotopyGroup.Pi k (F.space (n + c + 2)) x))

example (n : ℕ) :
    IsHomotopyConnectedMap ((mappingConeFiberComparison f).map (n + c + 2)) (2 * n + 2) :=
  mappingConeFiberComparison_isHomotopyConnectedMap_of_linearGrowth f c n
    (hE _) (hF _) (hπE n) (hπF n)

example : IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)) :=
  parameterLoopingMap_coneFiber_isStableEquivalence_of_linearGrowth f c hE hF hπE hπF

example : IsStableEquivalence (mappingConeParameterLoopingComparison f) :=
  mappingConeParameterLoopingComparison_isStableEquivalence_of_linearGrowth f c hE hF hπE hπF

end LinearGrowth

section ActualIteratedS

variable {W V : WideSubcategory preservesZero.{u}} (f : prespectrum W ⟶ prespectrum V)

example : IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)) :=
  CategoryTheory.Waldhausen.IteratedS.parameterLoopingMap_coneFiber_isStableEquivalence f

example : IsStableEquivalence (mappingConeParameterLoopingComparison f) :=
  CategoryTheory.Waldhausen.IteratedS.mappingConeParameterLoopingComparison_isStableEquivalence f

example (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (mappingConeParameterLoopingComparison f)) :=
  CategoryTheory.Waldhausen.IteratedS.mappingConeParameterLoopingComparison_isStableEquivalence f d

-- The signed boundary needs no excision hypothesis for these actual S-models.
example (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (mappingConeParameterLoopingComparison f) ≫
        stableFiberConnecting (parameterLoopingMap (mappingConeInclusion f)) d =
      stableMappingConeConnecting (parameterLoopingMap f)
          (CategoryTheory.Waldhausen.IteratedS.parameterLoopingMap_coneFiber_isStableEquivalence f)
          d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (parameterLoopingMap (mappingConeInclusion f))
            (parameterLoopingMap f) (mappingConeParameterLoopingHomotopy f)) :=
  mappingConeParameterLoopingComparison_connecting f
    (CategoryTheory.Waldhausen.IteratedS.parameterLoopingMap_coneFiber_isStableEquivalence f) d

end ActualIteratedS

-- The existing native AsSmall realization also retains its independent object/hom universes.
example {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) (f : originalPrespectrum W ⟶ originalPrespectrum V) :
    IsStableEquivalence (mappingConeParameterLoopingComparison f) :=
  CategoryTheory.Waldhausen.IteratedS.mappingConeParameterLoopingComparison_isStableEquivalence f
