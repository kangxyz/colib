/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.CoherentPrincipalClosedComparison
public import Colib.AlgebraicGeometry.KTheory.CoherentAffineSupportedComparison

/-!
# Actual principal closed direct image into supported coherent G-theory

The literal coherent direct image lands in the kernel of the actual principal
localization pullback. The chosen small-model lift retains that functor.

Implementation source: `Quillen/AlgebraicGeometry/Scheme/Coherent/ClosedImmersion/Devissage.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.Coherent.PrincipalClosed
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

/-- The original principal closed immersion. -/
abbrev immersion := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))

/-- The actual closed direct image vanishes after principal localization. -/
theorem pushforward_localization_isZero
    (M : SheafOfModules.CoherentModules
      (Spec (CommRingCat.of (FGModuleCat.ClosedRing f))).ringCatSheaf) :
    IsZero ((affineLocalizationExact (Submonoid.powers f)).toFunctor.obj
      ((closedPushforwardExact (immersion R f)).toFunctor.obj M)) := by
  let J := affineGlobalSections (CommRingCat.of (Localization (Submonoid.powers f)))
  let : J.IsEquivalence := affineGlobalSections_isEquivalence _
  apply IsZero.of_full_of_faithful_of_isZero J
  let N := (affineGlobalSections (CommRingCat.of (FGModuleCat.ClosedRing f))).obj M
  have hz : IsZero ((FGModuleCat.localizedModuleFunctor (Submonoid.powers f)).obj
      ((FGModuleCat.closedRestriction f).obj N)) := by
    change (FGModuleCat.localizedModuleFunctor (Submonoid.powers f)).kernel _
    rw [FGModuleCat.localizedModuleFunctor_kernel]
    intro m
    refine ⟨⟨f, ⟨1, pow_one f⟩⟩, ?_⟩
    exact FGModuleCat.closedRestriction_killed f N m
  let e := (closedPushforwardGlobalSectionsIso
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)).app M
  have he := hz.of_iso ((FGModuleCat.localizedModuleFunctor (Submonoid.powers f)).mapIso e)
  exact he.of_iso ((coherentLocalizationGlobalSectionsIso (Submonoid.powers f)).app
    ((closedPushforwardExact (immersion R f)).toFunctor.obj M))

/-- The actual upper-universe small closed pushforward lands in the true kernel. -/
theorem smallPushforward_supported
    (M : SmallModel.{u + 1} (SheafOfModules.CoherentModules
      (Spec (CommRingCat.of (FGModuleCat.ClosedRing f))).ringCatSheaf)) :
    SmallModelGLocalization.supported.{u + 1} (affineLocalizationExact (Submonoid.powers f))
      ((closedPushforwardExact (immersion R f)).smallModel.{u + 1}.toFunctor.obj M) := by
  apply ((affineLocalizationExact (Submonoid.powers f)).smallModel_kernel_iff.{u + 1} _).2
  have h := pushforward_localization_isZero R f
    ((equivSmallModel.{u + 1} _).inverse.obj M)
  exact h.of_iso ((affineLocalizationExact (Submonoid.powers f)).toFunctor.mapIso
    ((equivSmallModel.{u + 1} _).unitIso.app
      ((closedPushforwardExact (immersion R f)).toFunctor.obj
        ((equivSmallModel.{u + 1} _).inverse.obj M)))).symm

/-- The literal small-model pushforward, factored through the actual supported category. -/
def smallPushforwardToSupport :
    SmallModel.{u + 1} (SheafOfModules.CoherentModules
      (Spec (CommRingCat.of (FGModuleCat.ClosedRing f))).ringCatSheaf) ⥤
    (SmallModelGLocalization.supported.{u + 1}
      (affineLocalizationExact (Submonoid.powers f))).FullSubcategory :=
  ObjectProperty.lift _ (closedPushforwardExact (immersion R f)).smallModel.{u + 1}.toFunctor
    (smallPushforward_supported R f)

instance smallPushforwardToSupport_additive : (smallPushforwardToSupport R f).Additive := by
  unfold smallPushforwardToSupport
  infer_instance

/-- Actual closed direct image with its original supported exact structure. -/
def smallPushforwardToSupportExact :
    ExactFunctor (coherentExactStructure
      (Spec (CommRingCat.of (FGModuleCat.ClosedRing f)))).smallModel.{u + 1}
    (abelianExactStructure (SmallModelGLocalization.supported.{u + 1}
      (affineLocalizationExact (Submonoid.powers f))).FullSubcategory) where
  toFunctor := smallPushforwardToSupport R f
  map_conflation T hT := by
    have h := ((closedPushforwardExact (immersion R f)).smallModel.{u + 1}.comp
      (CategoryTheory.SmallModel.abelianExactComparison.{u + 1}
        (SheafOfModules.CoherentModules (Spec R).ringCatSheaf))).map_conflation T hT
    exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (SmallModelGLocalization.supported.{u + 1}
        (affineLocalizationExact (Submonoid.powers f))).ι h

private def publicGlobalSectionsExact (T : CommRingCat.{u}) [IsNoetherianRing T] :
    ExactFunctor (coherentExactStructure (Spec T)).smallModel.{u + 1}
      (abelianExactStructure (FGModuleCat.{u} T)).smallModel.{u} :=
  ((coherentExactStructure (Spec T)).smallModelUniverseComparison.{u + 1, u}).comp
    (affineGlobalSectionsExact T).smallModel.{u}

private def supportedLowerRoute :=
  ((publicGlobalSectionsExact (CommRingCat.of (FGModuleCat.ClosedRing f))).comp
    (FGModuleCat.Localization.smallClosedToSupportExact.{u,u} f)).comp
      (SmallModelBoundaryNaturality.Universe.supportExact.{u, u + 1}
        (FGModuleCat.localizationExactFunctor.{u,u} (Submonoid.powers f)))

private def supportedUpperRoute :=
  (smallPushforwardToSupportExact R f).comp
    (upperSupportedGlobalSectionsExact (Submonoid.powers f))

private def modelRoundTripIso :
    (SmallModelBoundaryNaturality.Universe.standardComparison.{u + 1, u}
      (FGModuleCat.{u} R)).toFunctor ⋙
    (SmallModelBoundaryNaturality.Universe.standardComparison.{u, u + 1}
      (FGModuleCat.{u} R)).toFunctor ≅ 𝟭 (SmallModel.{u + 1} (FGModuleCat.{u} R)) :=
  Functor.isoWhiskerLeft (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).inverse
    (Functor.isoWhiskerRight (equivSmallModel.{u} (FGModuleCat.{u} R)).unitIso.symm
      (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).functor) ≪≫
    Functor.isoWhiskerLeft (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).inverse
      (Functor.leftUnitor (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).functor) ≪≫
        (equivSmallModel.{u + 1} (FGModuleCat.{u} R)).counitIso

private theorem smallKUniverseEquiv_roundTrip (n : ℕ) :
    ((abelianExactStructure (FGModuleCat.{u} R)).smallKUniverseEquiv.{u, u + 1} n).toMonoidHom.comp
      ((abelianExactStructure (FGModuleCat.{u} R)).smallKUniverseEquiv.{u + 1, u} n).toMonoidHom =
    MonoidHom.id _ := by
  let E := abelianExactStructure (FGModuleCat.{u} R)
  change ((E.smallModelUniverseComparison.{u, u + 1}).universalKMap n).comp
    ((E.smallModelUniverseComparison.{u + 1, u}).universalKMap n) = _
  rw [← ExactFunctor.universalKMap_comp]
  have h := ExactFunctor.universalKMap_eq_of_natIso
    (F := ((abelianExactStructure (FGModuleCat.{u} R)).smallModelUniverseComparison.{u + 1, u}).comp
      ((abelianExactStructure (FGModuleCat.{u} R)).smallModelUniverseComparison.{u, u + 1}))
    (G := ExactFunctor.id (abelianExactStructure (FGModuleCat.{u} R)).smallModel.{u + 1})
    (modelRoundTripIso R) n
  rw [ExactFunctor.universalKMap_eq_KMap
    (ExactFunctor.id (abelianExactStructure (FGModuleCat.{u} R)).smallModel.{u + 1}),
    ExactFunctor.KMap_id] at h
  exact h

/-- Public affine comparison promoted upward is the actual upper global-sections map. -/
theorem publicGlobalSections_up (T : CommRingCat.{u}) [IsNoetherianRing T] (n : ℕ)
    (a : Scheme.G (Spec T) n) :
    (abelianExactStructure (FGModuleCat.{u} T)).smallKUniverseEquiv.{u, u + 1} n
      (publicSpecGRingEquiv T n a) = (affineGlobalSectionsExact T).smallKMap.{u + 1} n a := by
  have hn := DFunLike.congr_fun
    (ExactFunctor.smallKUniverseEquiv_naturality.{u + 1, u} (affineGlobalSectionsExact T) n) a
  have hs := DFunLike.congr_fun (publicSpecGRingEquiv_toMonoidHom T n) a
  change publicSpecGRingEquiv T n a =
    (affineGlobalSectionsExact T).smallKMap.{u} n
      ((coherentExactStructure (Spec T)).smallKUniverseEquiv.{u + 1, u} n a) at hs
  change (affineGlobalSectionsExact T).smallKMap.{u} n
      ((coherentExactStructure (Spec T)).smallKUniverseEquiv.{u + 1, u} n a) =
    (abelianExactStructure (FGModuleCat.{u} T)).smallKUniverseEquiv.{u + 1, u} n
      ((affineGlobalSectionsExact T).smallKMap.{u + 1} n a) at hn
  rw [hs, hn]
  exact DFunLike.congr_fun (smallKUniverseEquiv_roundTrip T n)
    ((affineGlobalSectionsExact T).smallKMap.{u + 1} n a)

private def supportedGlobalSectionsIso :
    (supportedLowerRoute R f).toFunctor ≅ (supportedUpperRoute R f).toFunctor := by
  apply Functor.fullyFaithfulCancelRight
    (SmallModelGLocalization.supported.{u + 1}
      (FGModuleCat.localizationExactFunctor.{u,u} (Submonoid.powers f))).ι
  let H := (closedPushforwardExact (immersion R f)).comp (affineGlobalSectionsExact R)
  let Cmp := (coherentExactStructure
    (Spec (CommRingCat.of (FGModuleCat.ClosedRing f)))).smallModelUniverseComparison.{u + 1, u}
  let U := (abelianExactStructure (FGModuleCat.{u} R)).smallModelUniverseComparison.{u, u + 1}
  let e := closedPushforwardGlobalSectionsIso
    (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft Cmp.toFunctor
        ((ExactFunctor.smallModelCompIso.{u}
          (affineGlobalSectionsExact (CommRingCat.of (FGModuleCat.ClosedRing f)))
          (FGModuleCat.closedRestrictionExact f)).symm ≪≫
          ExactFunctor.smallModelNatIso.{u} e.symm)) U.toFunctor ≪≫
    Functor.isoWhiskerRight
      (ExactFunctor.smallModelUniverseComparisonNaturalityIso.{u + 1, u} H) U.toFunctor ≪≫
    Functor.isoWhiskerLeft H.smallModel.{u + 1}.toFunctor (modelRoundTripIso R) ≪≫
    Functor.rightUnitor H.smallModel.{u + 1}.toFunctor ≪≫
      ExactFunctor.smallModelCompIso.{u + 1}
        (closedPushforwardExact (immersion R f)) (affineGlobalSectionsExact R)

private theorem publicGlobalSectionsExact_universalKMap (T : CommRingCat.{u})
    [IsNoetherianRing T] (n : ℕ) :
    (publicGlobalSectionsExact T).universalKMap n = (publicSpecGRingEquiv T n).toMonoidHom := by
  rw [publicSpecGRingEquiv_toMonoidHom]
  unfold publicGlobalSectionsExact
  rw [ExactFunctor.universalKMap_comp,
    ExactFunctor.universalKMap_eq_KMap (affineGlobalSectionsExact T).smallModel.{u}]
  rfl

set_option maxHeartbeats 1000000 in
-- The routes include two exact model comparisons and both native coherent and module categories.
private theorem supportedGlobalSectionsKMap (n : ℕ)
    (a : Scheme.G (Spec (CommRingCat.of (FGModuleCat.ClosedRing f))) n) :
    (SmallModelBoundaryNaturality.Universe.supportExact.{u, u + 1}
      (FGModuleCat.localizationExactFunctor.{u,u} (Submonoid.powers f))).universalKMap n
        (FGModuleCat.Localization.closedSupportGEquiv.{u,u} f n
          (publicSpecGRingEquiv (CommRingCat.of (FGModuleCat.ClosedRing f)) n a)) =
    (upperSupportedGlobalSectionsExact (Submonoid.powers f)).KMap n
      ((smallPushforwardToSupportExact R f).KMap n a) := by
  let A := publicGlobalSectionsExact (CommRingCat.of (FGModuleCat.ClosedRing f))
  let B := FGModuleCat.Localization.smallClosedToSupportExact.{u,u} f
  let C := SmallModelBoundaryNaturality.Universe.supportExact.{u, u + 1}
    (FGModuleCat.localizationExactFunctor.{u,u} (Submonoid.powers f))
  let D := smallPushforwardToSupportExact R f
  let E := upperSupportedGlobalSectionsExact (Submonoid.powers f)
  have h := ExactFunctor.universalKMap_eq_of_natIso (supportedGlobalSectionsIso R f) n
  have hL : (supportedLowerRoute R f).universalKMap n =
      (C.universalKMap n).comp ((B.KMap n).comp (A.universalKMap n)) :=
    (ExactFunctor.universalKMap_comp (A.comp B) C n).trans
      (congrArg (fun k => (C.universalKMap n).comp k)
        ((ExactFunctor.universalKMap_comp A B n).trans
          (congrArg (fun k => k.comp (A.universalKMap n))
            (ExactFunctor.universalKMap_eq_KMap B n))))
  have hR : (supportedUpperRoute R f).universalKMap n = (E.KMap n).comp (D.KMap n) :=
    (ExactFunctor.universalKMap_comp D E n).trans
      ((congrArg (fun k => k.comp (D.universalKMap n))
        (ExactFunctor.universalKMap_eq_KMap E n)).trans
        (congrArg (fun k => (E.KMap n).comp k) (ExactFunctor.universalKMap_eq_KMap D n)))
  have hm := DFunLike.congr_fun (hL.symm.trans (h.trans hR)) a
  have hp := DFunLike.congr_fun
    (publicGlobalSectionsExact_universalKMap (CommRingCat.of (FGModuleCat.ClosedRing f)) n) a
  have hl := DFunLike.congr_fun (FGModuleCat.Localization.closedSupportGEquiv_coe f n)
    (publicSpecGRingEquiv (CommRingCat.of (FGModuleCat.ClosedRing f)) n a)
  change FGModuleCat.Localization.closedSupportGEquiv f n
      (publicSpecGRingEquiv (CommRingCat.of (FGModuleCat.ClosedRing f)) n a) =
    B.KMap n (publicSpecGRingEquiv (CommRingCat.of (FGModuleCat.ClosedRing f)) n a) at hl
  exact (congrArg (C.universalKMap n) hl).trans
    ((congrArg (fun x => C.universalKMap n (B.KMap n x)) hp.symm).trans hm)

/-- The closed-support equivalence, with the actual pushforward identified below. -/
def closedSupportGEquiv (n : ℕ) :
    Scheme.G (Spec (CommRingCat.of (FGModuleCat.ClosedRing f))) n ≃*
      SmallModelGLocalization.SupportedK.{u + 1}
        (affineLocalizationExact (Submonoid.powers f)) n :=
  (((publicSpecGRingEquiv (CommRingCat.of (FGModuleCat.ClosedRing f)) n).trans
    (FGModuleCat.Localization.closedSupportGEquiv.{u,u} f n)).trans
      (ExactFunctor.universalKEquivOfMapQIsEquivalence
        (SmallModelBoundaryNaturality.Universe.supportExact.{u, u + 1}
          (FGModuleCat.localizationExactFunctor.{u,u} (Submonoid.powers f))) n)).trans
    (upperSupportedGlobalSectionsKEquiv (Submonoid.powers f) n).symm

/-- The equivalence is precisely the original actual closed-to-support K-map. -/
theorem closedSupportGEquiv_toMonoidHom (n : ℕ) :
    (closedSupportGEquiv R f n).toMonoidHom =
      (smallPushforwardToSupportExact R f).KMap n := by
  ext a
  apply (upperSupportedGlobalSectionsKEquiv (Submonoid.powers f) n).injective
  change upperSupportedGlobalSectionsKEquiv (Submonoid.powers f) n
    ((upperSupportedGlobalSectionsKEquiv (Submonoid.powers f) n).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  exact supportedGlobalSectionsKMap R f n a

/-- The original closed-support equivalence commutes with supported global sections. -/
theorem closedSupportGEquiv_globalSections (n : ℕ)
    (a : Scheme.G (Spec (CommRingCat.of (FGModuleCat.ClosedRing f))) n) :
    (SmallModelBoundaryNaturality.Universe.supportExact.{u, u + 1}
      (FGModuleCat.localizationExactFunctor.{u,u} (Submonoid.powers f))).universalKMap n
        (FGModuleCat.Localization.closedSupportGEquiv.{u,u} f n
          (publicSpecGRingEquiv (CommRingCat.of (FGModuleCat.ClosedRing f)) n a)) =
    (upperSupportedGlobalSectionsExact (Submonoid.powers f)).KMap n
      (closedSupportGEquiv R f n a) := by
  have h := DFunLike.congr_fun (closedSupportGEquiv_toMonoidHom R f n) a
  change closedSupportGEquiv R f n a = (smallPushforwardToSupportExact R f).KMap n a at h
  exact (supportedGlobalSectionsKMap R f n a).trans
    (congrArg ((upperSupportedGlobalSectionsExact (Submonoid.powers f)).KMap n) h.symm)

/-- Supported inclusion recovers the original geometric direct-image map. -/
theorem closedSupportGEquiv_pushforward (n : ℕ) :
    (SmallModelGLocalization.inclusionKMap.{u + 1}
      (affineLocalizationExact (Submonoid.powers f)) n).comp
        (closedSupportGEquiv R f n).toMonoidHom =
    Scheme.closedPushforwardG (immersion R f) n := by
  rw [closedSupportGEquiv_toMonoidHom]
  have hi : (smallPushforwardToSupportExact R f).comp
      (ObjectProperty.exactInclusion (SmallModelGLocalization.supported.{u + 1}
        (affineLocalizationExact (Submonoid.powers f)))) =
    (closedPushforwardExact (immersion R f)).smallModel.{u + 1}.comp
      (CategoryTheory.SmallModel.abelianExactComparison.{u + 1}
        (SheafOfModules.CoherentModules (Spec R).ringCatSheaf)) := rfl
  have hk := congrArg (fun H => H.KMap n) hi
  simp only [ExactFunctor.KMap_comp] at hk
  ext x
  apply (SmallModelLocalization.standardKEquiv.{u + 1}
    (SheafOfModules.CoherentModules (Spec R).ringCatSheaf) n).injective
  change SmallModelLocalization.standardKEquiv _ n
    ((SmallModelLocalization.standardKEquiv _ n).symm
      (Abelian.Devissage.KMap _ n ((smallPushforwardToSupportExact R f).KMap n x))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun hk x

end AlgebraicGeometry.Scheme.Modules.Coherent.PrincipalClosed
