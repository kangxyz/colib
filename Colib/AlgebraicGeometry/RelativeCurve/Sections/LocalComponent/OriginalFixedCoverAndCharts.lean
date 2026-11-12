/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.OriginalCompactifiedFixedFullBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleCurveOriginalCover
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualRetainedAffineChart

/-! # One original cover and one scalar map for both actual chart coordinates

The retained source is precisely the nested source already selected by the
fixed-target construction. The independent etale chart remains a separate
pullback of its original open. Only the ring presentation of the actual base
map is selected; the cover, clopen and retained source are not selected again.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Produce the finite cover, original retained coordinate and independent etale
coordinate on precisely the clopen selected by the fixed-section construction. -/
theorem exists_original_fixed_cover_and_charts
    {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    (s : GeometricPoint X.left) {C N Y YN E : Scheme.{u}} (p : C ⟶ X.left)
    {A : Type u} [CommRing A] (v : C ⟶ N) (q : N ⟶ Spec (.of A))
    (b : X.left ⟶ Spec (.of A)) (h : IsPullback v p q b)
    (j : Y ⟶ C) (jN : YN ⟶ N) (y : Y ⟶ YN) (hY : IsPullback j y v jN)
    (π : N ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = q)
    (aY : YN ⟶ Spec (.of (Polynomial A)))
    (haY : aY ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = jN ≫ q)
    (hjN : jN ≫ π = aY ≫ projectiveLineXChart A)
    (eChart : E ⟶ N) (aE : E ⟶ Spec (.of (Polynomial A))) [Etale aE]
    (haE : aE ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = eChart ≫ q)
    (heChart : eChart ≫ π = aE ≫ projectiveLineXChart A)
    {i₀ i : SmallEtaleNeighborhood X s} (e : i ⟶ i₀) (a : Over i)
    (U : ((etaleCurveDiagram X s p).obj a.left).Opens) [IsClosedImmersion U.ι] :
    let R := ((smallEtaleNeighborhoodInclusion X s).obj a.left).obj.left.unop
    let F := (etaleCurveDiagram X s p).map (a.hom ≫ e)
    let j₀ := etaleCurveOriginalRetainedStageMap X s p j i₀
    let V := pullback U.ι (pullback.fst F j₀)
    let jV := pullback.fst U.ι (pullback.fst F j₀)
    let vY := pullback.snd U.ι (pullback.fst F j₀) ≫ pullback.snd F j₀ ≫
      pullback.snd ((smallEtaleNeighborhoodOver X s).obj i₀).hom (j ≫ p)
    let vStage := pullback.snd ((smallEtaleNeighborhoodOver X s).obj a.left).hom p ≫ v
    let qStage := (etaleCurveStructure X s p).app a.left
    ∃ (φ : A →+* R)
      (_hφ : Spec.map (CommRingCat.ofHom φ) =
        ((smallEtaleNeighborhoodOver X s).obj a.left).hom ≫ b)
      (hpb : IsPullback vStage qStage q (Spec.map (CommRingCat.ofHom φ))),
      let πU := U.ι ≫ projectiveLineCoverOfActualCartesian q φ vStage qStage hpb π hπ
      IsFinite πU ∧ πU ≫ (projectiveLine R ↘ Spec (.of R)) = U.ι ≫ qStage ∧
      ∃ (cV : V ⟶ Spec (.of (Polynomial R)))
        (cE : pullback (U.ι ≫ vStage) eChart ⟶ Spec (.of (Polynomial R))),
        cV ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
          jV ≫ (U.ι ≫ qStage) ∧
        cV ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)) = (vY ≫ y) ≫ aY ∧
        jV ≫ πU = cV ≫ projectiveLineXChart R ∧
        Etale cE ∧
        cE ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
          pullback.fst (U.ι ≫ vStage) eChart ≫ (U.ι ≫ qStage) ∧
        cE ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)) =
          pullback.snd (U.ι ≫ vStage) eChart ≫ aE ∧
        pullback.fst (U.ι ≫ vStage) eChart ≫ πU = cE ≫ projectiveLineXChart R := by
  intro R F j₀ V jV vY vStage qStage
  let hUOpen : IsOpenImmersion U.ι :=
    IsOpenImmersion.ofRestrict ((etaleCurveDiagram X s p).obj a.left) U.isOpenEmbedding
  have hVold := originalCompactified_fixedClopen_retained_isPullback X s p j e a U
  have hVpaste := hVold.paste_vert hY
  let pr₀ := pullback.snd ((smallEtaleNeighborhoodOver X s).obj i₀).hom p
  let pr := pullback.snd ((smallEtaleNeighborhoodOver X s).obj a.left).hom p
  have hproj : F ≫ pr₀ = pr := pullback.lift_snd _ _ _
  have hright : (U.ι ≫ F ≫ pr₀) ≫ v = U.ι ≫ vStage :=
    ((congrArg (fun z : U.toScheme ⟶ C => z ≫ v) (Category.assoc U.ι F pr₀).symm).trans
      (Category.assoc (U.ι ≫ F) pr₀ v)).trans
      ((Category.assoc U.ι F (pr₀ ≫ v)).trans
      ((congrArg (fun z => U.ι ≫ z) (Category.assoc F pr₀ v).symm).trans
        (congrArg (fun z : ((etaleCurveDiagram X s p).obj a.left) ⟶ C =>
          U.ι ≫ (z ≫ v)) hproj)))
  have hV : IsPullback jV (vY ≫ y) (U.ι ≫ vStage) jN :=
    (congrArg (fun z : U.toScheme ⟶ N => IsPullback jV (vY ≫ y) z jN) hright).mp hVpaste
  obtain ⟨φ, hφ, hpb, hfinite, hstructure⟩ :=
    exists_etaleCurve_clopen_original_cover X s p v q b h a.left U π hπ
  let cV : V ⟶ Spec (.of (Polynomial R)) :=
    affineChartOfActualRetained q φ vStage qStage hpb U.ι jN aY haY jV (vY ≫ y) hV
  let cE : pullback (U.ι ≫ vStage) eChart ⟶ Spec (.of (Polynomial R)) :=
    affineChartOfActualClopen q φ vStage qStage hpb U.ι eChart aE haE
  refine ⟨φ, hφ, hpb, hfinite, hstructure, cV, cE, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact affineChartOfActualRetained_structure q φ vStage qStage hpb U.ι
      jN aY haY jV (vY ≫ y) hV
  · exact affineChartOfActualRetained_map q φ vStage qStage hpb U.ι
      jN aY haY jV (vY ≫ y) hV
  · exact affineChartOfActualRetained_cover q φ vStage qStage hpb U.ι
      jN aY haY jV (vY ≫ y) hV π hπ hjN
  · exact @affineChartOfActualClopen_etale A R _ _ N
      ((etaleCurveDiagram X s p).obj a.left) U.toScheme E
      q φ vStage qStage hpb U.ι eChart aE haE hUOpen inferInstance
  · exact affineChartOfActualClopen_structure q φ vStage qStage hpb U.ι eChart aE haE
  · exact affineChartOfActualClopen_map q φ vStage qStage hpb U.ι eChart aE haE
  · exact affineChartOfActualClopen_cover q φ vStage qStage hpb U.ι eChart aE haE π hπ heChart

end AlgebraicGeometry.Scheme.SmoothSite
