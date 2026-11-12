/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ProjectiveLine
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.PolynomialGeometry

/-!
# The full boundary meets every fiber of the original strict-local component

Transport the original finite projective-line cover and its coordinate maps. Flatness implies
that a nonempty original etale chart meets every actual component of the base-changed normal
curve. The same component is therefore surjective over the projective line, and its actual
full retained boundary is surjective over the local base. This is stronger than mere finiteness
of the boundary and does not infer nonemptiness from finiteness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- After a flat affine base change to a domain, the full retained boundary meets every base
fiber on the same actual component. Normality and local Noetherianity are stated on this
arbitrary base change; the strict-henselization specialization below supplies both internally. -/
theorem surjective_baseChanged_normalComponentBoundary_of_etale_chart
    {A R : Type u} [CommRing A] [CommRing R] [IsDomain R]
    {X Y E D : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of A)) (g : Spec (.of R) ⟶ Spec (.of A)) [Flat g]
    [IsLocallyNoetherian (pullback p g)] [IsNormal (pullback p g)]
    (π : X ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A)
    (e : E ⟶ X) [IsOpenImmersion e] [Nonempty E]
    (c : E ⟶ Spec (.of (Polynomial A))) [Etale c]
    (hc : c ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = e ≫ p)
    (he : e ≫ π = c ≫ projectiveLineXChart A)
    (b : D ⟶ X) (hb : Set.range b = (Set.range j)ᶜ) (x : (pullback p g : Scheme.{u})) :
    Surjective (pullback.fst (normalComponentOpen x).ι (pullback.fst (pullback.fst p g) b) ≫
      (normalComponentOpen x).ι ≫ pullback.snd p g) := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective g
  let g := Spec.map f
  let U := normalComponentOpen x
  have hn : Nonempty (pullback (U.ι ≫ pullback.fst p g) e : Scheme.{u}) :=
    nonempty_pullback_normalComponent_chart_of_flat (pullback.fst p g) e x
  have : Nonempty (pullback U.ι (pullback.fst (pullback.fst p g) e) : Scheme.{u}) :=
    hn.map (pullbackRightPullbackFstIso (pullback.fst p g) e U.ι).inv
  have hb' : Set.range (pullback.fst (pullback.fst p g) b) =
      (Set.range (pullback.fst (pullback.fst p g) j))ᶜ := by
    rw [Pullback.range_fst, Pullback.range_fst, hb]
    rfl
  exact surjective_normalComponentBoundary_of_nonempty_etale_chart R
    (pullback.snd p g) (pullback.fst (pullback.fst p g) j)
    (affineLineChartBaseChange p f.hom j a ha) (projectiveLineCoverBaseChange p f.hom π hπ)
    (projectiveLineCoverBaseChange_structure p f.hom π hπ)
    (affineLineChartBaseChange_comp_XChart p f.hom π hπ j a ha hj)
    (pullback.fst (pullback.fst p g) e) (affineLineChartBaseChange p f.hom e c hc)
    (affineLineChartBaseChange_comp_XChart p f.hom π hπ e c hc he)
    (pullback.fst (pullback.fst p g) b) hb' x

/-- The actual strict-local component supplied by the section construction has a surjective
full boundary. The input `U` is identified with that same native irreducible component; no new
component or compactification is chosen. The original finite projective-line cover, retained
coordinate map and nonempty etale coordinate chart are preserved through the base change. -/
theorem surjective_strictLocal_componentBoundary_of_etale_chart
    {A : Type u} [CommRing A] (B : BigEtaleSite.{u})
    (hA : B.Contains (Spec (.of A))) (s : GeometricPoint (Spec (.of A)))
    (hreg : IsRegular (Spec (.of A)))
    {X Y E D : Scheme.{u}} [IsNormal X] [IsIntegral X]
    (p : X ⟶ Spec (.of A)) [IsProper p]
    (π : X ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A)
    (e : E ⟶ X) [IsOpenImmersion e] [Nonempty E]
    (c : E ⟶ Spec (.of (Polynomial A))) [Etale c]
    (hc : c ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = e ≫ p)
    (he : e ≫ π = c ≫ projectiveLineXChart A)
    (b : D ⟶ X) (hb : Set.range b = (Set.range j)ᶜ)
    (x : (pullback p (strictHenselizationToBase B (Spec (.of A)) hA s) : Scheme.{u}))
    (U : (pullback p (strictHenselizationToBase B (Spec (.of A)) hA s) : Scheme.{u}).Opens)
    (hU : (U : Set (pullback p (strictHenselizationToBase B (Spec (.of A)) hA s) : Scheme.{u})) =
      _root_.irreducibleComponent x) :
    Surjective (pullback.fst U.ι
      (pullback.fst (pullback.fst p (strictHenselizationToBase B (Spec (.of A)) hA s)) b) ≫
        U.ι ≫ pullback.snd p (strictHenselizationToBase B (Spec (.of A)) hA s)) := by
  have := isLocallyNoetherian_of_isRegular hreg
  have := isNormal_pullback_strictHenselizationToBase B hA s p
  have := isLocallyNoetherian_pullback_strictHenselizationToBase B hA s p
  have := isRegularLocalRing_etaleLocalRing_of_isRegular B (Spec (.of A)) hA s hreg
  have : IsDomain ↥(etaleLocalRing B (Spec (.of A)) hA s) := IsRegularLocalRing.isDomain _
  have := flat_strictHenselizationToBase B (Spec (.of A)) hA s
  have hU' : U = normalComponentOpen x := SetLike.coe_injective hU
  subst U
  exact surjective_baseChanged_normalComponentBoundary_of_etale_chart p
    (strictHenselizationToBase B (Spec (.of A)) hA s) π hπ j a ha hj e c hc he b hb x

/-- Assemble the actual strict-local integral component with both original sections, affine
smooth retained open, full finite surjective boundary, and integral Noetherian polynomial
cylinder. The normal proper compactification and nonempty etale coordinate chart are the
original ones; no property of the sought component or its boundary is an input. -/
theorem exists_integral_strictLocal_component_with_surjective_boundary
    {A : Type u} [CommRing A] (B : BigEtaleSite.{u})
    (hA : B.Contains (Spec (.of A))) (s : GeometricPoint (Spec (.of A)))
    (hreg : IsRegular (Spec (.of A)))
    {X Y E D : Scheme.{u}} [IsNormal X] [IsIntegral X] [IsAffine Y]
    (p : X ⟶ Spec (.of A)) [IsProper p]
    (π : X ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (j : Y ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ p)]
    (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A)
    (e : E ⟶ X) [IsOpenImmersion e] [Nonempty E]
    (c : E ⟶ Spec (.of (Polynomial A))) [Etale c]
    (hc : c ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = e ≫ p)
    (he : e ≫ π = c ≫ projectiveLineXChart A)
    (b : D ⟶ X) [IsClosedImmersion b] [IsFinite (b ≫ p)]
    (hb : Set.range b = (Set.range j)ᶜ)
    (s₀ s₁ : strictHenselization B (Spec (.of A)) hA s ⟶
      pullback (pullback.fst p (strictHenselizationToBase B (Spec (.of A)) hA s)) j)
    (h₀ : s₀ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B (Spec (.of A)) hA s)) j ≫
      pullback.snd p (strictHenselizationToBase B (Spec (.of A)) hA s) = 𝟙 _)
    (h₁ : s₁ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B (Spec (.of A)) hA s)) j ≫
      pullback.snd p (strictHenselizationToBase B (Spec (.of A)) hA s) = 𝟙 _)
    (hs : (s₀ ≫ pullback.fst (pullback.fst p
        (strictHenselizationToBase B (Spec (.of A)) hA s)) j)
        (IsLocalRing.closedPoint ↥(etaleLocalRing B (Spec (.of A)) hA s)) =
      (s₁ ≫ pullback.fst (pullback.fst p
        (strictHenselizationToBase B (Spec (.of A)) hA s)) j)
        (IsLocalRing.closedPoint ↥(etaleLocalRing B (Spec (.of A)) hA s))) :
    let g := strictHenselizationToBase B (Spec (.of A)) hA s
    let j' := pullback.fst (pullback.fst p g) j
    let b' := pullback.fst (pullback.fst p g) b
    let p' := pullback.snd p g
    ∃ (U : (pullback p g : Scheme.{u}).Opens)
      (t₀ t₁ : strictHenselization B (Spec (.of A)) hA s ⟶ pullback U.ι j'),
      (U : Set (pullback p g : Scheme.{u})) = _root_.irreducibleComponent
        ((s₀ ≫ j') (IsLocalRing.closedPoint ↥(etaleLocalRing B (Spec (.of A)) hA s))) ∧
      IsIntegral U.toScheme ∧ IsNormal U.toScheme ∧ IsNoetherian U.toScheme ∧
      IsClosedImmersion U.ι ∧ IsProper (U.ι ≫ p') ∧
      (IsProjectiveMorphism p → IsProjectiveMorphism (U.ι ≫ p')) ∧
      IsIntegral (pullback U.ι j') ∧ IsNoetherian (pullback U.ι j') ∧
      IsAffine (pullback U.ι j') ∧ IsOpenImmersion (pullback.fst U.ι j') ∧
      IsDominant (pullback.fst U.ι j') ∧
      SmoothOfRelativeDimension 1 (pullback.fst U.ι j' ≫ U.ι ≫ p') ∧
      IsClosedImmersion (pullback.fst U.ι b') ∧
      IsFinite (pullback.fst U.ι b' ≫ U.ι ≫ p') ∧
      Surjective (pullback.fst U.ι b' ≫ U.ι ≫ p') ∧
      Nonempty (pullback U.ι b' : Scheme.{u}) ∧
      Set.range (pullback.fst U.ι b') = (Set.range (pullback.fst U.ι j'))ᶜ ∧
      t₀ ≫ pullback.snd U.ι j' = s₀ ∧ t₁ ≫ pullback.snd U.ι j' = s₁ ∧
      t₀ ≫ pullback.fst U.ι j' ≫ U.ι ≫ p' = 𝟙 _ ∧
      t₁ ≫ pullback.fst U.ι j' ≫ U.ι ≫ p' = 𝟙 _ ∧
      IsIntegral (PrincipalFamilyUnitOpen.parameterSpace (U.ι ≫ p')) ∧
      IsNoetherian (PrincipalFamilyUnitOpen.parameterSpace (U.ι ≫ p')) := by
  intro g j' b' p'
  have := isLocallyNoetherian_of_isRegular hreg
  obtain ⟨U, t₀, t₁, hU, hi, hn, hln, hclosed, hp, hproj, hiopen, hopen, hsm,
    hbclosed, hbfinite, hbrange, ht₀, ht₁, -, -, hsec₀, hsec₁⟩ :=
    exists_integral_component_strictLocal_retaining_sections B hA s p j b hb s₀ s₁ h₀ h₁ hs
  have := hi
  have := hln
  have := hclosed
  have := hp
  have := hiopen
  have := hopen
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ p')
  have : IsNoetherian U.toScheme := ⟨⟩
  have : IsLocallyNoetherian (pullback U.ι j') :=
    isLocallyNoetherian_of_isOpenImmersion (pullback.fst U.ι j')
  have : TopologicalSpace.NoetherianSpace (pullback U.ι j' : Scheme.{u}) :=
    (pullback.fst U.ι j').isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : IsNoetherian (pullback U.ι j') := ⟨⟩
  have : IsAffine (pullback (pullback.fst p g) j) := isAffine_pullback_retainedOpen p j g
  have : IsAffine (pullback U.ι j') := isAffine_of_isAffineHom (pullback.snd U.ι j')
  have hdom : IsDominant (pullback.fst U.ι j') :=
    ⟨(pullback.fst U.ι j').isOpenMap.isOpen_range.dense (Set.range_nonempty _)⟩
  have hsurj := surjective_strictLocal_componentBoundary_of_etale_chart B hA s hreg p π hπ
    j a ha hj e c hc he b hb _ U hU
  have := hsurj
  obtain ⟨z, -⟩ := (pullback.fst U.ι b' ≫ U.ι ≫ p').surjective
    (IsLocalRing.closedPoint ↥(etaleLocalRing B (Spec (.of A)) hA s))
  exact ⟨U, t₀, t₁, hU, hi, hn, inferInstance, hclosed, hp, hproj, hiopen, inferInstance,
    inferInstance, hopen, hdom, hsm, hbclosed, hbfinite, hsurj, ⟨z⟩, hbrange, ht₀, ht₁,
    hsec₀, hsec₁, PrincipalFamilyUnitOpen.isIntegral_parameterSpace _,
    PrincipalFamilyUnitOpen.isNoetherian_parameterSpace _⟩

end AlgebraicGeometry.Scheme
