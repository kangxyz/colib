module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.PolynomialGeometry
import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BoundaryBaseChange

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

example (B : BigEtaleSite.{u}) {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : B.Contains S) (s : GeometricPoint S) (p : X ⟶ S) [LocallyOfFiniteType p] :
    IsLocallyNoetherian (pullback p (strictHenselizationToBase B S hS s)) :=
  isLocallyNoetherian_pullback_strictHenselizationToBase B hS s p

example (B : BigEtaleSite.{u}) {S X Y D : Scheme.{u}}
    [IsLocallyNoetherian S] [IsNormal X] (hS : B.Contains S) (s : GeometricPoint S)
    (p : X ⟶ S) [IsProper p]
    (j : Y ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ p)]
    (b : D ⟶ X) [IsClosedImmersion b] [IsFinite (b ≫ p)]
    (hb : Set.range b = (Set.range j)ᶜ)
    (s₀ s₁ : strictHenselization B S hS s ⟶
      pullback (pullback.fst p (strictHenselizationToBase B S hS s)) j)
    (h₀ : s₀ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B S hS s)) j ≫
      pullback.snd p (strictHenselizationToBase B S hS s) = 𝟙 _)
    (h₁ : s₁ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B S hS s)) j ≫
      pullback.snd p (strictHenselizationToBase B S hS s) = 𝟙 _)
    (hs : (s₀ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B S hS s)) j)
        (IsLocalRing.closedPoint ↥(etaleLocalRing B S hS s)) =
      (s₁ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B S hS s)) j)
        (IsLocalRing.closedPoint ↥(etaleLocalRing B S hS s))) :
    let g := strictHenselizationToBase B S hS s
    let j' := pullback.fst (pullback.fst p g) j
    ∃ (U : (pullback p g : Scheme.{u}).Opens)
      (t₀ t₁ : strictHenselization B S hS s ⟶ pullback U.ι j'),
      IsIntegral U.toScheme ∧ IsProper (U.ι ≫ pullback.snd p g) ∧
      (IsProjectiveMorphism p → IsProjectiveMorphism (U.ι ≫ pullback.snd p g)) ∧
      t₀ ≫ pullback.snd U.ι j' = s₀ ∧ t₁ ≫ pullback.snd U.ι j' = s₁ := by
  obtain ⟨U, t₀, t₁, -, hi, -, -, -, hp, hproj, -, -, -, -, -, -, ht₀, ht₁, -⟩ :=
    exists_integral_component_strictLocal_retaining_sections B hS s p j b hb s₀ s₁ h₀ h₁ hs
  exact ⟨U, t₀, t₁, hi, hp, hproj, ht₀, ht₁⟩

#print axioms AlgebraicGeometry.isLocallyNoetherian_pullback_strictHenselizationToBase
#print axioms AlgebraicGeometry.Scheme.isProjectiveMorphism_normalComponentOpen
#print axioms AlgebraicGeometry.Scheme.exists_integral_component_retaining_sections
#print axioms AlgebraicGeometry.Scheme.exists_integral_component_strictLocal_retaining_sections


example {R : Type u} [CommRing R] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (p : X ⟶ Spec (.of R)) [IsProper p] (x : X) :
    IsIntegral (PrincipalFamilyUnitOpen.parameterSpace ((normalComponentOpen x).ι ≫ p)) ∧
    IsNoetherian (PrincipalFamilyUnitOpen.parameterSpace ((normalComponentOpen x).ι ≫ p)) :=
  ⟨isIntegral_normalComponentParameterSpace p x, isNoetherian_normalComponentParameterSpace p x⟩

example {X N V : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IrreducibleSpace N]
    (f : X ⟶ N) [Flat f] (j : V ⟶ N) [IsOpenImmersion j] [Nonempty V] (x : X) :
    Nonempty (pullback ((normalComponentOpen x).ι ≫ f) j : Scheme.{u}) :=
  nonempty_pullback_normalComponent_chart_of_flat f j x

#print axioms AlgebraicGeometry.Scheme.isNoetherian_normalComponentOpen
#print axioms AlgebraicGeometry.Scheme.isNoetherian_normalComponentRetainedOpen
#print axioms AlgebraicGeometry.Scheme.isQuasiAffine_normalComponentRetainedOpen
#print axioms AlgebraicGeometry.Scheme.isAffine_pullback_retainedOpen
#print axioms AlgebraicGeometry.Scheme.isIntegral_normalComponentParameterSpace
#print axioms AlgebraicGeometry.Scheme.isNoetherian_normalComponentParameterSpace
#print axioms AlgebraicGeometry.Scheme.nonempty_pullback_normalComponent_chart_of_flat
#print axioms AlgebraicGeometry.Scheme.surjective_normalComponentBoundary_of_nonempty_etale_chart


example {A R : Type u} [CommRing A] [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) (f : A →+* R)
    (π : X ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    IsFinite (projectiveLineCoverBaseChange p f π hπ) := inferInstance

#print axioms AlgebraicGeometry.Scheme.isPullback_projectiveLineCoverBaseChange
#print axioms AlgebraicGeometry.Scheme.isPullback_affineLineChartBaseChange
#print axioms AlgebraicGeometry.Scheme.affineLineChartBaseChange_comp_XChart
#print axioms AlgebraicGeometry.Scheme.surjective_strictLocal_componentBoundary_of_etale_chart
#print axioms AlgebraicGeometry.Scheme.exists_integral_strictLocal_component_with_surjective_boundary
