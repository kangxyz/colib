module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleComponentRefinement
import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleRetainedGeometry
import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleBoundary

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite TopologicalSpace

universe u

noncomputable section

example {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsNoetherian (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (U : c.pt.Opens) (hU : IsClopen (U : Set c.pt)) :
    ∃ (i : I) (V : (D.obj i).Opens), IsClopen (V : Set (D.obj i)) ∧
      c.π.app i ⁻¹ᵁ V = U :=
  exists_clopen_preimage_eq D c hc U hU

section OriginalModel

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  {N : Scheme.{u}} (p : N ⟶ X.left) (B : BigEtaleSite.{u})
  (hX : B.Contains X.left) (s : GeometricPoint X.left)

example : IsLimit (etaleCurveCone X B hX s p) := etaleCurveConeIsLimit X B hX s p

example (i : SmallEtaleNeighborhood X s) :
    IsPullback ((etaleCurveCone X B hX s p).π.app i)
      (pullback.fst (strictHenselizationToBase B X.left hX s) p)
      ((etaleCurveStructure X s p).app i)
      ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i) :=
  etaleCurveCone_isPullback X B hX s p i

set_option backward.isDefEq.respectTransparency false in
example
    [IsLocallyNoetherian X.left] [IsNormal X.left] [IsNormal N] [IsProper p]
    (x : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}))
    (i₀ : SmallEtaleNeighborhood X s) :
    ∃ (i : SmallEtaleNeighborhood X s) (_ : i ⟶ i₀)
      (C : EtaleNeighborhood X s.hom)
      (f : C ⟶ (smallEtaleNeighborhoodInclusion X s).obj i),
      IsIntegral ((etaleNeighborhoodToSmooth X s.hom).obj C).left ∧
      IsNoetherian ((etaleNeighborhoodToSmooth X s.hom).obj C).left ∧
      IsOpenImmersion (((etaleNeighborhoodToSmooth X s.hom).map f).left) ∧
      IsClosedImmersion (((etaleNeighborhoodToSmooth X s.hom).map f).left) ∧
      ((etaleNeighborhoodCurveConeLeg X p B hX s C ⁻¹ᵁ
        normalComponentOpen (etaleNeighborhoodCurveConeLeg X p B hX s C x)) :
          Set (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u})) =
            _root_.irreducibleComponent x :=
  exists_integral_etaleNeighborhood_same_component X p B hX s x i₀

end OriginalModel

section Retained

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N Y D : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
example
    [IsLocallyNoetherian X.left] [IsAffine X.left] [IsNormal N] [IsAffine Y]
    (p : N ⟶ X.left) [IsProper p]
    (j : Y ⟶ N) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ p)]
    (b : D ⟶ N) [IsClosedImmersion b] [IsFinite (b ≫ p)]
    (hb : Set.range b = (Set.range j)ᶜ) (i : EtaleNeighborhood X s.hom)
    (x : (pullback p (etaleNeighborhoodHom X s.hom i).left : Scheme.{u}))
    (hx : x ∈ Set.range (pullback.fst
      (pullback.fst p (etaleNeighborhoodHom X s.hom i).left) j)) :
    let f := (etaleNeighborhoodHom X s.hom i).left
    let q := pullback.snd p f
    let j' := pullback.fst (pullback.fst p f) j
    let b' := pullback.fst (pullback.fst p f) b
    let U := normalComponentOpen x
    let r := pullback.fst U.ι j' ≫ U.ι ≫ q
    IsIntegral U.toScheme ∧ IsNoetherian U.toScheme ∧ IsProper (U.ι ≫ q) ∧
      (IsProjectiveMorphism p → IsProjectiveMorphism (U.ι ≫ q)) ∧
      IsIntegral (pullback U.ι j') ∧ IsNoetherian (pullback U.ι j') ∧
      IsAffine (pullback U.ι j') ∧ IsDominant (pullback.fst U.ι j') ∧
      SmoothOfRelativeDimension 1 r ∧ IsClosedImmersion (pullback.fst U.ι b') ∧
      IsFinite (pullback.fst U.ι b' ≫ U.ι ≫ q) ∧
      Set.range (pullback.fst U.ι b') = (Set.range (pullback.fst U.ι j'))ᶜ ∧
      ∃ (W : SmoothSite S) (e : W.left ≅ pullback U.ι j'),
        e.hom ≫ r ≫ ((etaleNeighborhoodToSmooth X s.hom).obj i).hom = W.hom :=
  retainedGeometry_etaleNeighborhood_normalComponent X s p j b hb i x hx

end Retained

set_option backward.isDefEq.respectTransparency false in
example
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A : Type u} [CommRing A] [IsLocallyNoetherian (Spec (.of A))]
    (α : Spec (.of A) ⟶ S) [Smooth α] [IsSeparated α] [QuasiCompact α]
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ Spec (.of A))
    (C : EtaleNeighborhood (mk α) ξ)
    [IsIntegral ((etaleNeighborhoodToSmooth (mk α) ξ).obj C).left]
    {N Y E D : Scheme.{u}} [IsNormal N] [IsIntegral N]
    (p : N ⟶ Spec (.of A)) [IsProper p]
    (π : N ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (j : Y ⟶ N) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A)
    (e : E ⟶ N) [IsOpenImmersion e] [Nonempty E]
    (c : E ⟶ Spec (.of (Polynomial A))) [Etale c]
    (hc : c ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = e ≫ p)
    (he : e ≫ π = c ≫ projectiveLineXChart A)
    (b : D ⟶ N) (hb : Set.range b = (Set.range j)ᶜ)
    (x : (pullback p (etaleNeighborhoodHom (mk α) ξ C).left : Scheme.{u})) :
    ∃ U : (pullback p (etaleNeighborhoodHom (mk α) ξ C).left : Scheme.{u}).Opens,
      (U : Set (pullback p (etaleNeighborhoodHom (mk α) ξ C).left : Scheme.{u})) =
        _root_.irreducibleComponent x ∧
      Surjective (pullback.fst U.ι
        (pullback.fst (pullback.fst p (etaleNeighborhoodHom (mk α) ξ C).left) b) ≫
          U.ι ≫ pullback.snd p (etaleNeighborhoodHom (mk α) ξ C).left) :=
  exists_etaleNeighborhood_normalComponent_surjectiveBoundary α ξ C p π hπ
    j a ha hj e c hc he b hb x

example
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormal X] [IsNormal Y] (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsPullback (f.resLE (normalComponentOpen (f x)) (normalComponentOpen x)
      (normalComponentOpen_preimage_of_isOpenImmersion f x).ge)
      (normalComponentOpen x).ι (normalComponentOpen (f x)).ι f :=
  normalComponentOpen_isPullback_of_isOpenImmersion f x

example {T N : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian N] [IsNormal N]
    (p : N ⟶ T) (s₀ s₁ : T ⟶ N) (t : T) (hs : s₀ t = s₁ t)
    (h₀ : s₀ ≫ p = 𝟙 T) (h₁ : s₁ ≫ p = 𝟙 T) :
    ∃ (a₀ a₁ : T ⟶ (normalComponentOpen (s₀ t)).toScheme),
      a₀ ≫ (normalComponentOpen (s₀ t)).ι = s₀ ∧
      a₁ ≫ (normalComponentOpen (s₀ t)).ι = s₁ ∧
      a₀ ≫ (normalComponentOpen (s₀ t)).ι ≫ p = 𝟙 T ∧
      a₁ ≫ (normalComponentOpen (s₀ t)).ι ≫ p = 𝟙 T := by
  obtain ⟨a₀, a₁, ha₀, ha₁⟩ := exists_integral_component_lifts_of_preconnected s₀ s₁ t hs
  exact ⟨a₀, a₁, ha₀, ha₁, by rw [← Category.assoc, ha₀, h₀],
    by rw [← Category.assoc, ha₁, h₁]⟩

example {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
    [IsLocallyNoetherian X.left] {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ X.left) (C : EtaleNeighborhood X ξ)
    {N : Scheme.{u}} [IsNormal N] (p : N ⟶ X.left) [IsProper p]
    (x : (pullback p (etaleNeighborhoodHom X ξ C).left : Scheme.{u})) :
    IsIntegral (PrincipalFamilyUnitOpen.parameterSpace
      ((normalComponentOpen x).ι ≫ pullback.snd p (etaleNeighborhoodHom X ξ C).left)) ∧
    IsNoetherian (PrincipalFamilyUnitOpen.parameterSpace
      ((normalComponentOpen x).ι ≫ pullback.snd p (etaleNeighborhoodHom X ξ C).left)) := by
  have hp : IsProper (pullback.snd p (etaleNeighborhoodHom X ξ C).left) := inferInstance
  exact ⟨isIntegral_normalComponentParameterSpace (R := C.obj.left.unop)
      (pullback.snd p (etaleNeighborhoodHom X ξ C).left) x,
    @isNoetherian_normalComponentParameterSpace _ _ _ C.obj.left.unop _
      (pullback.snd p (etaleNeighborhoodHom X ξ C).left) hp x⟩

#print axioms AlgebraicGeometry.Scheme.exists_clopen_preimage_eq
#print axioms AlgebraicGeometry.Scheme.SmoothSite.exists_integral_etaleNeighborhood_same_component
#print axioms AlgebraicGeometry.Scheme.SmoothSite.retainedGeometry_etaleNeighborhood_normalComponent
#print axioms
  AlgebraicGeometry.Scheme.SmoothSite.exists_etaleNeighborhood_normalComponent_surjectiveBoundary
#print axioms AlgebraicGeometry.Scheme.normalComponentOpen_isPullback_of_isOpenImmersion
#print axioms AlgebraicGeometry.Scheme.exists_integral_component_lifts_of_preconnected
