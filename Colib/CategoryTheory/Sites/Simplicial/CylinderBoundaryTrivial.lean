/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CylinderEndpointMono
import Colib.CategoryTheory.Limits.FixedQuotientPullback
import Mathlib.CategoryTheory.Adhesive.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The relative boundary inclusion of a pointed cylinder

The cylinder of a monomorphism and the two target endpoints meet exactly
in the two source endpoints. The actual boundary pushout is therefore a
monomorphism. For a stalkwise trivial map it is again stalkwise trivial.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]
  {A B : PointedSimplicialPresheaf.{w} C} (f : A ⟶ B)

private theorem product_pointAxis_isPullback [Mono f.right] (K : Cᵒᵖ ⥤ SSet.{w}) :
    IsPullback (intervalAxis A K) (𝟙 K) (prod.map f.right (𝟙 K)) (intervalAxis B K) := by
  refine IsPullback.mk' (by apply prod.hom_ext <;> simp [intervalAxis, Under.w])
    (fun _ _ _ _ e => by simpa using e) ?_
  intro T a b h
  refine ⟨b, ?_, by simp⟩
  apply prod.hom_ext
  · apply (cancel_mono f.right).1
    have h' := congrArg (· ≫ (prod.fst : B.right ⨯ K ⟶ B.right)) h
    simp only [intervalAxis, Category.assoc, prod.lift_fst, Under.w]
    simpa only [intervalAxis, Category.assoc, prod.map_fst, prod.lift_fst,
      terminal.comp_from] using h'.symm
  · have h' := congrArg (· ≫ (prod.snd : B.right ⨯ K ⟶ K)) h
    simpa only [intervalAxis, Category.assoc, prod.map_snd, prod.lift_snd, Category.comp_id]
      using h'.symm

private theorem product_endpointGraph_isPullback [Mono f.right] (i : Fin 2) :
    IsPullback (endpointGraph A i) f.right (prod.map f.right (𝟙 (interval C)))
      (endpointGraph B i) := by
  refine IsPullback.mk' (by apply prod.hom_ext <;> simp [endpointGraph])
    (fun _ _ _ _ e => (cancel_mono f.right).1 e) ?_
  intro T a b h
  refine ⟨a ≫ prod.fst, ?_, ?_⟩
  · apply prod.hom_ext
    · simp
    · have h' := congrArg (· ≫ (prod.snd : B.right ⨯ interval C ⟶ interval C)) h
      simpa only [endpointGraph, Category.assoc, prod.lift_snd, prod.map_snd,
        Category.comp_id, terminal.comp_from_assoc] using h'.symm
  · have h' := congrArg (· ≫ (prod.fst : B.right ⨯ interval C ⟶ B.right)) h
    simpa only [endpointGraph, Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
      using h'

private theorem quotientCylinder_isPullback_at [Mono f.right] (U : Cᵒᵖ)
    (n : SimplexCategoryᵒᵖ) :
    let E := cylinderDegreeEvaluation.{w} U n
    let K := interval.{w} C
    IsPullback (E.map (pushout.inl (intervalAxis A K) (terminal.from K)))
      (E.map (prod.map f.right (𝟙 K)))
      (E.map (parameterizedCylinderMap f (interval C)).right)
      (E.map (pushout.inl (intervalAxis B K) (terminal.from K))) := by
  let E := cylinderDegreeEvaluation.{w} U n
  let K := interval.{w} C
  let a := intervalAxis A K
  let b := intervalAxis B K
  let t := terminal.from K
  let p := pushout.inl a t
  let q := pushout.inl b t
  let g := parameterizedCylinderMap f K
  let F := prod.map f.right (𝟙 K)
  let : Mono F := inferInstanceAs (Mono (prod.map f.right (𝟙 K)))
  let : Mono (E.map F) := E.map_mono F
  let : Mono b := mono_of_mono_fac
    (prod.lift_snd (terminal.from K ≫ B.hom) (𝟙 K))
  let : Mono (E.map b) := E.map_mono b
  have w₁ : p ≫ g.right = F ≫ q := pushout.inl_desc _ _ _
  have w₂ : pushout.inr a t ≫ g.right = pushout.inr b t := by
    change pushout.inr a t ≫ pushout.desc _ _ _ = _
    rw [pushout.inr_desc, Category.id_comp]
  exact Types.isPullback_of_pushout_fixed ((IsPushout.of_hasPushout a t).map E)
    ((IsPushout.of_hasPushout b t).map E)
    (by
      simpa only [E.map_id] using (product_pointAxis_isPullback f K).map E)
    (by rw [← E.map_comp, ← E.map_comp, w₁]) (by rw [← E.map_comp, w₂])

private theorem cylinder_isPullback_at [Mono f.right] (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (i : Fin 2) :
    let E := cylinderDegreeEvaluation.{w} U n
    IsPullback (E.map (cylinderSection A (intervalEndpoint C i)).right) (E.map f.right)
      (E.map (parameterizedCylinderMap f (interval C)).right)
      (E.map (cylinderSection B (intervalEndpoint C i)).right) := by
  let E := cylinderDegreeEvaluation.{w} U n
  have h := ((product_endpointGraph_isPullback f i).map E).paste_horiz
    (quotientCylinder_isPullback_at f U n)
  simpa only [cylinderSection, Under.homMk_right, Functor.map_comp] using h

private theorem mono_parameterizedCylinderMap_at [Mono f.right] (U : Cᵒᵖ)
    (n : SimplexCategoryᵒᵖ) :
    Mono ((cylinderDegreeEvaluation U n).map (parameterizedCylinderMap f (interval C)).right) := by
  let E := cylinderDegreeEvaluation.{w} U n
  let K := interval.{w} C
  let a := intervalAxis A K
  let t := terminal.from K
  let p := pushout.inl a t
  have pb := quotientCylinder_isPullback_at f U n
  let : Mono (E.map (prod.map f.right (𝟙 K))) := E.map_mono _
  let : Unique (E.obj (⊤_ (Cᵒᵖ ⥤ SSet.{w}))) :=
    Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj E _)
  apply (CategoryTheory.mono_iff_injective _).2
  intro x y hxy
  rcases Types.eq_or_eq_of_isPushout ((IsPushout.of_hasPushout a t).map E) x with
    ⟨x', rfl⟩ | ⟨z, rfl⟩
  · obtain ⟨y', hy', hf⟩ := Types.exists_of_isPullback pb y (E.map (prod.map f.right (𝟙 K)) x')
      (hxy.symm.trans (ConcreteCategory.congr_hom pb.w x'))
    exact (congrArg (E.map p) (CategoryTheory.injective_of_mono _ hf.symm)).trans hy'
  · rcases Types.eq_or_eq_of_isPushout ((IsPushout.of_hasPushout a t).map E) y with
      ⟨y', rfl⟩ | ⟨z', rfl⟩
    · obtain ⟨x', hx', hf⟩ := Types.exists_of_isPullback pb (E.map (pushout.inr a t) z)
        (E.map (prod.map f.right (𝟙 K)) y') (hxy.trans (ConcreteCategory.congr_hom pb.w y'))
      exact hx'.symm.trans (congrArg (E.map p) (CategoryTheory.injective_of_mono _ hf))
    · exact congrArg (E.map (pushout.inr a t)) (Subsingleton.elim z z')

private theorem endpointPairMap_isPullback_at [Mono f.right] (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    let E := cylinderDegreeEvaluation.{w} U n
    IsPullback (E.map (simplicialEndpointPair A).right) (E.map (coprod.map f f).right)
      (E.map (parameterizedCylinderMap f (interval C)).right)
      (E.map (simplicialEndpointPair B).right) := by
  let E := cylinderDegreeEvaluation.{w} U n
  let tA := simplicialEndpointPair A
  let tB := simplicialEndpointPair B
  let F := coprod.map f f
  let G := parameterizedCylinderMap f (interval C)
  have w : E.map tA.right ≫ E.map G.right = E.map F.right ≫ E.map tB.right := by
    rw [← E.map_comp, ← E.map_comp]
    exact congrArg E.map (congrArg Under.Hom.right (simplicialEndpointPair_naturality f))
  let : Mono (E.map tA.right) := mono_simplicialEndpointPair_at A U n
  rw [Types.isPullback_iff]
  refine ⟨w, fun _ _ h => CategoryTheory.injective_of_mono (E.map tA.right) h.1, ?_⟩
  intro x y h
  let i₀ : B ⟶ B ⨿ B := coprod.inl
  let i₁ : B ⟶ B ⨿ B := coprod.inr
  have hp := (endpointCoproduct_isPushout B).map E
  rcases Types.eq_or_eq_of_isPushout hp y with ⟨y₀, rfl⟩ | ⟨y₁, rfl⟩
  · let j₀ : A ⟶ A ⨿ A := coprod.inl
    have hy : E.map G.right x =
        E.map (cylinderSection B (intervalEndpoint C 0)).right y₀ := by
      have e : E.map i₀.right ≫ E.map tB.right =
          E.map (cylinderSection B (intervalEndpoint C 0)).right := by
        rw [← E.map_comp]
        exact congrArg E.map (congrArg Under.Hom.right (coprod.inl_desc _ _))
      exact h.trans (ConcreteCategory.congr_hom e y₀)
    obtain ⟨z, hz, hzf⟩ := Types.exists_of_isPullback (cylinder_isPullback_at f U n 0) x y₀ hy
    refine ⟨E.map j₀.right z, ?_, ?_⟩
    · have e : E.map j₀.right ≫ E.map tA.right =
          E.map (cylinderSection A (intervalEndpoint C 0)).right := by
        rw [← E.map_comp]
        exact congrArg E.map (congrArg Under.Hom.right (coprod.inl_desc _ _))
      exact (ConcreteCategory.congr_hom e z).trans hz
    · have e : E.map j₀.right ≫ E.map F.right = E.map f.right ≫ E.map i₀.right := by
        rw [← E.map_comp, ← E.map_comp]
        exact congrArg E.map (congrArg Under.Hom.right (coprod.inl_map f f))
      exact (ConcreteCategory.congr_hom e z).trans (congrArg (E.map i₀.right) hzf)
  · let j₁ : A ⟶ A ⨿ A := coprod.inr
    have hy : E.map G.right x =
        E.map (cylinderSection B (intervalEndpoint C 1)).right y₁ := by
      have e : E.map i₁.right ≫ E.map tB.right =
          E.map (cylinderSection B (intervalEndpoint C 1)).right := by
        rw [← E.map_comp]
        exact congrArg E.map (congrArg Under.Hom.right (coprod.inr_desc _ _))
      exact h.trans (ConcreteCategory.congr_hom e y₁)
    obtain ⟨z, hz, hzf⟩ := Types.exists_of_isPullback (cylinder_isPullback_at f U n 1) x y₁ hy
    refine ⟨E.map j₁.right z, ?_, ?_⟩
    · have e : E.map j₁.right ≫ E.map tA.right =
          E.map (cylinderSection A (intervalEndpoint C 1)).right := by
        rw [← E.map_comp]
        exact congrArg E.map (congrArg Under.Hom.right (coprod.inr_desc _ _))
      exact (ConcreteCategory.congr_hom e z).trans hz
    · have e : E.map j₁.right ≫ E.map F.right = E.map f.right ≫ E.map i₁.right := by
        rw [← E.map_comp, ← E.map_comp]
        exact congrArg E.map (congrArg Under.Hom.right (coprod.inr_map f f))
      exact (ConcreteCategory.congr_hom e z).trans (congrArg (E.map i₁.right) hzf)

/-- The actual boundary inclusion of a pointed simplicial monomorphism is monic. -/
theorem mono_cylinderBoundaryMap [Mono f] : Mono (cylinderBoundaryMap f) := by
  let : Mono f.right := Under.mono_right_of_mono f
  suffices h : Mono (cylinderBoundaryMap f).right from Under.mono_of_mono_right _
  refine (NatTrans.mono_iff_mono_app _).2 fun U =>
    (NatTrans.mono_iff_mono_app _).2 fun n => ?_
  let E := cylinderDegreeEvaluation.{w} U n
  let G := parameterizedCylinderMap f (interval C)
  let : Mono (E.map G.right) := mono_parameterizedCylinderMap_at f U n
  let : Mono (E.map (simplicialEndpointPair B).right) := mono_simplicialEndpointPair_at B U n
  have sq := ((IsPushout.of_hasPushout (simplicialEndpointPair A) (coprod.map f f)).map
    (forget.{w} C)).map E
  change Mono (E.map (cylinderBoundaryMap f).right)
  refine Types.mono_of_isPushout_of_isPullback sq (endpointPairMap_isPullback_at f U n) ?_ ?_ ?_
  · exact (E.map_comp _ _).symm.trans
      (congrArg E.map (congrArg Under.Hom.right (cylinderBoundary_inl_map f)))
  · exact (E.map_comp _ _).symm.trans
      (congrArg E.map (congrArg Under.Hom.right (cylinderBoundary_inr_map f)))
  · intro x y _ _ e
    exact CategoryTheory.injective_of_mono (E.map (simplicialEndpointPair B).right) e

/-- The boundary inclusion of a stalkwise trivial monomorphism is itself trivial. -/
theorem stalkwiseTrivialMonomorphisms_cylinderBoundaryMap [LocallySmall.{w} C]
    (J : GrothendieckTopology C) (hf : stalkwiseTrivialMonomorphisms C J f) :
    stalkwiseTrivialMonomorphisms C J (cylinderBoundaryMap f) := by
  let : Mono f := hf.1
  exact ⟨mono_cylinderBoundaryMap f, stalkwiseWeakEquivalences_cylinderBoundaryMap J hf⟩

end CategoryTheory.PointedSimplicialPresheaf
