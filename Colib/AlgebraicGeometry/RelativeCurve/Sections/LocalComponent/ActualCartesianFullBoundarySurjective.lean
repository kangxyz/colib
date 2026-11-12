/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualCartesianAffineChart

/-! # Surjectivity of the full boundary on the actual refined component

The fixed model X may be disconnected. The independent nonempty chart belongs
to the original irreducible curve N, and flat maps from X' through X to N force
that chart to meet the selected component of X'. No component equality across
ambient curves, and no nonemptiness-from-finiteness inference, is used.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- Two successive actual chart pullbacks meet the same marked component, using
only the independent original nonempty chart and flatness to its original curve. -/
theorem nonempty_component_iterated_original_chart
    {X' X N E : Scheme.{u}} [IsLocallyNoetherian X'] [IsNormal X']
    [IrreducibleSpace N] (v : X' ⟶ X) [Flat v] (r : X ⟶ N) [Flat r]
    (e : E ⟶ N) [IsOpenImmersion e] [Nonempty E] (x : X') :
    Nonempty (pullback (normalComponentOpen x).ι
      (pullback.fst v (pullback.fst r e)) : Scheme.{u}) := by
  have hn : Nonempty (pullback (((normalComponentOpen x).ι ≫ v) ≫ r) e : Scheme.{u}) := by
    simpa only [Category.assoc] using
      nonempty_pullback_normalComponent_chart_of_flat (v ≫ r) e x
  have hn1 := hn.map (pullbackRightPullbackFstIso r e ((normalComponentOpen x).ι ≫ v)).inv
  exact hn1.map
    (pullbackRightPullbackFstIso v (pullback.fst r e) (normalComponentOpen x).ι).inv

/-- The actual full boundary of the component of X' surjects over the new integral
base. X is the fixed clopen model U, X' is Cnew; neither is assumed integral.
The independent original chart is pulled back along r and then along v. -/
theorem surjective_actualCartesian_component_fullBoundary
    {A R : Type u} [CommRing A] [CommRing R] [IsDomain R]
    {X X' Y D N E : Scheme.{u}}
    [IsLocallyNoetherian X'] [IsNormal X'] [IrreducibleSpace N]
    (p : X ⟶ Spec (.of A)) (f : A →+* R)
    (v : X' ⟶ X) [Flat v] (q : X' ⟶ Spec (.of R))
    (h : IsPullback v q p (Spec.map (CommRingCat.ofHom f)))
    (π : X ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (j : Y ⟶ X) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A)
    (r : X ⟶ N) [Flat r] (e : E ⟶ N) [IsOpenImmersion e] [Nonempty E]
    (c : pullback r e ⟶ Spec (.of (Polynomial A))) [Etale c]
    (hc : c ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) =
      pullback.fst r e ≫ p)
    (he : pullback.fst r e ≫ π = c ≫ projectiveLineXChart A)
    (d : D ⟶ X) (hd : Set.range d = (Set.range j)ᶜ) (x : X') :
    Surjective (pullback.fst (normalComponentOpen x).ι (pullback.fst v d) ≫
      (normalComponentOpen x).ι ≫ q) := by
  let := nonempty_component_iterated_original_chart v r e x
  have hd' : Set.range (pullback.fst v d) = (Set.range (pullback.fst v j))ᶜ := by
    rw [Pullback.range_fst, Pullback.range_fst, hd]
    rfl
  exact surjective_normalComponentBoundary_of_nonempty_etale_chart R q
    (pullback.fst v j) (affineLineChartOfActualCartesian p f v q h j a ha)
    (projectiveLineCoverOfActualCartesian p f v q h π hπ)
    (projectiveLineCoverOfActualCartesian_structure p f v q h π hπ)
    (affineLineChartOfActualCartesian_comp_XChart p f v q h j a ha π hπ hj)
    (pullback.fst v (pullback.fst r e))
    (affineLineChartOfActualCartesian p f v q h (pullback.fst r e) c hc)
    (affineLineChartOfActualCartesian_comp_XChart p f v q h
      (pullback.fst r e) c hc π hπ he)
    (pullback.fst v d) hd' x

end AlgebraicGeometry.Scheme
