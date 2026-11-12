/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.RetainedGeometry
public import Colib.AlgebraicGeometry.Normalization.Compactification.NonemptyBoundary

/-!
# Nonempty full boundary on the same actual component

Finiteness of a boundary does not imply nonemptiness. Here the finite projective-line map,
its actual nonempty etale chart on the chosen component, and the chart compatibility force
surjectivity of that component's projective-line map. Its full retained boundary consequently
meets every base fiber. The etale chart and its nonemptiness are explicit geometric inputs;
no surjectivity or nonemptiness of the desired boundary is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Every nonempty original open chart meets the same component after any flat base change.
This is the nonemptiness input for restricting an original generically etale coordinate chart. -/
theorem nonempty_pullback_normalComponent_chart_of_flat
    {X N V : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IrreducibleSpace N]
    (f : X ⟶ N) [Flat f] (j : V ⟶ N) [IsOpenImmersion j] [Nonempty V] (x : X) :
    Nonempty (pullback ((normalComponentOpen x).ι ≫ f) j : Scheme.{u}) := by
  let q := (normalComponentOpen x).ι ≫ f
  obtain ⟨a, -, ha⟩ := Flat.generalizingMap q
    (genericPoint_specializes (q ⟨x, mem_normalComponentOpen x⟩))
  have hgen : genericPoint N ∈ Set.range j :=
    ((genericPoint_spec N).mem_open_set_iff j.isOpenMap.isOpen_range).mpr
      (by simpa only [Set.univ_inter] using Set.range_nonempty j)
  have haRange : a ∈ Set.range (pullback.fst q j) := by
    rw [Pullback.range_fst]
    change q a ∈ Set.range j
    rwa [ha]
  obtain ⟨z, -⟩ := haRange
  exact ⟨z⟩

/-- A surjective projective-line cover has full retained boundary in every fiber when its
retained open maps into the actual affine-line chart. -/
theorem surjective_fullBoundary_of_projectiveLine_chart
    (R : Type u) [CommRing R] {X Y D : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (j : Y ⟶ X) (g : Y ⟶ Spec (.of (Polynomial R)))
    (π : X ⟶ projectiveLine R) [Surjective π]
    (hπ : π ≫ (projectiveLine R ↘ Spec (.of R)) = p)
    (hj : j ≫ π = g ≫ projectiveLineXChart R)
    (b : D ⟶ X) (hb : Set.range b = (Set.range j)ᶜ) :
    Surjective (b ≫ p) := by
  constructor
  intro r
  obtain ⟨z, hz⟩ := π.surjective (projectiveLineInfinitySection R r)
  have houtside : z ∉ Set.range j := by
    rintro ⟨y, rfl⟩
    have hinfty : projectiveLineInfinitySection R r ∉ Set.range (projectiveLineXChart R) := by
      have hi : projectiveLineInfinitySection R r ∈ Set.range (projectiveLineInfinitySection R) :=
        Set.mem_range_self r
      rwa [range_projectiveLineInfinitySection] at hi
    have hπj : π (j y) = projectiveLineXChart R (g y) :=
      congrArg (fun f : Y ⟶ projectiveLine R ↦ f y) hj
    exact hinfty ⟨g y, hπj.symm.trans hz⟩
  have hzboundary : z ∈ Set.range b := by rw [hb]; exact houtside
  obtain ⟨d, hd⟩ := hzboundary
  refine ⟨d, ?_⟩
  change p (b d) = r
  rw [hd, ← hπ, Hom.comp_apply, hz]
  exact congrArg (fun f : Spec (.of R) ⟶ Spec (.of R) ↦ f r)
    (projectiveLineInfinitySection_comp_structureMorphism R)

/-- The same actual component surjects onto the projective line if its retained etale chart
is nonempty. This uses the restricted original finite map, not a new compactification. -/
theorem surjective_projectiveLine_normalComponent_of_etale_chart
    (R : Type u) [CommRing R] [IsDomain R]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (j : Y ⟶ X) (g : Y ⟶ Spec (.of (Polynomial R))) [Etale g]
    (π : X ⟶ projectiveLine R) [IsFinite π]
    (hj : j ≫ π = g ≫ projectiveLineXChart R) (x : X)
    [Nonempty (pullback (normalComponentOpen x).ι j : Scheme.{u})] :
    Surjective ((normalComponentOpen x).ι ≫ π) := by
  apply surjective_projectiveLine_cover_of_etale_chart R
    (pullback.snd (normalComponentOpen x).ι j ≫ g)
    (pullback.fst (normalComponentOpen x).ι j)
  rw [← Category.assoc, pullback.condition, Category.assoc, hj, Category.assoc]

/-- The entire original boundary, restricted to this same component, meets every base fiber.
The input nonempty etale chart is distinct from the boundary conclusion. -/
theorem surjective_normalComponentBoundary_of_etale_chart
    (R : Type u) [CommRing R] [IsDomain R]
    {X Y D : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (p : X ⟶ Spec (.of R)) (j : Y ⟶ X)
    (g : Y ⟶ Spec (.of (Polynomial R))) [Etale g]
    (π : X ⟶ projectiveLine R) [IsFinite π]
    (hπ : π ≫ (projectiveLine R ↘ Spec (.of R)) = p)
    (hj : j ≫ π = g ≫ projectiveLineXChart R)
    (b : D ⟶ X) (hb : Set.range b = (Set.range j)ᶜ) (x : X)
    [Nonempty (pullback (normalComponentOpen x).ι j : Scheme.{u})] :
    Surjective
      (pullback.fst (normalComponentOpen x).ι b ≫ (normalComponentOpen x).ι ≫ p) := by
  have := surjective_projectiveLine_normalComponent_of_etale_chart R j g π hj x
  apply surjective_fullBoundary_of_projectiveLine_chart R
    ((normalComponentOpen x).ι ≫ p) (pullback.fst (normalComponentOpen x).ι j)
    (pullback.snd (normalComponentOpen x).ι j ≫ g) ((normalComponentOpen x).ι ≫ π)
  · rw [Category.assoc, hπ]
  · rw [← Category.assoc, pullback.condition, Category.assoc, hj, Category.assoc]
  · exact range_normalComponentBoundary j b hb x

/-- The same boundary conclusion allows a separate nonempty etale chart. The whole retained
open need only map into the affine chart; its coordinate map need not be etale everywhere. -/
theorem surjective_normalComponentBoundary_of_nonempty_etale_chart
    (R : Type u) [CommRing R] [IsDomain R]
    {X Y E D : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (p : X ⟶ Spec (.of R)) (j : Y ⟶ X)
    (g : Y ⟶ Spec (.of (Polynomial R)))
    (π : X ⟶ projectiveLine R) [IsFinite π]
    (hπ : π ≫ (projectiveLine R ↘ Spec (.of R)) = p)
    (hj : j ≫ π = g ≫ projectiveLineXChart R)
    (e : E ⟶ X) (a : E ⟶ Spec (.of (Polynomial R))) [Etale a]
    (he : e ≫ π = a ≫ projectiveLineXChart R)
    (b : D ⟶ X) (hb : Set.range b = (Set.range j)ᶜ) (x : X)
    [Nonempty (pullback (normalComponentOpen x).ι e : Scheme.{u})] :
    Surjective
      (pullback.fst (normalComponentOpen x).ι b ≫ (normalComponentOpen x).ι ≫ p) := by
  have := surjective_projectiveLine_normalComponent_of_etale_chart R e a π he x
  apply surjective_fullBoundary_of_projectiveLine_chart R
    ((normalComponentOpen x).ι ≫ p) (pullback.fst (normalComponentOpen x).ι j)
    (pullback.snd (normalComponentOpen x).ι j ≫ g) ((normalComponentOpen x).ι ≫ π)
  · rw [Category.assoc, hπ]
  · rw [← Category.assoc, pullback.condition, Category.assoc, hj, Category.assoc]
  · exact range_normalComponentBoundary j b hb x

end AlgebraicGeometry.Scheme
