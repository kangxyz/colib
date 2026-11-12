/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# The same normal component at a finite stage of an actual limit

A clopen of a cofiltered limit of Noetherian schemes with affine transitions descends as a
clopen. When the stages and limit are normal, the actual component through the image of a
specified limit point can be used at a stage: its preimage is exactly the original component.
No stage component certificate or integrality of every stage is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- An actual normal component is transported exactly by an open immersion containing its
specified point. This also records the canonical pullback-symmetry identification. -/
theorem normalComponentOpen_preimage_of_isOpenImmersion
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormal X] [IsNormal Y] (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    f ⁻¹ᵁ normalComponentOpen (f x) = normalComponentOpen x := by
  have hC := preimage_mem_irreducibleComponents
    (irreducibleComponent_mem_irreducibleComponents (f x)) f.isOpenEmbedding
    ⟨f x, mem_irreducibleComponent, x, rfl⟩
  have hsub : normalComponentOpen x ≤ f ⁻¹ᵁ normalComponentOpen (f x) :=
    (irreducibleComponent_mem_irreducibleComponents x).1.2.isPreconnected.subset_isClopen
      ((isClopen_normalComponentOpen (f x)).preimage f.continuous)
      ⟨x, mem_normalComponentOpen x, mem_normalComponentOpen _⟩
  exact le_antisymm ((irreducibleComponent_mem_irreducibleComponents x).2 hC.1 hsub) hsub

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, IsNoetherian (D.obj i)] (c : Cone D) (hc : IsLimit c)

include hc in
/-- An actual clopen of the limit descends as a clopen at a finite stage. -/
theorem exists_clopen_preimage_eq (U : c.pt.Opens) (hU : IsClopen (U : Set c.pt)) :
    ∃ (i : I) (V : (D.obj i).Opens), IsClopen (V : Set (D.obj i)) ∧
      c.π.app i ⁻¹ᵁ V = U := by
  have : CompactSpace c.pt := compactSpace_of_isLimit D c hc
  let Uc : c.pt.Opens := ⟨(U : Set c.pt)ᶜ, hU.isClosed.isOpen_compl⟩
  obtain ⟨i, V, -, hV⟩ := exists_preimage_eq D c hc U hU.isClosed.isCompact
  obtain ⟨j, W, -, hW⟩ := exists_preimage_eq D c hc Uc hU.isOpen.isClosed_compl.isCompact
  let k := IsCofiltered.min i j
  let f : k ⟶ i := IsCofiltered.minToLeft i j
  let g : k ⟶ j := IsCofiltered.minToRight i j
  let V' := D.map f ⁻¹ᵁ V
  let W' := D.map g ⁻¹ᵁ W
  have hV' : c.π.app k ⁻¹ᵁ V' = U := by
    simpa only [V', ← Hom.comp_preimage, c.w] using hV
  have hW' : c.π.app k ⁻¹ᵁ W' = Uc := by
    simpa only [W', ← Hom.comp_preimage, c.w] using hW
  have hsup : c.π.app k ⁻¹ᵁ (V' ⊔ W') = ⊤ := by
    rw [Hom.preimage_sup, hV', hW']
    ext x
    simp [Uc]
  have hinf : c.π.app k ⁻¹ᵁ (V' ⊓ W') ≤ c.π.app k ⁻¹ᵁ ⊥ := by
    rw [Hom.preimage_inf, hV', hW', Hom.preimage_bot]
    intro x hx
    exact (hx.2 hx.1).elim
  obtain ⟨l, a, ha⟩ := exists_map_eq_top D c hc (V' ⊔ W') hsup
  obtain ⟨m, b, hb⟩ := exists_map_preimage_le_map_preimage D c hc
    (NoetherianSpace.isCompact _) hinf
  obtain ⟨n, d, e, hde⟩ := IsCofiltered.cospan a b
  let Vn := D.map (d ≫ a) ⁻¹ᵁ V'
  let Wn := D.map (d ≫ a) ⁻¹ᵁ W'
  have hsup' : Vn ⊔ Wn = ⊤ := by
    simp only [Vn, Wn, D.map_comp, Hom.comp_preimage, ← Hom.preimage_sup, ha,
      Hom.preimage_top]
  have hinf' : Vn ⊓ Wn ≤ ⊥ := by
    have h := Hom.preimage_mono (D.map e) hb
    simpa only [Vn, Wn, hde, D.map_comp, Hom.comp_preimage, ← Hom.preimage_inf,
      Hom.preimage_bot] using h
  have hcompl : (Vn : Set (D.obj n)) = (Wn : Set (D.obj n))ᶜ := by
    ext x
    constructor
    · intro hx hx'
      exact hinf' ⟨hx, hx'⟩
    · intro hx
      have h : x ∈ Vn ⊔ Wn := hsup'.symm ▸ trivial
      exact h.elim id (fun h' => (hx h').elim)
  refine ⟨n, Vn, ⟨?_, Vn.isOpen⟩, ?_⟩
  · rw [hcompl]
    exact Wn.isOpen.isClosed_compl
  · simpa only [Vn, ← Hom.comp_preimage, c.w] using hV'

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- The preimage of the stage component contains the entire component of the original point. -/
theorem normalComponentOpen_le_preimage
    [IsLocallyNoetherian c.pt] [IsNormal c.pt] [∀ i, IsNormal (D.obj i)]
    (x : c.pt) (i : I) :
    normalComponentOpen x ≤ c.π.app i ⁻¹ᵁ normalComponentOpen (c.π.app i x) :=
  (irreducibleComponent_mem_irreducibleComponents x).1.2.isPreconnected.subset_isClopen
    ((isClopen_normalComponentOpen (c.π.app i x)).preimage (c.π.app i).continuous)
    ⟨x, mem_normalComponentOpen x, mem_normalComponentOpen _⟩

include hc in
/-- The actual normal component through a limit point is the exact preimage of the actual
normal component through its image at a finite stage. -/
theorem exists_normalComponentOpen_preimage_eq
    [IsLocallyNoetherian c.pt] [IsNormal c.pt] [∀ i, IsNormal (D.obj i)] (x : c.pt) :
    ∃ i : I, c.π.app i ⁻¹ᵁ normalComponentOpen (c.π.app i x) = normalComponentOpen x := by
  obtain ⟨i, V, hV, hpre⟩ := exists_clopen_preimage_eq D c hc
    (normalComponentOpen x) (isClopen_normalComponentOpen x)
  have hx : c.π.app i x ∈ V := by
    change x ∈ c.π.app i ⁻¹ᵁ V
    rw [hpre]
    exact mem_normalComponentOpen x
  have hsub : normalComponentOpen (c.π.app i x) ≤ V :=
    (irreducibleComponent_mem_irreducibleComponents
      (c.π.app i x)).1.2.isPreconnected.subset_isClopen
      hV ⟨c.π.app i x, mem_normalComponentOpen _, hx⟩
  exact ⟨i, le_antisymm ((Hom.preimage_mono _ hsub).trans hpre.le)
    (normalComponentOpen_le_preimage D c x i)⟩


omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
/-- After a component has descended, the marked actual component at every further stage has
that same preimage. The entire base change is not asserted to be integral. -/
theorem normalComponentOpen_preimage_eq_of_refinement
    [IsLocallyNoetherian c.pt] [IsNormal c.pt] [∀ i, IsNormal (D.obj i)]
    (x : c.pt) {i j : I} (f : j ⟶ i)
    (hi : c.π.app i ⁻¹ᵁ normalComponentOpen (c.π.app i x) = normalComponentOpen x) :
    c.π.app j ⁻¹ᵁ normalComponentOpen (c.π.app j x) = normalComponentOpen x := by
  have hx : D.map f (c.π.app j x) = c.π.app i x := by
    rw [← Hom.comp_apply, c.w]
  have hsub : normalComponentOpen (c.π.app j x) ≤
      D.map f ⁻¹ᵁ normalComponentOpen (c.π.app i x) :=
    (irreducibleComponent_mem_irreducibleComponents
      (c.π.app j x)).1.2.isPreconnected.subset_isClopen
      ((isClopen_normalComponentOpen (c.π.app i x)).preimage (D.map f).continuous)
      ⟨c.π.app j x, mem_normalComponentOpen _, by
        change D.map f (c.π.app j x) ∈ normalComponentOpen (c.π.app i x)
        rw [hx]
        exact mem_normalComponentOpen _⟩
  apply le_antisymm _ (normalComponentOpen_le_preimage D c x j)
  have h := Hom.preimage_mono (c.π.app j) hsub
  simpa only [← Hom.comp_preimage, c.w, hi] using h

include hc in
/-- The same component can be supplied after any prescribed initial stage, allowing a common
refinement with the original root, frame and section data. -/
theorem exists_normalComponentOpen_preimage_eq_over
    [IsLocallyNoetherian c.pt] [IsNormal c.pt] [∀ i, IsNormal (D.obj i)]
    (x : c.pt) (i₀ : I) :
    ∃ (i : I) (_ : i ⟶ i₀),
      c.π.app i ⁻¹ᵁ normalComponentOpen (c.π.app i x) = normalComponentOpen x := by
  obtain ⟨i, hi⟩ := exists_normalComponentOpen_preimage_eq D c hc x
  exact ⟨IsCofiltered.min i i₀, IsCofiltered.minToRight i i₀,
    normalComponentOpen_preimage_eq_of_refinement D c x (IsCofiltered.minToLeft i i₀) hi⟩


/-- Each stage of that actual Cartesian component diagram is Noetherian. -/
instance normalComponentStageDiagram_isNoetherian [∀ i, IsNormal (D.obj i)]
    (i : I) (x : D.obj i) (j : Over i) :
    IsNoetherian ((opensDiagram D i (normalComponentOpen x)).obj j) := by
  let U := D.map j.hom ⁻¹ᵁ normalComponentOpen x
  change IsNoetherian U.toScheme
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  exact ⟨⟩

end AlgebraicGeometry.Scheme
