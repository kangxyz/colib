module

import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteLifting

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

-- Every scheme-theoretic point and nilpotent is retained by the canonical pullback.
example {Z S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (s : S) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (n : ℕ) (V : Fin n → (pullback p g).Opens),
      (∀ i, IsClopen (V i : Set (pullback p g : Scheme)) ∧
        IsFinite ((V i).ι ≫ pullback.snd p g)) ∧
      Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧ (⨆ i, V i) = ⊤ ∧
      ∀ i, ∃ v : V i, pullback.snd p g v.1 = u ∧
        ∀ v' : V i, pullback.snd p g v'.1 = u → v' = v :=
  exists_nisnevich_finiteSplitting p s

-- The lift realizes the input point, not just some point above the same support branch.
example {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p]
    (s : S) (z : Z) (hz : p z = s) (huniq : ∀ z' : Z, p z' = s → z' = z)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (v : V) (hv : q v = z) (hres : IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g ∧
      ∀ t : (pullback p g : Scheme), pullback.snd p g t = u → b t = v :=
  exists_nisnevich_lift_of_isFinite_singleton_with_point p s z hz huniq q v hv hres

-- Gluing is valid for arbitrary indexing universes, including empty disjoint open covers.
example {X V Z : Scheme.{u}} (a : X ⟶ Z) (q : V ⟶ Z)
    {I : Type v} (E : I → X.Opens)
    (hdisj : Pairwise fun i j ↦ Disjoint (E i) (E j))
    (hcover : iSup E = ⊤) (b : ∀ i, (E i).toScheme ⟶ V)
    (hb : ∀ i, b i ≫ q = (E i).ι ≫ a) :
    ∃ f : X ⟶ V, f ≫ q = a ∧ ∀ i, (E i).ι ≫ f = b i :=
  Scheme.exists_lift_of_disjoint_openCover a q E hdisj hcover b hb

-- No flatness, reducedness, connectedness, perfection, or integral-base premise occurs.
example {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (s : S)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (hq : ∀ z : Z, p z = s → ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g :=
  exists_nisnevich_lift_of_isFinite p s q hq

-- A missing fiber imposes no arbitrary lift hypothesis.
example {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (s : S)
    (hempty : ∀ z : Z, p z ≠ s) (q : V ⟶ Z) [Etale q] [IsSeparated q] :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g :=
  exists_nisnevich_lift_of_isFinite p s q (fun z hz ↦ (hempty z hz).elim)

-- The empty family of pointed neighborhoods still has an actual pointed refinement.
example {S : Scheme.{u}} (s : S) :
    ∃ (W : Scheme.{u}) (h : W ⟶ S), Etale h ∧
    ∃ w : W, h w = s ∧ IsIso (h.residueFieldMap w) := by
  obtain ⟨W, h, hh, w, hw, hr, _, _, _⟩ := exists_common_nisnevich_refinement s 0
    (fun _ ↦ S) (fun _ ↦ 𝟙 S) (fun _ ↦ inferInstance) (fun _ ↦ s)
    (fun _ ↦ rfl) (fun _ ↦ inferInstance)
  exact ⟨W, h, hh, w, hw, hr⟩

-- The upper endpoint returns an actual smooth, separated, finite-type object over the affine base.
example {S : Scheme.{u}} [IsAffine S] (X : Scheme.SmoothSite S)
    {Z V : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p] (x : X.left)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (hq : ∀ z : Z, p z = x → ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.SmoothSite S) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ b : pullback p g.left ⟶ V, b ≫ q = pullback.fst p g.left :=
  Scheme.SmoothSite.exists_nisnevich_lift_of_isFinite X p x q hq

example {S : Scheme.{u}} [IsAffine S] (X : Scheme.SmoothSite S) (x : X.left) :
    ∃ (W : Scheme.SmoothSite S) (h : W ⟶ X), Etale h.left ∧
    ∃ w : W.left, h.left w = x ∧ IsIso (h.left.residueFieldMap w) := by
  obtain ⟨W, h, hh, w, hw, hr, _, _, _⟩ :=
    Scheme.SmoothSite.exists_common_nisnevich_refinement X x 0
      (fun _ ↦ X) (fun _ ↦ 𝟙 X) (fun _ ↦ inferInstance) (fun _ ↦ x)
      (fun _ ↦ rfl) (fun _ ↦ inferInstance)
  exact ⟨W, h, hh, w, hw, hr⟩
