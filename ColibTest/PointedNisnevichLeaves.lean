module

import Colib.AlgebraicGeometry.Morphisms.FiniteEtale.FiniteEtaleNeighborhoodIso
import Colib.AlgebraicGeometry.Sites.Nisnevich.Lifting.QuasiFinite

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

-- No finiteness, reducedness or connectedness assumption is needed for the fiber statement.
example {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (x : X)
    [IsIso (f.residueFieldMap x)] (h : ∀ x' : X, f x' = f x → x' = x) :
    IsIso (f.fiberToSpecResidueField (f x)) :=
  f.isIso_fiberToSpecResidueField_of_singleton x h

example {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (x : X)
    [IsIso (f.residueFieldMap x)] (h : ∀ x' : X, f x' = f x → x' = x) :
    f.fiberSectionOfResidueFieldIso x ≫ f.fiberToSpecResidueField (f x) = 𝟙 _ ∧
      f.fiberToSpecResidueField (f x) ≫ f.fiberSectionOfResidueFieldIso x = 𝟙 _ :=
  ⟨f.fiberSectionOfResidueFieldIso_fiberToSpecResidueField x,
    f.fiberToSpecResidueField_fiberSectionOfResidueFieldIso x h⟩

-- The rank-one input is the native Stacks theorem, over any finite flat finite-presentation map.
example {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (s : S) (hs : f.finrank s = 1) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso (f ∣_ U) :=
  exists_open_restrict_isIso_of_finrank_eq_one f s hs

example {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f]
    (s : S) (x : X) (hx : f x = s) (h : ∀ x' : X, f x' = s → x' = x)
    (hres : IsIso (f.residueFieldMap x)) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso (f ∣_ U) :=
  f.exists_isIso_morphismRestrict_of_singleton s x hx h hres

-- Finite supports may retain nilpotents and need not be flat or integral over the base.
example {Z S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (z : Z) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ (u : U), g u = p z ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (V W : (pullback p g).Opens) (v : V),
      IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd p g) ∧
      pullback.fst p g v.1 = z ∧ pullback.snd p g v.1 = u ∧
      ∀ v' : V, pullback.snd p g v'.1 = u → v' = v :=
  exists_nisnevich_isCompl_of_quasiFiniteAt p rfl (p.quasiFiniteAt z)

-- This instance includes every nonreduced or disconnected affine base, without extra hypotheses.
example (R : CommRingCat.{u}) (s : Spec R) :
    ∃ U : (Spec R).Opens, s ∈ U ∧ IsIso ((𝟙 (Spec R)) ∣_ U) :=
  Scheme.Hom.exists_isIso_morphismRestrict_of_singleton (𝟙 (Spec R)) s s rfl
    (fun _ h ↦ h) inferInstance
