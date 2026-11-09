module

import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteDescent

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.SmoothSite

universe u v w

noncomputable section

variable {S : Scheme.{u}}
variable (P : (SmoothSite S)ᵒᵖ ⥤ Type v)
variable (hprod : ∀ (n : ℕ) (Y : Fin n → SmoothSite S),
  Function.Bijective (finiteCoproductRestriction P Y))

-- Component restriction is the actual presheaf map of the scheme inclusion.
example {n : ℕ} (Y : Fin n → SmoothSite S) (s : P.obj (op (finiteCoproduct Y)))
    (i : Fin n) : finiteCoproductRestriction P Y s i =
      P.map (finiteCoproductι Y i).op s := rfl

example {n : ℕ} (Y : Fin n → SmoothSite S) :
    Presieve.ofArrows Y (finiteCoproductι Y) ∈
      nisnevichPrecoverage S (finiteCoproduct Y) :=
  finiteCoproductι_mem_nisnevichPrecoverage Y

-- The finite-product hypothesis really includes existence and uniqueness at the empty scheme.
example : Nonempty (P.obj (op (finiteCoproduct (S := S)
    (fun i : Fin 0 => Fin.elim0 i)))) := by
  obtain ⟨s, _⟩ := (hprod 0 (fun i : Fin 0 => Fin.elim0 i)).surjective
    (fun i => Fin.elim0 i)
  exact ⟨s⟩

example : Subsingleton (P.obj (op (finiteCoproduct (S := S)
    (fun i : Fin 0 => Fin.elim0 i)))) := by
  refine ⟨fun s t => (hprod 0 (fun i : Fin 0 => Fin.elim0 i)).injective ?_⟩
  exact funext (fun i => Fin.elim0 i)

variable (hsingle : ∀ {X Y : SmoothSite S} (q : Y ⟶ X),
  Presieve.singleton q ∈ nisnevichPrecoverage S X → Presieve.IsSheafFor P (.singleton q))

-- Separation is stated for an arbitrary original index universe and only a Noetherian target.
example {X : SmoothSite S} [IsNoetherian X.left] {ι : Type w}
    {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ nisnevichPrecoverage S X)
    {s t : P.obj (op X)} (h : ∀ i, P.map (f i).op s = P.map (f i).op t) : s = t :=
  sections_ext_of_nisnevich_family P hprod hsingle f hf h

variable [∀ X : SmoothSite S, IsNoetherian X.left]

example {X : SmoothSite S} {ι : Type w} {Y : ι → SmoothSite S}
    (f : ∀ i, Y i ⟶ X) (hf : Presieve.ofArrows Y f ∈ nisnevichPrecoverage S X) :
    Presieve.IsSheafFor P (Presieve.ofArrows Y f) :=
  isSheafFor_nisnevich_family_of_finiteCoproduct P hprod hsingle f hf

example : Presieve.IsSheaf (nisnevichTopology S) P :=
  isSheaf_of_singleton_of_finiteCoproduct P hprod hsingle

example : Presieve.IsSheaf (nisnevichTopology S) P ↔
    ∀ {X Y : SmoothSite S} (q : Y ⟶ X),
      Presieve.singleton q ∈ nisnevichPrecoverage S X →
        Presieve.IsSheafFor P (.singleton q) :=
  isSheaf_iff_singleton_of_finiteCoproduct P hprod
