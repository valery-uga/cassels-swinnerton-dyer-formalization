import PfaffianDescent.AffinePointKoszulOverlap
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# An affine cover adapted to a closed point

The distinguished member is a prescribed affine neighborhood of the point.
Every other member avoids it. This is the cover used to compare a point's
Koszul resolution with the augmented Cech resolution.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PfaffianDescent.PointAdaptedAffineCover

universe u

variable {X : Scheme.{u}}

/-- Affine opens avoiding the chosen point, with a distinguished extra index. -/
abbrev Index (X : Scheme.{u}) (x : X) :=
  Option {V : X.Opens // IsAffineOpen V ∧ x ∉ V}

/-- `none` denotes the chosen parameter neighborhood. -/
def opens (U : X.Opens) (x : X) : Index X x → X.Opens
  | none => U
  | some V => V.val

@[simp] theorem opens_none (U : X.Opens) (x : X) : opens U x none = U := rfl

@[simp] theorem opens_some (U : X.Opens) (x : X)
    (V : {V : X.Opens // IsAffineOpen V ∧ x ∉ V}) :
    opens U x (some V) = V.val := rfl

theorem isAffineOpen (U : X.Opens) (hU : IsAffineOpen U) (x : X)
    (i : Index X x) : IsAffineOpen (opens U x i) := by
  cases i with
  | none => exact hU
  | some V => exact V.prop.1

theorem point_not_mem_of_ne_none (U : X.Opens) (x : X)
    (i : Index X x) (hi : i ≠ none) : x ∉ opens U x i := by
  cases i with
  | none => exact (hi rfl).elim
  | some V => exact V.prop.2

/-- Closedness supplies affine neighborhoods avoiding the point, so the
chosen neighborhood and these opens cover the whole scheme. -/
theorem covers (U : X.Opens) (x : X) (hx : x ∈ U)
    (hxclosed : IsClosed ({x} : Set X)) :
    (⨆ i : Index X x, opens U x i) = ⊤ := by
  apply top_unique
  intro z _
  by_cases hz : z = x
  · subst z
    exact (le_iSup (opens U x) none) hx
  · have hzc : z ∈ ({x} : Set X)ᶜ := by simpa using hz
    obtain ⟨V, hV, hzV, hVc⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (show z ∈ (⟨({x} : Set X)ᶜ, hxclosed.isOpen_compl⟩ : X.Opens) from hzc)
    have hxV : x ∉ V := by
      intro h
      exact (hVc h) (Set.mem_singleton x)
    exact (le_iSup (opens U x) (some ⟨V, hV, hxV⟩)) hzV

/-- Every overlap involving an index other than the distinguished one
avoids the point. -/
theorem point_not_mem_inter (U : X.Opens) (x : X)
    (i j : Index X x) (hi : i ≠ none) :
    x ∉ opens U x i ⊓ opens U x j := by
  exact fun h => point_not_mem_of_ne_none U x i hi h.1

/-- On schemes with affine diagonal, all pair intersections in this cover
are affine. -/
theorem isAffineOpen_inter
    [IsAffineHom (CategoryTheory.Limits.pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (i j : Index X x) :
    IsAffineOpen (opens U x i ⊓ opens U x j) :=
  (isAffineOpen U hU x i).inf (isAffineOpen U hU x j)

/-- The actual overlap of the parameter neighborhood and any other cover
member has a unit ideal of restricted parameters. -/
theorem parameter_span_eq_top_on_overlap
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (i : Index X x) (hi : i ≠ none) :
    Ideal.span ({X.presheaf.map (homOfLE
        (inf_le_left : U ⊓ opens U x i ≤ U)).op q,
      X.presheaf.map (homOfLE
        (inf_le_left : U ⊓ opens U x i ≤ U)).op f} :
      Set Γ(X, U ⊓ opens U x i)) = ⊤ := by
  apply affine_restricted_pair_span_eq_top_away_point U x q f haway
    (U ⊓ opens U x i) (hU.inf (isAffineOpen U hU x i)) inf_le_left
  exact fun h => point_not_mem_of_ne_none U x i hi h.2

/-- Hence a first lift on these specific cover overlaps exists without
choosing or assuming any extra local equations. -/
theorem exists_parameter_overlap_lift
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (i : Index X x) (hi : i ≠ none)
    (t : Γ(X, U ⊓ opens U x i)) :
    ∃ v : Γ(X, U ⊓ opens U x i) × Γ(X, U ⊓ opens U x i),
      twoGeneratorLast
        (X.presheaf.map (homOfLE (inf_le_left : U ⊓ opens U x i ≤ U)).op q)
        (X.presheaf.map (homOfLE (inf_le_left : U ⊓ opens U x i ≤ U)).op f) v = t := by
  apply exists_affine_point_koszul_overlap_lift U x q f haway
    (U ⊓ opens U x i) (hU.inf (isAffineOpen U hU x i)) inf_le_left
    (fun h => point_not_mem_of_ne_none U x i hi h.2) t

/-- All finite intersections meeting another cover member have the same
unit-ideal property. This includes the triple and quadruple overlaps used
for the transgression and its cocycle identity. -/
theorem parameter_span_eq_top_on_multiple_overlap
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {ι : Type*} [Finite ι] [Nonempty ι]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (i : ι → Index X x) (j : ι) (hj : i j ≠ none) :
    Ideal.span ({X.presheaf.map (homOfLE
        (inf_le_left : U ⊓ ⨅ k, opens U x (i k) ≤ U)).op q,
      X.presheaf.map (homOfLE
        (inf_le_left : U ⊓ ⨅ k, opens U x (i k) ≤ U)).op f} :
      Set Γ(X, U ⊓ ⨅ k, opens U x (i k))) = ⊤ := by
  apply affine_restricted_pair_span_eq_top_away_point U x q f haway
    (U ⊓ ⨅ k, opens U x (i k))
    (hU.inf (IsAffineOpen.iInf (fun k => isAffineOpen U hU x (i k)))) inf_le_left
  intro h
  have hle : (⨅ k, opens U x (i k)) ≤ opens U x (i j) := iInf_le _ j
  exact point_not_mem_of_ne_none U x (i j) hj (hle h.2)

end PfaffianDescent.PointAdaptedAffineCover
