import AllCharacteristics.FiniteSubschemeClosedImmersionPushforward
import AllCharacteristics.DisjointFiniteSubschemeUnion
import PfaffianDescent.CubicLineFiniteSubscheme
import PfaffianDescent.LinearHypersurfaceSection

/-!
# Finite line sections inside linear sections of a cubic

A finite cubic line section formed inside a parametrized projective plane can
be pushed through the plane's closed immersion into the original cubic
surface.  This is the scheme-level form needed when a line is selected inside
a hyperplane avoiding a prescribed finite subscheme.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A normalized line section of a parametrized linear section of a cubic
surface gives a rank-three finite subscheme of the original surface. -/
theorem nonempty_rankThree_finiteSubscheme_of_linearHypersurfaceSection_line
    {K : Type u} [Field K]
    (M : Matrix (Fin 4) (Fin 3) K) (N : Matrix (Fin 3) (Fin 4) K) (hNM : N * M = 1)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Fin 3) (a b : Vec K 3) (hai : a i = 1) (hbi : b i = 0)
    (ell : MvPolynomial (Fin 3) K) (hell : ell.IsHomogeneous 1)
    (hella : ell.eval a = 0) (hellb : ell.eval b = 1)
    (c : Cubic K 3)
    (hc : c.toMvPolynomial = rectangularSubstitution M p)
    (ha : c.eval a ≠ 0) :
    Nonempty (FiniteSubschemeDatum (hypersurfaceToBase p hp) 3) := by
  let q := rectangularSubstitution M p
  let hq := rectangularSubstitution_homogeneous M hp
  obtain ⟨D⟩ := cubic_line_intersection_finite_subscheme_linear_normalized
    i q hq c hc a b hai hbi ell hell hella hellb ha
  let g := linearHypersurfaceSectionι M N hNM p hp
  let D' : FiniteSubschemeDatum (g ≫ hypersurfaceToBase p hp) 3 := by
    rw [linearHypersurfaceSectionι_toBase]
    exact D
  exact ⟨finiteSubschemeDatum_pushforwardClosedImmersion g (hypersurfaceToBase p hp) D'⟩

/-- A nonzero cubic restriction to a parametrized projective plane has a
rank-three finite line section on the original cubic surface.  The proof
constructs the line on the plane cubic and pushes it through the plane's
closed immersion. -/
theorem nonempty_rankThree_finiteSubscheme_of_nonzero_linearHypersurfaceSection
    {K : Type u} [Field K] [Infinite K]
    (M : Matrix (Fin 4) (Fin 3) K) (N : Matrix (Fin 3) (Fin 4) K) (hNM : N * M = 1)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hne : rectangularSubstitution M p ≠ 0) :
    Nonempty (FiniteSubschemeDatum (hypersurfaceToBase p hp) 3) := by
  let q := rectangularSubstitution M p
  let hq := rectangularSubstitution_homogeneous M hp
  obtain ⟨D⟩ := nonempty_rankThree_finiteSubscheme_of_nonzero_homogeneous_cubic_equation
    (by decide : 2 ≤ 3) q hq hne
  let g := linearHypersurfaceSectionι M N hNM p hp
  let D' : FiniteSubschemeDatum (g ≫ hypersurfaceToBase p hp) 3 := by
    rw [linearHypersurfaceSectionι_toBase]
    exact D
  exact ⟨finiteSubschemeDatum_pushforwardClosedImmersion g (hypersurfaceToBase p hp) D'⟩

/-- If a parametrized plane avoids an arbitrary map to a cubic surface and
the cubic has nonzero restriction to that plane, a rank-three line section is
disjoint from the map's range. -/
theorem exists_rankThree_finiteSubscheme_disjoint_from_map_of_nonzero_linearHypersurfaceSection
    {K : Type u} [Field K] [Infinite K]
    (M : Matrix (Fin 4) (Fin 3) K) (N : Matrix (Fin 3) (Fin 4) K) (hNM : N * M = 1)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp)
    (havoid : Disjoint (Set.range i)
      (Set.range (linearHypersurfaceSectionι M N hNM p hp)))
    (hne : rectangularSubstitution M p ≠ 0) :
    ∃ D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3,
      Disjoint (Set.range i)
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)) := by
  let q := rectangularSubstitution M p
  let hq := rectangularSubstitution_homogeneous M hp
  obtain ⟨D⟩ := nonempty_rankThree_finiteSubscheme_of_nonzero_homogeneous_cubic_equation
    (by decide : 2 ≤ 3) q hq hne
  let g := linearHypersurfaceSectionι M N hNM p hp
  let D' : FiniteSubschemeDatum (g ≫ hypersurfaceToBase p hp) 3 := by
    rw [linearHypersurfaceSectionι_toBase]
    exact D
  let D₃ := finiteSubschemeDatum_pushforwardClosedImmersion g (hypersurfaceToBase p hp) D'
  exact ⟨D₃, disjoint_range_pushforwardClosedImmersion_of_disjoint_range
    i g (hypersurfaceToBase p hp) D' havoid⟩

/-- If a parametrized plane avoids a degree-ten finite datum and the cubic
does not vanish identically on that plane, a rank-three line section can be
chosen disjoint from the degree-ten datum. -/
theorem exists_rankThree_finiteSubscheme_disjoint_of_nonzero_linearHypersurfaceSection
    {K : Type u} [Field K] [Infinite K]
    (M : Matrix (Fin 4) (Fin 3) K) (N : Matrix (Fin 3) (Fin 4) K) (hNM : N * M = 1)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (havoid : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (linearHypersurfaceSectionι M N hNM p hp)))
    (hne : rectangularSubstitution M p ≠ 0) :
    ∃ D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3,
      Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)) := by
  let q := rectangularSubstitution M p
  let hq := rectangularSubstitution_homogeneous M hp
  obtain ⟨D⟩ := nonempty_rankThree_finiteSubscheme_of_nonzero_homogeneous_cubic_equation
    (by decide : 2 ≤ 3) q hq hne
  let g := linearHypersurfaceSectionι M N hNM p hp
  let D' : FiniteSubschemeDatum (g ≫ hypersurfaceToBase p hp) 3 := by
    rw [linearHypersurfaceSectionι_toBase]
    exact D
  let D₃ := finiteSubschemeDatum_pushforwardClosedImmersion g (hypersurfaceToBase p hp) D'
  refine ⟨D₃, ?_⟩
  apply finiteSubschemeDatum_disjoint_pushforwardClosedImmersion_of_disjoint_range g
    (hypersurfaceToBase p hp) D₁₀ D'
  exact havoid

/-- Two disjoint parametrized planes avoiding a degree-ten datum, on each of
which the cubic has nonzero restriction, provide the two disjoint rank-three
line sections required for the degree-sixteen starting datum. -/
theorem exists_two_rankThree_finiteSubschemes_disjoint_of_nonzero_linearHypersurfaceSections
    {K : Type u} [Field K] [Infinite K]
    (M₁ : Matrix (Fin 4) (Fin 3) K) (N₁ : Matrix (Fin 3) (Fin 4) K) (hN₁M₁ : N₁ * M₁ = 1)
    (M₂ : Matrix (Fin 4) (Fin 3) K) (N₂ : Matrix (Fin 3) (Fin 4) K) (hN₂M₂ : N₂ * M₂ = 1)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (hD₁₀g₁ : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (linearHypersurfaceSectionι M₁ N₁ hN₁M₁ p hp)))
    (hD₁₀g₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (linearHypersurfaceSectionι M₂ N₂ hN₂M₂ p hp)))
    (hg₁g₂ : Disjoint (Set.range (linearHypersurfaceSectionι M₁ N₁ hN₁M₁ p hp))
      (Set.range (linearHypersurfaceSectionι M₂ N₂ hN₂M₂ p hp)))
    (hne₁ : rectangularSubstitution M₁ p ≠ 0)
    (hne₂ : rectangularSubstitution M₂ p ≠ 0) :
    ∃ (D₃ D₃' : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3),
      Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)) ∧
      Disjoint (Set.range (disjointSpecUnionMap
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃')) := by
  let q₁ := rectangularSubstitution M₁ p
  let hq₁ := rectangularSubstitution_homogeneous M₁ hp
  obtain ⟨E₁⟩ := nonempty_rankThree_finiteSubscheme_of_nonzero_homogeneous_cubic_equation
    (by decide : 2 ≤ 3) q₁ hq₁ hne₁
  let g₁ := linearHypersurfaceSectionι M₁ N₁ hN₁M₁ p hp
  let E₁' : FiniteSubschemeDatum (g₁ ≫ hypersurfaceToBase p hp) 3 := by
    rw [linearHypersurfaceSectionι_toBase]
    exact E₁
  let D₃ := finiteSubschemeDatum_pushforwardClosedImmersion g₁ (hypersurfaceToBase p hp) E₁'
  let q₂ := rectangularSubstitution M₂ p
  let hq₂ := rectangularSubstitution_homogeneous M₂ hp
  obtain ⟨E₂⟩ := nonempty_rankThree_finiteSubscheme_of_nonzero_homogeneous_cubic_equation
    (by decide : 2 ≤ 3) q₂ hq₂ hne₂
  let g₂ := linearHypersurfaceSectionι M₂ N₂ hN₂M₂ p hp
  let E₂' : FiniteSubschemeDatum (g₂ ≫ hypersurfaceToBase p hp) 3 := by
    rw [linearHypersurfaceSectionι_toBase]
    exact E₂
  let D₃' := finiteSubschemeDatum_pushforwardClosedImmersion g₂ (hypersurfaceToBase p hp) E₂'
  refine ⟨D₃, D₃', ?_, ?_⟩
  · apply finiteSubschemeDatum_disjoint_pushforwardClosedImmersion_of_disjoint_range g₁
      (hypersurfaceToBase p hp) D₁₀ E₁'
    exact hD₁₀g₁
  · have hD₃g₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃))
        (Set.range g₂) := by
      exact (disjoint_range_pushforwardClosedImmersion_of_disjoint_range g₂ g₁
        (hypersurfaceToBase p hp) E₁' hg₁g₂.symm).symm
    have hqg₂ : Disjoint (Set.range (disjointSpecUnionMap
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
        (Set.range g₂) :=
      disjoint_disjointSpecUnionMap_range_of_disjoint
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃) g₂ hD₁₀g₂ hD₃g₂
    exact disjoint_range_pushforwardClosedImmersion_of_disjoint_range
      (disjointSpecUnionMap
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃))
      g₂ (hypersurfaceToBase p hp) E₂' hqg₂

end PfaffianDescent
