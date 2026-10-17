import PfaffianDescent.CorayOriginalLeastWindowInternalNaturalAiAssembly
import PfaffianDescent.CorayMinimalPointSelection
import AllCharacteristics.VoisinDegreeTenReduction
import Mathlib.Data.Nat.Find

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Choose the ORIGINAL degree interpolation window internally by the
first genus bound above d. No interpolation index/window is supplied. -/
private theorem originalDegree_ge_four_exists_interpolationWindow001
    (d : ℕ) (hd : 4 ≤ d) :
    ∃ n : ℕ, 2 ≤ n ∧ 1 + 3 * n.choose 2 ≤ d ∧ d < 1 + 3 * (n + 1).choose 2 := by
  classical
  have hStep : (d + 1).choose 2 = d + d.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' d 1
  have hex : ∃ n : ℕ, d < 1 + 3 * (n + 1).choose 2 := by
    refine ⟨d, ?_⟩
    rw [hStep]
    omega
  let n := Nat.find hex
  have hUpper : d < 1 + 3 * (n + 1).choose 2 := Nat.find_spec hex
  have hn : 2 ≤ n := by
    by_contra h
    have hChoose : (n + 1).choose 2 ≤ (2 : ℕ).choose 2 :=
      Nat.choose_le_choose 2 (by omega)
    norm_num at hChoose
    omega
  have hLower : 1 + 3 * n.choose 2 ≤ d := by
    have hPrev : ¬ d < 1 + 3 * ((n - 1) + 1).choose 2 :=
      Nat.find_min hex (show n - 1 < Nat.find hex by change n - 1 < n; omega)
    rw [show n - 1 + 1 = n by omega] at hPrev
    omega
  exact ⟨n, hn, hLower, hUpper⟩

/-- Internal original Coray closure from an ACTUAL degree-one cycle.
A rational section gives its actual closed degree-one point. Otherwise
actual cycle arithmetic chooses the least ORIGINAL coprime-degree point,
quadratic descent derives its degree>=4, and the interpolation index/window
is selected internally. Genuine natural Ai gives its exact FULL degree4 or10.
No Coray assumption, least point, degree window, auxiliary/tangent/regularity,
chosen curve, normalization or desired closed-point outcome is supplied. -/
theorem coray_originalDegreeOneCycle_exists_closedPoint_one_four_or_ten_internal001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ P : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree P.1 = 1 ∨
      (hypersurfaceToBase p hp).residueDegree P.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree P.1 = 10 := by
  classical
  by_cases hSection : ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _
  · obtain ⟨s, hs⟩ := hSection
    obtain ⟨P, hP⟩ := closedPoint_degree_one_of_section (hypersurfaceToBase p hp) s hs
    exact ⟨P, Or.inl hP⟩
  · obtain ⟨P, hPcop, hLeast⟩ :=
      zeroCycle_degree_one_has_minimal_coprime_closedPoint (hypersurfaceToBase p hp) z hz
    have hDegree : 4 ≤ (hypersurfaceToBase p hp).residueDegree P.1 :=
      cubic_coprime_point_degree_ge_four_of_no_section p hp hSection P hPcop
    obtain ⟨n, _hn, hLower, hUpper⟩ :=
      originalDegree_ge_four_exists_interpolationWindow001
        ((hypersurfaceToBase p hp).residueDegree P.1) hDegree
    rcases coray_leastOriginalPoint_noSection_window_eq_four_or_ten_internalAi001
        p hp hp0 P hPcop hLeast hSection n hLower hUpper with hFour | hTen
    · exact ⟨P, Or.inr (Or.inl hFour.1)⟩
    · exact ⟨P, Or.inr (Or.inr hTen.1)⟩

/-- The original characteristic-zero Coray interface is proved internally
from its actual cubic and actual degree-one cycle inputs. The definition
is reused only as the output proposition; no external Coray theorem or
uniform degree-reduction hypothesis is invoked. -/
theorem internalCorayDegreeOneFourOrTenFor_charZero001
    {K : Type u} [Field K] [CharZero K] : AllCharacteristics.CorayDegreeOneFourOrTenFor K := by
  intro p hp hp0 hSmooth z hz
  letI : Smooth (hypersurfaceToBase p hp) := hSmooth
  exact coray_originalDegreeOneCycle_exists_closedPoint_one_four_or_ten_internal001 p hp hp0 z hz

end PfaffianDescent.Coray
