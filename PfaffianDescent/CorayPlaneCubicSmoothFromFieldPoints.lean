import PfaffianDescent.CorayPlaneCubicJacobianSmooth
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! SOURCE ONLY / UNVERIFIED149. Actual residue-field maximal-ideal argument
constructs plane Jacobian covers from pointwise nonsingularity, then the native
Fin3 presentation constructs Smooth. Euler's identity is used without division
by3, so characteristic3 is retained. The generic original-cubic caller below
constructs the pointwise input internally. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Nonsingularity of the SAME plane equation at every normalized point over
all coefficient-field extensions DERIVES actual partial unit ideals on every
chart. The ring quotient/residue field and native original chart are literal. -/
theorem planeCubic_chart_partial_span_top_of_fieldPoints
    {k : Type u} [Field k]
    (q : MvPolynomial (Fin 3) k) (hq : q.IsHomogeneous 3)
    (hpoint : ∀ (M : Type u) [Field M] [Algebra k M]
      (y : Fin 3 → M) (j : Fin 3), y j = 1 →
      q.eval₂ (algebraMap k M) y = 0 →
      ∃ i : Fin 3, (MvPolynomial.pderiv i q).eval₂ (algebraMap k M) y ≠ 0)
    (j : Fin 3) :
    Ideal.span (Set.range (plane_chartPDeriv q hq j)) = ⊤ := by
  classical
  by_contra hspan
  let I := equationIdeal q hq
  let D : Ideal (ChartRing I j) := Ideal.span (Set.range (plane_chartPDeriv q hq j))
  obtain ⟨Q, hQ, hDQ⟩ := Ideal.exists_le_maximal D hspan
  letI : Q.IsMaximal := hQ
  let M := ChartRing I j ⧸ Q
  letI : Field M := Ideal.Quotient.field Q
  let e : ChartRing I j →+* M := Ideal.Quotient.mk Q
  let f : k →+* M := e.comp (chartBaseMap I j)
  letI : Algebra k M := f.toAlgebra
  let y : Fin 3 → M := fun a => e (chartCoordinate I j a)
  have hyj : y j = 1 := by simp only [y, chartCoordinate_self, map_one]
  have hey : q.eval₂ (algebraMap k M) y = 0 := by
    have hz := congrArg e (eval₂_chartCoordinate_eq_zero_of_mem I j q
      (Ideal.subset_span (Set.mem_singleton q)))
    rw [MvPolynomial.hom_eval₂, map_zero] at hz
    exact hz
  have hret : ∀ a : Fin 3, a ≠ j →
      (MvPolynomial.pderiv a q).eval₂ (algebraMap k M) y = 0 := by
    intro a haj
    have hmem : plane_chartPDeriv q hq j ⟨a, haj⟩ ∈ Q :=
      hDQ (Ideal.subset_span ⟨⟨a, haj⟩, rfl⟩)
    have hz : e (plane_chartPDeriv q hq j ⟨a, haj⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    change e ((MvPolynomial.pderiv a q).eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0 at hz
    rw [MvPolynomial.hom_eval₂] at hz
    exact hz
  have heuler : (∑ a : Fin 3, y a *
      (MvPolynomial.pderiv a q).eval₂ (algebraMap k M) y) = 0 := by
    calc
      (∑ a : Fin 3, y a * (MvPolynomial.pderiv a q).eval₂ (algebraMap k M) y) =
          (∑ a : Fin 3, MvPolynomial.X a * MvPolynomial.pderiv a q).eval₂
            (algebraMap k M) y := by simp
      _ = (3 • q).eval₂ (algebraMap k M) y := by rw [hq.sum_X_mul_pderiv]
      _ = 0 := by simp [hey]
  have hsum : (∑ a : Fin 3, y a *
      (MvPolynomial.pderiv a q).eval₂ (algebraMap k M) y) =
        y j * (MvPolynomial.pderiv j q).eval₂ (algebraMap k M) y := by
    apply Finset.sum_eq_single j
    · intro a _ haj
      rw [hret a haj, mul_zero]
    · simp
  have hj : (MvPolynomial.pderiv j q).eval₂ (algebraMap k M) y = 0 := by
    rw [hsum, hyj, one_mul] at heuler
    exact heuler
  have hall : ∀ a : Fin 3, (MvPolynomial.pderiv a q).eval₂ (algebraMap k M) y = 0 := by
    intro a
    by_cases haj : a = j
    · simpa only [haj] using hj
    · exact hret a haj
  obtain ⟨a, ha⟩ := hpoint M y j hyj hey
  exact ha (hall a)

/-- Actual plane-point nonsingularity constructs native plane-curve Smooth,
using THREE variables/TWO relations and the real Jacobian-localized charts. -/
theorem planeCubic_smooth_of_normalizedFieldPoints
    {k : Type u} [Field k]
    (q : MvPolynomial (Fin 3) k) (hq : q.IsHomogeneous 3)
    (hpoint : ∀ (M : Type u) [Field M] [Algebra k M]
      (y : Fin 3 → M) (j : Fin 3), y j = 1 →
      q.eval₂ (algebraMap k M) y = 0 →
      ∃ i : Fin 3, (MvPolynomial.pderiv i q).eval₂ (algebraMap k M) y ≠ 0) :
    Smooth (hypersurfaceToBase q hq) :=
  plane_smooth_hypersurface_of_chart_pderiv_span q hq
    (planeCubic_chart_partial_span_top_of_fieldPoints q hq hpoint)

end PfaffianDescent.Coray
