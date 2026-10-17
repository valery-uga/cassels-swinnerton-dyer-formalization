import PfaffianDescent.HomogeneousProjection
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

namespace PfaffianDescent
open MvPolynomial
section
variable {K σ : Type*} [Field K]

/-- The top component of a product is the product of the top components,
with any valid upper bounds for the two total degrees. -/
lemma homogeneousComponent_top_mul (p q : MvPolynomial σ K) (m n : ℕ)
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) :
    homogeneousComponent (m+n) (p*q) = homogeneousComponent m p * homogeneousComponent n q := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d.degree = m+n
  · rw [coeff_homogeneousComponent, if_pos hd, coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    by_cases ha : coeff ab.1 p = 0
    · simp [coeff_homogeneousComponent, ha]
    by_cases hb : coeff ab.2 q = 0
    · simp [coeff_homogeneousComponent, hb]
    have ha' : ab.1.degree ≤ m := (le_totalDegree (mem_support_iff.mpr ha)).trans hp
    have hb' : ab.2.degree ≤ n := (le_totalDegree (mem_support_iff.mpr hb)).trans hq
    have hab' : ab.1 + ab.2 = d := Finset.mem_antidiagonal.mp hab
    have habd : ab.1.degree + ab.2.degree = m+n := by rw [← map_add, hab', hd]
    have ham : ab.1.degree = m := by omega
    have hbn : ab.2.degree = n := by omega
    simp [coeff_homogeneousComponent, ham, hbn]
  · rw [coeff_homogeneousComponent, if_neg hd]
    exact (((homogeneousComponent_isHomogeneous m p).mul
      (homogeneousComponent_isHomogeneous n q)).coeff_eq_zero hd).symm

/-- A nonzero polynomial has a nonzero highest homogeneous component. -/
lemma top_homogeneousComponent_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    (fun d => d.sum fun _ e => e)
  have hdegree : d.degree = p.totalDegree := he.symm
  intro hz
  have hc := congrArg (coeff d) hz
  rw [coeff_homogeneousComponent, if_pos hdegree, coeff_zero] at hc
  exact mem_support_iff.mp hd hc

/-- A homogeneous product equals the product of its two highest components. -/
lemma homogeneous_product_eq_top_components {p q : MvPolynomial σ K} {d : ℕ}
    (hp : p ≠ 0) (hq : q ≠ 0) (h : (p*q).IsHomogeneous d) :
    p*q = homogeneousComponent p.totalDegree p * homogeneousComponent q.totalDegree q := by
  have hd : p.totalDegree + q.totalDegree = d :=
    (totalDegree_mul_of_isDomain hp hq).symm.trans (h.totalDegree (mul_ne_zero hp hq))
  rw [← homogeneousComponent_top_mul p q _ _ le_rfl le_rfl, hd,
    homogeneousComponent_eq_self h]

/-- The order of a nonzero homogeneous polynomial, considered as a formal
power series, is its homogeneous degree. -/
lemma coe_order_of_homogeneous {p : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) (hp0 : p ≠ 0) :
    (p : MvPowerSeries σ K).order = d := by
  rw [MvPowerSeries.order_eq_nat]
  constructor
  · obtain ⟨a, ha⟩ := exists_coeff_ne_zero hp0
    refine ⟨a, ?_, ?_⟩
    · simpa using ha
    · by_contra hne
      exact ha (hp.coeff_eq_zero hne)
  · intro a ha
    rw [MvPolynomial.coeff_coe]
    exact hp.coeff_eq_zero (ne_of_lt ha)

/-- The order of a nonzero polynomial is at most its total degree. -/
lemma coe_order_le_totalDegree {p : MvPolynomial σ K} (hp0 : p ≠ 0) :
    (p : MvPowerSeries σ K).order ≤ p.totalDegree := by
  obtain ⟨a, ha⟩ := exists_coeff_ne_zero (top_homogeneousComponent_ne_zero hp0)
  have hdegree : a.degree = p.totalDegree := by
    by_contra hne
    have hz : (0 : K) ≠ 0 := by
      simpa [coeff_homogeneousComponent, hne] using ha
    exact hz rfl
  have hpa : coeff a p ≠ 0 := by
    rw [coeff_homogeneousComponent, hdegree] at ha
    simpa using ha
  have hle := MvPowerSeries.order_le (f := (p : MvPowerSeries σ K)) (by simpa using hpa)
  simpa [hdegree] using hle

/-- A nonzero degree-zero homogeneous form over a field is a unit. -/
lemma isUnit_of_homogeneous_zero {p : MvPolynomial σ K}
    (hp : p.IsHomogeneous 0) (hp0 : p ≠ 0) : IsUnit p := by
  rw [← homogeneousComponent_eq_self hp, homogeneousComponent_zero]
  apply RingHom.isUnit_map
  exact isUnit_iff_ne_zero.mpr (by
    intro h
    apply hp0
    rw [← homogeneousComponent_eq_self hp, homogeneousComponent_zero, h, C_0])

/-- A positive-degree homogeneous form over a field is not a unit. -/
lemma homogeneous_not_isUnit_of_pos_degree_of_eval_zero {p : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : 0 < d) : ¬ IsUnit p := by
  intro hunit
  obtain ⟨a, ha⟩ := isUnit_iff_dvd_one.mp hunit
  have hzeroCoeff : coeff 0 p = 0 :=
    hp.coeff_eq_zero (d := (0 : σ →₀ ℕ)) (by
      simpa using (Nat.ne_of_gt hd).symm)
  have hzeroEval : eval₂Hom (RingHom.id K) (0 : σ → K) p = 0 := by
    rw [eval₂Hom_zero_apply, constantCoeff_eq, hzeroCoeff]
    rfl
  have he := congrArg (eval₂Hom (RingHom.id K) (0 : σ → K)) ha
  rw [map_mul, hzeroEval, zero_mul] at he
  simpa using he

/-- Factors of a nonzero homogeneous polynomial over a field are homogeneous.
The lowest nonzero degrees add by the power-series order formula, while the
highest degrees add by `totalDegree_mul_of_isDomain`; equality forces every
factor to have one degree. -/
lemma homogeneous_factor_of_homogeneous_product
    {p q : MvPolynomial σ K} {d : ℕ}
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (h : (p * q).IsHomogeneous d) :
    p.IsHomogeneous p.totalDegree ∧ q.IsHomogeneous q.totalDegree := by
  let P : MvPowerSeries σ K := p
  let Q : MvPowerSeries σ K := q
  have hP0 : P ≠ 0 := by simpa [P] using hp0
  have hQ0 : Q ≠ 0 := by simpa [Q] using hq0
  let op : ℕ := P.order.toNat
  let oq : ℕ := Q.order.toNat
  have hop : P.order = (op : ℕ∞) := by
    exact (MvPowerSeries.ne_zero_iff_order_finite.mp hP0).symm
  have hoq : Q.order = (oq : ℕ∞) := by
    exact (MvPowerSeries.ne_zero_iff_order_finite.mp hQ0).symm
  have hP_le : op ≤ p.totalDegree := by
    have hle : P.order ≤ p.totalDegree := by simpa [P] using coe_order_le_totalDegree hp0
    rw [hop] at hle
    exact_mod_cast hle
  have hQ_le : oq ≤ q.totalDegree := by
    have hle : Q.order ≤ q.totalDegree := by simpa [Q] using coe_order_le_totalDegree hq0
    rw [hoq] at hle
    exact_mod_cast hle
  have horder : P.order + Q.order = d := by
    rw [← MvPowerSeries.order_mul, ← MvPolynomial.coe_mul]
    simpa [P, Q] using coe_order_of_homogeneous h (mul_ne_zero hp0 hq0)
  rw [hop, hoq] at horder
  have horder' : op + oq = d := by exact_mod_cast horder
  have hdegree : p.totalDegree + q.totalDegree = d := by
    exact (totalDegree_mul_of_isDomain hp0 hq0).symm.trans
      (h.totalDegree (mul_ne_zero hp0 hq0))
  have hP_eq : op = p.totalDegree := by omega
  have hQ_eq : oq = q.totalDegree := by omega
  have hP_order : P.order = p.totalDegree := by
    rw [hop, hP_eq]
  have hQ_order : Q.order = q.totalDegree := by
    rw [hoq, hQ_eq]
  have hpcomp : p = homogeneousComponent p.totalDegree p := by
    ext a
    by_cases ha : a.degree = p.totalDegree
    · simp [coeff_homogeneousComponent, ha]
    · rw [coeff_homogeneousComponent, if_neg ha]
      by_cases halt : a.degree < p.totalDegree
      · have hz := MvPowerSeries.coeff_of_lt_order (f := P) (by simpa [hP_order] using halt)
        simpa [P] using hz
      · exact coeff_eq_zero_of_totalDegree_lt
          (lt_of_le_of_ne (Nat.le_of_not_gt halt) (Ne.symm ha))
  have hqcomp : q = homogeneousComponent q.totalDegree q := by
    ext a
    by_cases ha : a.degree = q.totalDegree
    · simp [coeff_homogeneousComponent, ha]
    · rw [coeff_homogeneousComponent, if_neg ha]
      by_cases halt : a.degree < q.totalDegree
      · have hz := MvPowerSeries.coeff_of_lt_order (f := Q) (by simpa [hQ_order] using halt)
        simpa [Q] using hz
      · exact coeff_eq_zero_of_totalDegree_lt
          (lt_of_le_of_ne (Nat.le_of_not_gt halt) (Ne.symm ha))
  constructor
  · have ht : (homogeneousComponent p.totalDegree p).IsHomogeneous p.totalDegree :=
      homogeneousComponent_isHomogeneous p.totalDegree p
    rw [← hpcomp] at ht
    exact ht
  · have ht : (homogeneousComponent q.totalDegree q).IsHomogeneous q.totalDegree :=
      homogeneousComponent_isHomogeneous q.totalDegree q
    rw [← hqcomp] at ht
    exact ht

/-- The affine normalization `X j = 1` does not kill a nonzero homogeneous
form.  A hypothetical factor would contradict the homogeneity of factors of
a homogeneous product. -/
lemma homogeneous_not_dvd_X_sub_one {p : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) (hp0 : p ≠ 0) (j : σ) :
    ¬ (X j - 1 : MvPolynomial σ K) ∣ p := by
  classical
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hq0 : q ≠ 0 := by
    intro hq0
    apply hp0
    rw [hq, hq0, mul_zero]
  have hs : Finsupp.single j 1 ≠ (0 : σ →₀ ℕ) :=
    Finsupp.single_ne_zero.mpr one_ne_zero
  have hX0 : (X j - 1 : MvPolynomial σ K) ≠ 0 := by
    intro hx
    have hcoeff := congrArg (coeff (0 : σ →₀ ℕ)) hx
    norm_num [MvPolynomial.coeff_sub, MvPolynomial.coeff_X] at hcoeff
  have hprod : ((X j - 1 : MvPolynomial σ K) * q).IsHomogeneous d := by
    rw [← hq]
    exact hp
  have hfac := homogeneous_factor_of_homogeneous_product hX0 hq0 hprod
  have hdegree : (X j - 1 : MvPolynomial σ K).totalDegree = 1 := by
    apply le_antisymm
    · exact le_trans (MvPolynomial.totalDegree_sub _ _)
        (by simp [MvPolynomial.totalDegree_X])
    · have hmem : Finsupp.single j 1 ∈ (X j - 1 : MvPolynomial σ K).support := by
        rw [MvPolynomial.mem_support_iff]
        rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X]
        rw [show (1 : MvPolynomial σ K) = C 1 by rfl, coeff_C]
        simp [Ne.symm hs]
      simpa using (le_totalDegree hmem)
  have hhom : (X j - 1 : MvPolynomial σ K).IsHomogeneous 1 := by
    rw [← hdegree]
    exact hfac.1
  have hcoeff := hhom.coeff_eq_zero (d := (0 : σ →₀ ℕ)) (by simp)
  norm_num [MvPolynomial.coeff_sub, MvPolynomial.coeff_X] at hcoeff

end
end PfaffianDescent
