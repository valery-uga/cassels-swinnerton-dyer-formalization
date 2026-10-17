import AllCharacteristics.CycleDegrees
import PfaffianDescent.SchemeModuleFiniteSignedPointTensorIteration
import PfaffianDescent.CorayDegreeReductionArithmetic

/-! Actual signed cycles on the SAME scheme give actual signed point words.
These are algebraic construction lemmas, not primitive original-surface
Coray callers. The cycle inputs are genuine signed cycles ON the intended
normalization; constructing them from the original surface point/hyperplane
is still required and is not erased by any theorem here. Original pi residue
degrees remain unchanged. SOURCE ONLY / UNVERIFIED; root alone compiles. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The literal signed point cycle specified by the same operation list.
This records multiplicities, including repeated points and both signs. -/
def signedPointTensorOperationsZeroCycle
    (ops : List (closedPoints X × Bool)) : ZeroCycle X :=
  (ops.map (fun operation => Finsupp.single operation.1
    (if operation.2 then (1 : ℤ) else -1))).sum

/-- Encode one INTEGER coefficient using actual repeated positive dual or
negative ideal operations. No point extension or scalar transport occurs. -/
def signedPointTensorCoefficientOperations
    (P : closedPoints X) : ℤ → List (closedPoints X × Bool)
  | .ofNat n => List.replicate n (P, true)
  | .negSucc n => List.replicate (n + 1) (P, false)

theorem signedPointTensorOperationsZeroCycle_append
    (ops₁ ops₂ : List (closedPoints X × Bool)) :
    signedPointTensorOperationsZeroCycle (ops₁ ++ ops₂) =
      signedPointTensorOperationsZeroCycle ops₁ + signedPointTensorOperationsZeroCycle ops₂ := by
  simp only [signedPointTensorOperationsZeroCycle, List.map_append, List.sum_append]

/-- Every coefficient is represented by its actual signed repeated point. -/
theorem signedPointTensorCoefficientOperations_zeroCycle
    (P : closedPoints X) (a : ℤ) :
    signedPointTensorOperationsZeroCycle (signedPointTensorCoefficientOperations P a) =
      Finsupp.single P a := by
  cases a with
  | ofNat n =>
    simp [signedPointTensorCoefficientOperations, signedPointTensorOperationsZeroCycle,
      List.map_replicate, List.sum_replicate, Finsupp.smul_single, nsmul_eq_mul]
  | negSucc n =>
    simp [signedPointTensorCoefficientOperations, signedPointTensorOperationsZeroCycle,
      List.map_replicate, List.sum_replicate, Finsupp.smul_single, nsmul_eq_mul,
      Int.negSucc_eq, neg_add, add_comm]

/-- The FULL signed-word weight equals the actual original-pi cycle degree.
This is an identity for actual scheme residue degrees, not a divisor-degree
certificate or an abstract field-replacement convention. -/
theorem signedPointTensorOperationsZeroCycle_degree
    (pi : X ⟶ Spec (CommRingCat.of K)) (ops : List (closedPoints X × Bool)) :
    ZeroCycle.degree pi (signedPointTensorOperationsZeroCycle ops) =
      schemeModuleSignedClosedPointTensorWeightSum pi ops := by
  induction ops with
  | nil => simp [signedPointTensorOperationsZeroCycle, schemeModuleSignedClosedPointTensorWeightSum]
  | cons operation ops ih =>
    rcases operation with ⟨P, sign⟩
    change ZeroCycle.degree pi
        (Finsupp.single P (if sign then (1 : ℤ) else -1) +
          signedPointTensorOperationsZeroCycle ops) =
      schemeModuleSignedClosedPointTensorWeight pi (P, sign) +
        schemeModuleSignedClosedPointTensorWeightSum pi ops
    rw [map_add, ZeroCycle.degree_single, ih]
    cases sign <;> simp [schemeModuleSignedClosedPointTensorWeight]

/-- Construct a finite literal word from ANY actual signed cycle, preserving
both the cycle itself and its FULL original-pi degree. No sign/effectivity
or nonzero-section premise is required. -/
theorem zeroCycle_exists_signedPointTensorOperations
    (pi : X ⟶ Spec (CommRingCat.of K)) (z : ZeroCycle X) :
    ∃ ops : List (closedPoints X × Bool),
      signedPointTensorOperationsZeroCycle ops = z ∧
        schemeModuleSignedClosedPointTensorWeightSum pi ops = ZeroCycle.degree pi z := by
  classical
  have h : ∃ ops : List (closedPoints X × Bool), signedPointTensorOperationsZeroCycle ops = z := by
    induction z using Finsupp.induction with
    | zero => exact ⟨[], by simp [signedPointTensorOperationsZeroCycle]⟩
    | @single_add P a z hP ha ih =>
      obtain ⟨ops, hops⟩ := ih
      refine ⟨signedPointTensorCoefficientOperations P a ++ ops, ?_⟩
      rw [signedPointTensorOperationsZeroCycle_append,
        signedPointTensorCoefficientOperations_zeroCycle, hops]
  obtain ⟨ops, hops⟩ := h
  refine ⟨ops, hops, ?_⟩
  rw [← signedPointTensorOperationsZeroCycle_degree, hops]

/-- Actual Bezout combination of TWO actual signed cycles on SAME X. A
canonical divisor is unnecessary for the degree-realization used below. -/
def zeroCycleDegreeGcdCombination
    (d e : ℕ) (zD zE : ZeroCycle X) : ZeroCycle X :=
  Nat.gcdA d e • zD + Nat.gcdB d e • zE

theorem zeroCycleDegreeGcdCombination_degree
    (pi : X ⟶ Spec (CommRingCat.of K)) (d e : ℕ) (zD zE : ZeroCycle X)
    (hD : ZeroCycle.degree pi zD = (d : ℤ))
    (hE : ZeroCycle.degree pi zE = (e : ℤ)) :
    ZeroCycle.degree pi (zeroCycleDegreeGcdCombination d e zD zE) = (Nat.gcd d e : ℤ) := by
  simp only [zeroCycleDegreeGcdCombination, map_add, map_smul, hD, hE, smul_eq_mul]
  have h := Nat.gcd_eq_gcd_ab d e
  simpa only [mul_comm] using h.symm

/-- A chosen nonnegative multiple of the actual two-cycle gcd is represented
by an actual signed word. This constructs its operations; the two cycles
must already exist on X, not just on a different surface or base extension. -/
theorem exists_signedPointTensorOperations_weight_eq_multiple_gcd
    (pi : X ⟶ Spec (CommRingCat.of K)) (d e : ℕ) (zD zE : ZeroCycle X)
    (hD : ZeroCycle.degree pi zD = (d : ℤ))
    (hE : ZeroCycle.degree pi zE = (e : ℤ))
    (theta : ℕ) (htheta : Nat.gcd d e ∣ theta) :
    ∃ ops : List (closedPoints X × Bool),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) := by
  obtain ⟨t, ht⟩ := htheta
  obtain ⟨ops, _hcycle, hweight⟩ := zeroCycle_exists_signedPointTensorOperations pi
    ((t : ℤ) • zeroCycleDegreeGcdCombination d e zD zE)
  refine ⟨ops, ?_⟩
  rw [hweight, map_smul, zeroCycleDegreeGcdCombination_degree pi d e zD zE hD hE]
  change (t : ℤ) * (Nat.gcd d e : ℤ) = (theta : ℤ)
  rw [ht, Nat.cast_mul]
  exact mul_comm _ _

/-- A(i)'s actual degree-d and degree-three NORMALIZATION cycles would give
a word of weight G_l<d. This does not construct those missing geometric
cycles from the available original cubic-surface point. -/
theorem coray_case_Ai_normalizationCycles_choose_word
    (pi : X ⟶ Spec (CommRingCat.of K)) (l d : ℕ) (hprime : ¬ 3 ∣ d)
    (hsmall : 3 * l.choose 2 + 1 < d)
    (zD zThree : ZeroCycle X)
    (hD : ZeroCycle.degree pi zD = (d : ℤ))
    (hThree : ZeroCycle.degree pi zThree = 3) :
    ∃ ops : List (closedPoints X × Bool),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = ((3 * l.choose 2 + 1 : ℕ) : ℤ) ∧
      ¬ 3 ∣ 3 * l.choose 2 + 1 ∧ 3 * l.choose 2 + 1 < d := by
  have hcop : Nat.Coprime d 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr hprime).symm
  have hdiv : Nat.gcd d 3 ∣ 3 * l.choose 2 + 1 := by
    rw [show Nat.gcd d 3 = 1 from hcop]
    exact one_dvd _
  obtain ⟨ops, hweight⟩ := exists_signedPointTensorOperations_weight_eq_multiple_gcd
    pi d 3 zD zThree hD hThree (3 * l.choose 2 + 1) hdiv
  refine ⟨ops, hweight, ?_, hsmall⟩
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

/-- A(ii)'s actual NORMALIZATION cycles of degrees d and 3*l suffice to
construct a prime-to-three weight in [G_l,d). The canonical divisor and its
2g-2 degree need not be constructed for THIS sufficient window. The cycle
inputs remain explicit algebraic data, not a claimed primitive Coray proof. -/
theorem coray_case_Aii_normalizationCycles_choose_word
    (pi : X ⟶ Spec (CommRingCat.of K)) (l d : ℕ) (hl : 3 ≤ l)
    (hd : 0 < d) (hprime : ¬ 3 ∣ d)
    (hdegree : d ≤ 3 * (l + 1).choose 2)
    (hfreedom : 3 * (l + 1).choose 2 - d < 3)
    (zD zH : ZeroCycle X)
    (hD : ZeroCycle.degree pi zD = (d : ℤ))
    (hH : ZeroCycle.degree pi zH = ((3 * l : ℕ) : ℤ)) :
    ∃ (theta : ℕ) (ops : List (closedPoints X × Bool)),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) ∧
      0 < theta ∧ ¬ 3 ∣ theta ∧ 3 * l.choose 2 + 1 ≤ theta ∧ theta < d := by
  let delta := Nat.gcd d (3 * l)
  have hdelta : 0 < delta := Nat.gcd_pos_of_pos_left _ hd
  have hdeltaD : delta ∣ d := Nat.gcd_dvd_left _ _
  have hdeltaH : delta ∣ 3 * l := Nat.gcd_dvd_right _ _
  have hdeltaPrime : ¬ 3 ∣ delta := fun h => hprime (dvd_trans h hdeltaD)
  obtain ⟨theta, hpos, hmultiple, hprimeTheta, hlow, hhigh⟩ :=
    coray_case_Aii_degree_selection l d (3 * l.choose 2 + 1) delta hl
      hdelta hdeltaPrime hdeltaH le_rfl hdegree hfreedom
  obtain ⟨ops, hweight⟩ := exists_signedPointTensorOperations_weight_eq_multiple_gcd
    pi d (3 * l) zD zH hD hH theta hmultiple
  exact ⟨theta, ops, hweight, hpos, hprimeTheta, hlow, hhigh⟩

/-- The omitted small-l A(ii) degrees7/8 use the SAME two-cycle Bezout
construction: gcd(d,6) divides4, giving a smaller weight4=G_2. -/
theorem coray_case_Aii_l_two_normalizationCycles_choose_word
    (pi : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) (hd : d = 7 ∨ d = 8)
    (zD zH : ZeroCycle X)
    (hD : ZeroCycle.degree pi zD = (d : ℤ))
    (hH : ZeroCycle.degree pi zH = 6) :
    ∃ ops : List (closedPoints X × Bool),
      schemeModuleSignedClosedPointTensorWeightSum pi ops = 4 ∧ 4 < d := by
  have hdiv : Nat.gcd d 6 ∣ 4 := by
    rcases hd with rfl | rfl <;> norm_num
  obtain ⟨ops, hweight⟩ := exists_signedPointTensorOperations_weight_eq_multiple_gcd
    pi d 6 zD zH hD hH 4 hdiv
  refine ⟨ops, hweight, ?_⟩
  omega

/-- Boundary A(iii)'s two actual NORMALIZATION cycles give the two literal
candidate word weights d-3 or d-2 and the arithmetic theta+3>=G_l. Applying
the sharper Euler window additionally needs an ACTUAL global quotient
contribution >=3; that geometric contribution is not assumed/proved here. -/
theorem coray_case_Aiii_normalizationCycles_choose_word
    (pi : X ⟶ Spec (CommRingCat.of K)) (l : ℕ) (hl : 2 ≤ l)
    (zD zH : ZeroCycle X)
    (hD : ZeroCycle.degree pi zD = ((3 * l.choose 2 + 1 : ℕ) : ℤ))
    (hH : ZeroCycle.degree pi zH = ((3 * l : ℕ) : ℤ)) :
    let d := 3 * l.choose 2 + 1
    ∃ (theta : ℕ) (ops : List (closedPoints X × Bool)),
      (theta = d - 3 ∨ theta = d - 2) ∧
      schemeModuleSignedClosedPointTensorWeightSum pi ops = (theta : ℤ) ∧
      0 < theta ∧ ¬ 3 ∣ theta ∧ theta + 3 ≥ d ∧ theta < d := by
  dsimp only
  let d := 3 * l.choose 2 + 1
  let delta := Nat.gcd d (3 * l)
  have hdeltaD : delta ∣ d := Nat.gcd_dvd_left _ _
  have hdeltaH : delta ∣ 3 * l := Nat.gcd_dvd_right _ _
  have hprimeD : ¬ 3 ∣ d := by dsimp only [d]; rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hdeltaPrime : ¬ 3 ∣ delta := fun h => hprimeD (dvd_trans h hdeltaD)
  have hdeltaL : delta ∣ l := degree_delta_dvd_l_of_dvd_three_l delta l hdeltaPrime hdeltaH
  have hchoose : 0 < l.choose 2 := Nat.choose_pos hl
  have hgenus : (d - 3) + 3 ≤ 3 * l.choose 2 + 1 := by dsimp only [d]; omega
  obtain ⟨theta, hcandidates, hpos, hmultiple, hprimeTheta, hlow, hhigh⟩ :=
    coray_case_Aiii_degree_selection l (d - 3) delta hl hdeltaL hdeltaD hgenus
  obtain ⟨ops, hweight⟩ := exists_signedPointTensorOperations_weight_eq_multiple_gcd
    pi d (3 * l) zD zH hD hH theta hmultiple
  refine ⟨theta, ops, hcandidates, hweight, hpos, hprimeTheta, ?_, hhigh⟩
  dsimp only [d] at hlow ⊢
  omega

/-- Exact equality of the arithmetic selector's triangular genus bound and
our actual original-X cohomological bound; no curve genus is assumed. -/
theorem coray_choose_genus_eq_euler_bound (l : ℕ) :
    3 * l.choose 2 + 1 = 1 + 3 * l * (l - 1) / 2 := by
  have htwo : 2 * l.choose 2 = l * (l - 1) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose l 2
    rw [show Nat.factorial 2 = 2 by decide] at h
    simpa only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      mul_one, mul_comm] using h.symm
  have hproduct : 3 * l * (l - 1) = 2 * (3 * l.choose 2) := by
    calc
      3 * l * (l - 1) = 3 * (l * (l - 1)) := by ring
      _ = 3 * (2 * l.choose 2) := congrArg (fun a : ℕ => 3 * a) htwo.symm
      _ = 2 * (3 * l.choose 2) := by ring
  rw [hproduct]
  omega

end PfaffianDescent.Coray
