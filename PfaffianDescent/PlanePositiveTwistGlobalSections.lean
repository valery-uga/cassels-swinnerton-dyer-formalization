import PfaffianDescent.PlaneNativeChartLaurentFaceNaturality
/-! SOURCE ONLY / UNCHECKED. Actual native P2 O(m) global sections are
homogeneous polynomials for EVERY m≥0, including zero. Chart Laurent
representatives and their equality are derived, not assumed. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist PlaneLaurentLocalization PlaneTwistLaurent
open PlaneTwistCechTerms PlaneTwistCechTerms.GenericEvaluation PlanePositiveTwistNaturality
open scoped AddMonoidAlgebra
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K
/-- The face-restriction formula specialized to the compatible local values
of one global positive-twist section. -/
lemma p2PositiveTwistGlobalChartLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3)
    (s : (positiveSheafOfModules PS m).sections) :
    awayToLaurent (K := K) (n + 1) f
        (p2PositiveTwistChartAway K (n + 1) f m
          ((deleteTuple i f) 0)
          (dvd_trans
            (p2Coordinate_zero_dvd_cechDenominator
              (K := K) n (deleteTuple i f))
            ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul
              (K := K) n i f⟩)
          (PresheafOfModules.sections.eval s
            (op (p2CechBasicOpen K (n + 1) f)))) =
      awayToLaurent (K := K) n (deleteTuple i f)
        (p2PositiveTwistChartAway K n (deleteTuple i f) m
          ((deleteTuple i f) 0)
          (p2Coordinate_zero_dvd_cechDenominator
            (K := K) n (deleteTuple i f))
          (PresheafOfModules.sections.eval s
            (op (p2CechBasicOpen K n (deleteTuple i f))))) := by
  let hST : p2CechBasicOpen K (n + 1) f ≤
      p2CechBasicOpen K n (deleteTuple i f) :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (p2CechDenominator (K := K) n (deleteTuple i f))
      (p2CechDenominator (K := K) (n + 1) f)
      ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
  have hsec := PresheafOfModules.sections_property s (homOfLE hST).op
  have hsec' :
      (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op
          (PresheafOfModules.sections.eval s
            (op (p2CechBasicOpen K n (deleteTuple i f)))) =
        PresheafOfModules.sections.eval s
          (op (p2CechBasicOpen K (n + 1) f)) := hsec
  have hface := p2PositiveTwistChartLaurent_restrict_face K m n i f
    (PresheafOfModules.sections.eval s
      (op (p2CechBasicOpen K n (deleteTuple i f))))
  dsimp only at hface
  rw [hsec'] at hface
  exact hface

/-- Restriction of a global positive-twist section to a standard chart. -/
noncomputable def p2PositiveTwistRestrictGlobal
    (m : ℕ) (s : (positiveSheafOfModules PS m).sections) (i : Fin 3) :
    Γ(positiveSheafOfModules PS m, p2StandardOpen (K := K) i) :=
  (positiveModulePresheaf PS m).presheaf.map
    (homOfLE (show p2StandardOpen (K := K) i ≤ ⊤ from le_top)).op
    (PresheafOfModules.sections.eval s (op (⊤ : Opens (Proj PS))))

lemma p2PositiveTwistRestrictGlobal_eq_eval
    (m : ℕ) (s : (positiveSheafOfModules PS m).sections) (i : Fin 3) :
    p2PositiveTwistRestrictGlobal K m s i =
      PresheafOfModules.sections.eval s
        (op (p2StandardOpen (K := K) i)) := by
  exact PresheafOfModules.sections_property s
    (homOfLE (show p2StandardOpen (K := K) i ≤ ⊤ from le_top)).op

/-- The Laurent representative of a positive-twist section on a standard
chart, after restoring the chart basis `X_i^m`. -/
noncomputable def p2PositiveTwistGlobalCechChartBase
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (s : (positiveSheafOfModules PS m).sections) :
    PlaneLaurentLocalization.LaurentPolynomial K :=
  awayToLaurent (K := K) n f
    (p2PositiveTwistChartAway K n f m (f 0)
      (p2Coordinate_zero_dvd_cechDenominator (K := K) n f)
      (PresheafOfModules.sections.eval s (op (p2CechBasicOpen K n f))))

/-- The Laurent representative of a positive-twist section on a standard
chart, after restoring the chart basis `X_i^m`. -/
noncomputable def p2PositiveTwistGlobalChartLaurent
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections) (i : Fin 3) :
    PlaneLaurentLocalization.LaurentPolynomial K :=
  p2PositiveTwistGlobalCechChartBase K m 0 ![i] s *
    AddMonoidAlgebra.single (positiveTwistShift m i) 1

/-- Every monomial in a positive-twist chart representative has the twist
degree, and any negative exponent is confined to that chart's inverted
coordinate. -/
theorem p2PositiveTwistGlobalChartLaurent_support
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections) (i : Fin 3) :
    ∀ a ∈ (p2PositiveTwistGlobalChartLaurent K m s i).coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ ({i} : Set (Fin 3)) := by
  intro a ha
  let z : HomogeneousLocalization.Away PS
      (p2CechDenominator (K := K) 0 ![i]) :=
    p2PositiveTwistChartAway K 0 ![i] m (![i] 0)
      (p2Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
      (PresheafOfModules.sections.eval s
        (op (p2CechBasicOpen K 0 ![i])))
  change a ∈ (p2PositiveTwistGlobalCechChartBase K m 0 ![i] s *
      AddMonoidAlgebra.single (positiveTwistShift m i) 1).coeff.support at ha
  change a ∈ (awayToLaurent (K := K) 0 ![i] z *
      AddMonoidAlgebra.single (positiveTwistShift m i) 1).coeff.support at ha
  obtain ⟨b, hb, rfl⟩ :=
    (PlaneTwistLaurent.mul_single_mem_support_iff (K := K)
      (awayToLaurent (K := K) 0 ![i] z)
      (positiveTwistShift m i) a).mp ha
  have hbase := awayToLaurent_support_properties (K := K) 0 ![i] z b hb
  constructor
  · rw [totalDegree_add, hbase.1,
      PlaneTwistLaurent.totalDegree_positiveTwistShift]
    simp
  · have hneg :=
      (PlaneTwistLaurent.negativeSupport_add_positiveTwistShift_subset m i b).trans
        hbase.2
    simpa using hneg

/-- The restored Laurent representatives of a global positive-twist section
agree on all four standard coordinate charts. -/
theorem p2PositiveTwistGlobalChartLaurent_eq
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections) (i j : Fin 3) :
    p2PositiveTwistGlobalChartLaurent K m s i =
      p2PositiveTwistGlobalChartLaurent K m s j := by
  let pair : Fin 2 → Fin 3 := ![i, j]
  let faceI : Fin 2 := 1
  let faceJ : Fin 2 := 0
  have hdelI : deleteTuple faceI pair = ![i] := by
    funext k
    fin_cases k
    rfl
  have hdelJ : deleteTuple faceJ pair = ![j] := by
    funext k
    fin_cases k
    rfl
  have hi := p2PositiveTwistGlobalChartLaurent_restrict_face
    K m 0 faceI pair s
  have hj := p2PositiveTwistGlobalChartLaurent_restrict_face
    K m 0 faceJ pair s
  let kI : Fin 3 := (deleteTuple faceI pair) 0
  let kJ : Fin 3 := (deleteTuple faceJ pair) 0
  have hkI : kI = i := by
    change (deleteTuple faceI pair) 0 = i
    rw [hdelI]
    rfl
  have hkJ : kJ = j := by
    change (deleteTuple faceJ pair) 0 = j
    rw [hdelJ]
    rfl
  have hi' := congrArg (fun q => q *
    AddMonoidAlgebra.single (positiveTwistShift m kI) (1 : K)) hi
  have hj' := congrArg (fun q => q *
    AddMonoidAlgebra.single (positiveTwistShift m kJ) (1 : K)) hj
  change _ = p2PositiveTwistGlobalCechChartBase K m 0
    (deleteTuple faceI pair) s *
      AddMonoidAlgebra.single (positiveTwistShift m kI) 1 at hi'
  change _ = p2PositiveTwistGlobalCechChartBase K m 0
    (deleteTuple faceJ pair) s *
      AddMonoidAlgebra.single (positiveTwistShift m kJ) 1 at hj'
  have hbaseI := congrArg
    (fun t => p2PositiveTwistGlobalCechChartBase K m 0 t s) hdelI
  have hbaseJ := congrArg
    (fun t => p2PositiveTwistGlobalCechChartBase K m 0 t s) hdelJ
  have hind := p2PositiveTwistChartLaurent_independent K 1 pair m kI
    (dvd_trans
      (p2Coordinate_zero_dvd_cechDenominator
        (K := K) 0 (deleteTuple faceI pair))
      ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul
        (K := K) 0 faceI pair⟩) kJ
    (dvd_trans
      (p2Coordinate_zero_dvd_cechDenominator
        (K := K) 0 (deleteTuple faceJ pair))
      ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul
        (K := K) 0 faceJ pair⟩)
    (PresheafOfModules.sections.eval s (op (p2CechBasicOpen K 1 pair)))
  calc
    p2PositiveTwistGlobalChartLaurent K m s i =
        p2PositiveTwistGlobalCechChartBase K m 0
            (deleteTuple faceI pair) s *
          AddMonoidAlgebra.single (positiveTwistShift m kI) 1 := by
      rw [p2PositiveTwistGlobalChartLaurent, hbaseI, hkI]
    _ = awayToLaurent (K := K) 1 pair
          (p2PositiveTwistChartAway K 1 pair m kI
            (dvd_trans
              (p2Coordinate_zero_dvd_cechDenominator
                (K := K) 0 (deleteTuple faceI pair))
              ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul
                (K := K) 0 faceI pair⟩)
            (PresheafOfModules.sections.eval s
              (op (p2CechBasicOpen K 1 pair)))) *
          AddMonoidAlgebra.single (positiveTwistShift m kI) 1 := hi'.symm
    _ = awayToLaurent (K := K) 1 pair
          (p2PositiveTwistChartAway K 1 pair m kJ
            (dvd_trans
              (p2Coordinate_zero_dvd_cechDenominator
                (K := K) 0 (deleteTuple faceJ pair))
              ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul
                (K := K) 0 faceJ pair⟩)
            (PresheafOfModules.sections.eval s
              (op (p2CechBasicOpen K 1 pair)))) *
          AddMonoidAlgebra.single (positiveTwistShift m kJ) 1 := hind
    _ = p2PositiveTwistGlobalCechChartBase K m 0
            (deleteTuple faceJ pair) s *
          AddMonoidAlgebra.single (positiveTwistShift m kJ) 1 := hj'
    _ = p2PositiveTwistGlobalChartLaurent K m s j := by
      rw [p2PositiveTwistGlobalChartLaurent, hbaseJ, hkJ]

/-- The chart Laurent representative of the global section attached to a
homogeneous polynomial is the Laurent image of that polynomial. -/
theorem p2PositiveTwistGlobalChartLaurent_of_homogeneous
    (m : ℕ) (p : PS m) (i : Fin 3) :
    p2PositiveTwistGlobalChartLaurent K m
        (positiveGlobalSectionOfHomogeneous PS m p) i =
      polynomialToLaurent (K := K) (p : MvPolynomial (Fin 3) K) := by
  let t : Fin 1 → Fin 3 := ![i]
  let s := positiveGlobalSectionOfHomogeneous PS m p
  let z := p2PositiveTwistChartAway K 0 t m (t 0)
    (p2Coordinate_zero_dvd_cechDenominator (K := K) 0 t)
    (PresheafOfModules.sections.eval s (op (p2CechBasicOpen K 0 t)))
  have hval := genericLocalizationMap_p2PositiveTwistChartAway K 0 t m (t 0)
    (p2Coordinate_zero_dvd_cechDenominator (K := K) 0 t)
    (PresheafOfModules.sections.eval s (op (p2CechBasicOpen K 0 t)))
  have hgen := awayToSection_positiveGeneric_apply K 0 t z
  change ((((ProjectiveSpectrum.Proj.awayToSection PS
      (p2CechDenominator (K := K) 0 t)).1 z).val
        (cechGenericPoint K 0 t)).val) = _ at hgen
  change _ = _ *
    (((ProjectiveSpectrum.Proj.awayToSection PS
      (p2CechDenominator (K := K) 0 t)).1 z).val
        (cechGenericPoint K 0 t)).val at hval
  rw [hgen] at hval
  have hcross : z.val *
        algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (p2CechDenominator (K := K) 0 t))
          ((degreeOnePower PS (p2Coordinate K (t 0)) m : PS m) :
            MvPolynomial (Fin 3) K) =
      algebraMap (MvPolynomial (Fin 3) K)
        (Localization.Away (p2CechDenominator (K := K) 0 t))
        (p : MvPolynomial (Fin 3) K) := by
    apply positiveGenericLocalizationMap_injective K 0 t
    rw [map_mul, positiveGenericLocalizationMap_algebraMap K 0 t,
      positiveGenericLocalizationMap_algebraMap K 0 t]
    change positiveGenericLocalizationMap K 0 t z.val *
        algebraMap (MvPolynomial (Fin 3) K)
          (PositiveFiber PS (p2GenericPoint K))
          ((degreeOnePower PS (p2Coordinate K (t 0)) m : PS m) :
            MvPolynomial (Fin 3) K) =
      algebraMap (MvPolynomial (Fin 3) K)
        (PositiveFiber PS (p2GenericPoint K))
        (p : MvPolynomial (Fin 3) K)
    calc
      _ = algebraMap (MvPolynomial (Fin 3) K)
            (PositiveFiber PS (p2GenericPoint K))
            ((degreeOnePower PS (p2Coordinate K (t 0)) m : PS m) :
              MvPolynomial (Fin 3) K) *
          positiveGenericLocalizationMap K 0 t z.val := mul_comm _ _
      _ = (PresheafOfModules.sections.eval s
            (op (p2CechBasicOpen K 0 t))).1 (cechGenericPoint K 0 t) := hval.symm
      _ = Localization.mk (p : MvPolynomial (Fin 3) K)
            ⟨1, Submonoid.one_mem _⟩ := rfl
      _ = _ := Localization.mk_one_eq_algebraMap _
  have hL := congrArg (localizationAwayToLaurent (K := K) 0 t) hcross
  simp only [map_mul, localizationAwayToLaurent_algebraMap,
    polynomialToLaurent_degreeOnePower K m] at hL
  change awayToLaurent (K := K) 0 t z *
      AddMonoidAlgebra.single (positiveTwistShift m (t 0)) 1 =
    polynomialToLaurent (K := K) (p : MvPolynomial (Fin 3) K) at hL
  simpa [p2PositiveTwistGlobalChartLaurent,
    p2PositiveTwistGlobalCechChartBase, t, s, z] using hL

/-- A Laurent exponent which can have a negative coordinate only at every
one of two distinct coordinate indices has no negative coordinates. -/
lemma negativeSupport_eq_empty_of_subset_singletons
    (a : PlaneLaurentLocalization.LaurentExponent)
    (h₀ : negativeSupport a ⊆ ({(0 : Fin 3)} : Set (Fin 3)))
    (h₁ : negativeSupport a ⊆ ({(1 : Fin 3)} : Set (Fin 3))) :
    negativeSupport a = ∅ := by
  ext j
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hj
  have hj₀ : j = 0 := by simpa using h₀ hj
  have hj₁ : j = 1 := by simpa using h₁ hj
  omega

/-- Once the Laurent representatives on all standard charts agree, their
common monomials are ordinary nonnegative monomials of degree `m`. -/
theorem p2PositiveTwist_commonLaurent_support
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections)
    (g : PlaneLaurentLocalization.LaurentPolynomial K)
    (hg : ∀ i, p2PositiveTwistGlobalChartLaurent K m s i = g) :
    ∀ a ∈ g.coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a = ∅ := by
  intro a ha
  have hsupport (i : Fin 3) :
      totalDegree a = (m : ℤ) ∧
        negativeSupport a ⊆ ({i} : Set (Fin 3)) := by
    apply p2PositiveTwistGlobalChartLaurent_support K m s i
    simpa [hg i] using ha
  exact ⟨(hsupport 0).1,
    negativeSupport_eq_empty_of_subset_singletons a
      (hsupport 0).2 (hsupport 1).2⟩

/-- Convert a Laurent exponent known to be nonnegative coordinatewise into
an ordinary multivariate-polynomial exponent. -/
def nonnegativeExponentToNat
    (a : PlaneLaurentLocalization.LaurentExponent) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ Int.toNat (a i)

@[simp] lemma nonnegativeExponentToNat_apply
    (a : PlaneLaurentLocalization.LaurentExponent) (i : Fin 3) :
    nonnegativeExponentToNat a i = Int.toNat (a i) := rfl

lemma exponentToInt_nonnegativeExponentToNat
    (a : PlaneLaurentLocalization.LaurentExponent)
    (ha : negativeSupport a = ∅) :
    exponentToInt (nonnegativeExponentToNat a) = a := by
  ext i
  rw [exponentToInt_apply, nonnegativeExponentToNat_apply,
    Int.toNat_of_nonneg]
  by_contra hi
  have hineg : i ∈ negativeSupport a := lt_of_not_ge hi
  rw [ha] at hineg
  exact hineg

lemma nonnegativeExponentToNat_degree
    (a : PlaneLaurentLocalization.LaurentExponent) (m : ℕ)
    (hdegree : totalDegree a = (m : ℤ))
    (ha : negativeSupport a = ∅) :
    (nonnegativeExponentToNat a).degree = m := by
  have htotal := totalDegree_exponentToInt (nonnegativeExponentToNat a)
  rw [exponentToInt_nonnegativeExponentToNat a ha, hdegree] at htotal
  rw [Finsupp.degree_apply, ← finsupp_sum_eq_sum_support]
  exact_mod_cast htotal.symm

lemma nonnegativeLaurentMonomial_mem_homogeneous
    (a : PlaneLaurentLocalization.LaurentExponent) (c : K) (m : ℕ)
    (hdegree : totalDegree a = (m : ℤ))
    (ha : negativeSupport a = ∅) :
    MvPolynomial.monomial (nonnegativeExponentToNat a) c ∈ PS m := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_monomial c
    (nonnegativeExponentToNat_degree a m hdegree ha)

/-- The ordinary polynomial obtained by interpreting every nonnegative
Laurent exponent as a natural exponent. -/
noncomputable def polynomialOfNonnegativeLaurent
    (g : PlaneLaurentLocalization.LaurentPolynomial K) :
    MvPolynomial (Fin 3) K :=
  ∑ a ∈ g.coeff.support,
    MvPolynomial.monomial (nonnegativeExponentToNat a) (g.coeff a)

/-- A Laurent polynomial supported in nonnegative degree-`m` exponents is
the Laurent image of an actual homogeneous polynomial of degree `m`. -/
theorem polynomialOfNonnegativeLaurent_mem_and_map
    (g : PlaneLaurentLocalization.LaurentPolynomial K) (m : ℕ)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a = ∅) :
    polynomialOfNonnegativeLaurent K g ∈ PS m ∧
      polynomialToLaurent (K := K) (polynomialOfNonnegativeLaurent K g) = g := by
  classical
  constructor
  · apply Submodule.sum_mem
    intro a ha
    exact nonnegativeLaurentMonomial_mem_homogeneous K a (g.coeff a) m
      (hg a ha).1 (hg a ha).2
  · unfold polynomialOfNonnegativeLaurent
    rw [map_sum]
    calc
      ∑ a ∈ g.coeff.support,
          polynomialToLaurent (K := K)
            (MvPolynomial.monomial (nonnegativeExponentToNat a) (g.coeff a)) =
          ∑ a ∈ g.coeff.support,
            AddMonoidAlgebra.single a (g.coeff a) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [polynomialToLaurent_monomial,
                exponentToInt_nonnegativeExponentToNat a (hg a ha).2]
      _ = g := by
        simpa [Finsupp.sum] using (AddMonoidAlgebra.sum_coeff_single g)

/-- If the four chart representatives of a global positive-twist section
agree, their common value is represented by an ordinary homogeneous
polynomial of the twist degree. -/
theorem exists_homogeneous_polynomial_of_positiveTwist_commonLaurent
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections)
    (g : PlaneLaurentLocalization.LaurentPolynomial K)
    (hg : ∀ i, p2PositiveTwistGlobalChartLaurent K m s i = g) :
    ∃ p : PS m, polynomialToLaurent (K := K) (p : MvPolynomial (Fin 3) K) = g := by
  let p := polynomialOfNonnegativeLaurent K g
  have hp := polynomialOfNonnegativeLaurent_mem_and_map K g m
    (p2PositiveTwist_commonLaurent_support K m s g hg)
  exact ⟨⟨p, hp.1⟩, hp.2⟩

/-- Every global positive-twist section determines a homogeneous polynomial
with the same Laurent representative on every standard chart. -/
theorem exists_homogeneous_polynomial_of_positiveTwist
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections) :
    ∃ p : PS m, ∀ i,
      polynomialToLaurent (K := K) (p : MvPolynomial (Fin 3) K) =
        p2PositiveTwistGlobalChartLaurent K m s i := by
  obtain ⟨p, hp⟩ :=
    exists_homogeneous_polynomial_of_positiveTwist_commonLaurent
      K m s (p2PositiveTwistGlobalChartLaurent K m s 0)
      (fun i => p2PositiveTwistGlobalChartLaurent_eq K m s i 0)
  exact ⟨p, fun i => hp.trans
    (p2PositiveTwistGlobalChartLaurent_eq K m s 0 i)⟩

lemma eq_of_mul_positiveTwistShift_eq
    (m : ℕ) (i : Fin 3)
    {a b : PlaneLaurentLocalization.LaurentPolynomial K}
    (h : a * AddMonoidAlgebra.single (positiveTwistShift m i) 1 =
      b * AddMonoidAlgebra.single (positiveTwistShift m i) 1) :
    a = b := by
  let p := AddMonoidAlgebra.single (positiveTwistShift m i) (1 : K)
  let q := AddMonoidAlgebra.single (twistShift m i) (1 : K)
  change a * p = b * p at h
  calc
    a = a * 1 := by rw [mul_one]
    _ = a * (p * q) := by rw [PlaneTwistLaurent.positiveTwistShift_mul_twistShift K m i]
    _ = (a * p) * q := by ring
    _ = (b * p) * q := by rw [h]
    _ = b * (p * q) := by ring
    _ = b := by rw [PlaneTwistLaurent.positiveTwistShift_mul_twistShift K m i, mul_one]

/-- Equality of restored Laurent representatives on one coordinate chart
implies equality of the two section restrictions to that chart. -/
lemma p2PositiveTwist_restrict_eq_of_chartLaurent_eq
    (m : ℕ)
    (s t : (positiveSheafOfModules PS m).sections) (i : Fin 3)
    (h : p2PositiveTwistGlobalChartLaurent K m s i =
      p2PositiveTwistGlobalChartLaurent K m t i) :
    PresheafOfModules.sections.eval s (op (p2CechBasicOpen K 0 ![i])) =
      PresheafOfModules.sections.eval t (op (p2CechBasicOpen K 0 ![i])) := by
  have hbase : p2PositiveTwistGlobalCechChartBase K m 0 ![i] s =
      p2PositiveTwistGlobalCechChartBase K m 0 ![i] t := by
    apply eq_of_mul_positiveTwistShift_eq K m i
    simpa only [p2PositiveTwistGlobalChartLaurent] using h
  have haway :
      p2PositiveTwistChartAway K 0 ![i] m (![i] 0)
          (p2Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
          (PresheafOfModules.sections.eval s
            (op (p2CechBasicOpen K 0 ![i]))) =
        p2PositiveTwistChartAway K 0 ![i] m (![i] 0)
          (p2Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
          (PresheafOfModules.sections.eval t
            (op (p2CechBasicOpen K 0 ![i]))) := by
    apply awayToLaurent_injective (K := K) 0 ![i]
    simpa only [p2PositiveTwistGlobalCechChartBase] using hbase
  let e := p2PositiveTwistBasicOpenIsoAway K
    (p2CechDenominator (K := K) 0 ![i]) 1
    (p2CechDenominator_mem (K := K) 0 ![i]) (by decide)
    (![i] 0) (p2Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i]) m
  change e.hom (PresheafOfModules.sections.eval s
      (op (p2CechBasicOpen K 0 ![i]))) =
    e.hom (PresheafOfModules.sections.eval t
      (op (p2CechBasicOpen K 0 ![i]))) at haway
  have hinv := congrArg (fun q => e.inv q) haway
  have hinv' :
      e.inv (e.hom (PresheafOfModules.sections.eval s
        (op (p2CechBasicOpen K 0 ![i])))) =
      e.inv (e.hom (PresheafOfModules.sections.eval t
        (op (p2CechBasicOpen K 0 ![i])))) := hinv
  have hs := e.hom_inv_id_apply
    (PresheafOfModules.sections.eval s (op (p2CechBasicOpen K 0 ![i])))
  have ht := e.hom_inv_id_apply
    (PresheafOfModules.sections.eval t (op (p2CechBasicOpen K 0 ![i])))
  exact hs.symm.trans (hinv'.trans ht)

lemma p2CechSingleOpen_eq_standard (i : Fin 3) :
    p2CechBasicOpen K 0 ![i] = p2StandardOpen (K := K) i := by
  change AlgebraicGeometry.Proj.basicOpen PS
      (p2CechDenominator (K := K) 0 ![i]) =
    AlgebraicGeometry.Proj.basicOpen PS (MvPolynomial.X i)
  congr 1
  simp [p2CechDenominator]

lemma p2CechSingleOpen_iSup :
    ⨆ i : Fin 3, p2CechBasicOpen K 0 ![i] = ⊤ := by
  simp_rw [p2CechSingleOpen_eq_standard K]
  exact p2StandardOpen_iSup K

/-- Global positive-twist sections are determined by their four restored
Laurent chart representatives. -/
theorem p2PositiveTwist_global_eq_of_chartLaurent_eq
    (m : ℕ)
    (s t : (positiveSheafOfModules PS m).sections)
    (h : ∀ i, p2PositiveTwistGlobalChartLaurent K m s i =
      p2PositiveTwistGlobalChartLaurent K m t i) :
    s = t := by
  let M := positiveSheafOfModules PS m
  let G : TopCat.Sheaf AddCommGrpCat (Proj PS) :=
    (SheafOfModules.toSheaf (Proj PS).ringCatSheaf).obj M
  have htop : PresheafOfModules.sections.eval s
        (op (⊤ : Opens (Proj PS))) =
      PresheafOfModules.sections.eval t
        (op (⊤ : Opens (Proj PS))) := by
    apply G.eq_of_locally_eq'
      (fun i : Fin 3 => p2CechBasicOpen K 0 ![i])
      (⊤ : Opens (Proj PS))
      (fun _ => homOfLE le_top)
      (by rw [p2CechSingleOpen_iSup K])
    intro i
    change (positiveSheafOfModules PS m).presheaf.map
        (homOfLE (show p2CechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval s
            (op (⊤ : Opens (Proj PS)))) =
      (positiveSheafOfModules PS m).presheaf.map
        (homOfLE (show p2CechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval t
            (op (⊤ : Opens (Proj PS))))
    have hsres : (positiveSheafOfModules PS m).presheaf.map
          (homOfLE (show p2CechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval s
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval s
          (op (p2CechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property s _
    have htres : (positiveSheafOfModules PS m).presheaf.map
          (homOfLE (show p2CechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval t
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval t
          (op (p2CechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property t _
    rw [hsres, htres]
    exact p2PositiveTwist_restrict_eq_of_chartLaurent_eq K m s t i (h i)
  apply PresheafOfModules.sections_ext
  intro U
  let r := (positiveSheafOfModules PS m).presheaf.map
    (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op
  have hsU := PresheafOfModules.sections_property s
    (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op
  have htU := PresheafOfModules.sections_property t
    (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op
  have hres : r (PresheafOfModules.sections.eval s
        (op (⊤ : Opens (Proj PS)))) =
      r (PresheafOfModules.sections.eval t
        (op (⊤ : Opens (Proj PS)))) := congrArg (fun q => r q) htop
  exact hsU.symm.trans (hres.trans htU)

/-- Homogeneous polynomials generate all global sections of every positive
twist on projective three-space. -/
theorem p2_positiveGlobalSectionOfHomogeneous_surjective
    (m : ℕ) :
    Function.Surjective (positiveGlobalSectionOfHomogeneous PS m) := by
  intro s
  obtain ⟨p, hp⟩ := exists_homogeneous_polynomial_of_positiveTwist K m s
  refine ⟨p, ?_⟩
  apply p2PositiveTwist_global_eq_of_chartLaurent_eq K m
  intro i
  exact (p2PositiveTwistGlobalChartLaurent_of_homogeneous K m p i).trans
    (hp i)


end PfaffianDescent.ProjectivePlaneNative
