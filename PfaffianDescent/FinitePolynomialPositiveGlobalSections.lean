import PfaffianDescent.FinitePolynomialPositiveChartGenericNaturality
/-! SOURCE ONLY / UNCHECKED. Actual native positive O(m) global sections are
homogeneous polynomials for EVERY m≥0, including zero. Chart Laurent
representatives and their equality are derived, not assumed. -/
noncomputable section
namespace PfaffianDescent.ProjectiveFiniteNative
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist FinitePolynomialLaurentLocalization FinitePolynomialTwistLaurent
open FinitePolynomialTwistCechTerms FinitePolynomialTwistCechTerms.GenericEvaluation FinitePolynomialPositiveTwistNaturality
open scoped AddMonoidAlgebra
universe u
variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nontrivial σ]
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (σ) K
/-- The face-restriction formula specialized to the compatible local values
of one global positive-twist section. -/
lemma finitePolynomialPositiveTwistGlobalChartLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → σ)
    (s : (positiveSheafOfModules PS m).sections) :
    awayToLaurent (K := K) (n + 1) f
        (finitePolynomialPositiveTwistChartAway K (n + 1) f m
          ((deleteTuple i f) 0)
          (dvd_trans
            (finitePolynomialCoordinate_zero_dvd_cechDenominator
              (K := K) n (deleteTuple i f))
            ⟨_, finitePolynomialCechDenominator_succ_eq_deleteTuple_mul
              (K := K) n i f⟩)
          (PresheafOfModules.sections.eval s
            (op (finitePolynomialCechBasicOpen K (n + 1) f)))) =
      awayToLaurent (K := K) n (deleteTuple i f)
        (finitePolynomialPositiveTwistChartAway K n (deleteTuple i f) m
          ((deleteTuple i f) 0)
          (finitePolynomialCoordinate_zero_dvd_cechDenominator
            (K := K) n (deleteTuple i f))
          (PresheafOfModules.sections.eval s
            (op (finitePolynomialCechBasicOpen K n (deleteTuple i f))))) := by
  let hST : finitePolynomialCechBasicOpen K (n + 1) f ≤
      finitePolynomialCechBasicOpen K n (deleteTuple i f) :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (finitePolynomialCechDenominator (K := K) n (deleteTuple i f))
      (finitePolynomialCechDenominator (K := K) (n + 1) f)
      ⟨_, finitePolynomialCechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
  have hsec := PresheafOfModules.sections_property s (homOfLE hST).op
  have hsec' :
      (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op
          (PresheafOfModules.sections.eval s
            (op (finitePolynomialCechBasicOpen K n (deleteTuple i f)))) =
        PresheafOfModules.sections.eval s
          (op (finitePolynomialCechBasicOpen K (n + 1) f)) := hsec
  have hface := finitePolynomialPositiveTwistChartLaurent_restrict_face K m n i f
    (PresheafOfModules.sections.eval s
      (op (finitePolynomialCechBasicOpen K n (deleteTuple i f))))
  dsimp only at hface
  rw [hsec'] at hface
  exact hface

/-- Restriction of a global positive-twist section to a standard chart. -/
noncomputable def finitePolynomialPositiveTwistRestrictGlobal
    (m : ℕ) (s : (positiveSheafOfModules PS m).sections) (i : σ) :
    Γ(positiveSheafOfModules PS m, finitePolynomialStandardOpen (K := K) i) :=
  (positiveModulePresheaf PS m).presheaf.map
    (homOfLE (show finitePolynomialStandardOpen (K := K) i ≤ ⊤ from le_top)).op
    (PresheafOfModules.sections.eval s (op (⊤ : Opens (Proj PS))))

lemma finitePolynomialPositiveTwistRestrictGlobal_eq_eval
    (m : ℕ) (s : (positiveSheafOfModules PS m).sections) (i : σ) :
    finitePolynomialPositiveTwistRestrictGlobal K m s i =
      PresheafOfModules.sections.eval s
        (op (finitePolynomialStandardOpen (K := K) i)) := by
  exact PresheafOfModules.sections_property s
    (homOfLE (show finitePolynomialStandardOpen (K := K) i ≤ ⊤ from le_top)).op

/-- The Laurent representative of a positive-twist section on a standard
chart, after restoring the chart basis `X_i^m`. -/
noncomputable def finitePolynomialPositiveTwistGlobalCechChartBase
    (m n : ℕ) (f : Fin (n + 1) → σ)
    (s : (positiveSheafOfModules PS m).sections) :
    FinitePolynomialLaurentLocalization.LaurentPolynomial (σ := σ) K :=
  awayToLaurent (K := K) n f
    (finitePolynomialPositiveTwistChartAway K n f m (f 0)
      (finitePolynomialCoordinate_zero_dvd_cechDenominator (K := K) n f)
      (PresheafOfModules.sections.eval s (op (finitePolynomialCechBasicOpen K n f))))

/-- The Laurent representative of a positive-twist section on a standard
chart, after restoring the chart basis `X_i^m`. -/
noncomputable def finitePolynomialPositiveTwistGlobalChartLaurent
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections) (i : σ) :
    FinitePolynomialLaurentLocalization.LaurentPolynomial (σ := σ) K :=
  finitePolynomialPositiveTwistGlobalCechChartBase K m 0 ![i] s *
    AddMonoidAlgebra.single (positiveTwistShift m i) 1

/-- Every monomial in a positive-twist chart representative has the twist
degree, and any negative exponent is confined to that chart's inverted
coordinate. -/
theorem finitePolynomialPositiveTwistGlobalChartLaurent_support
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections) (i : σ) :
    ∀ a ∈ (finitePolynomialPositiveTwistGlobalChartLaurent K m s i).coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ ({i} : Set (σ)) := by
  intro a ha
  let z : HomogeneousLocalization.Away PS
      (finitePolynomialCechDenominator (K := K) 0 ![i]) :=
    finitePolynomialPositiveTwistChartAway K 0 ![i] m (![i] 0)
      (finitePolynomialCoordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
      (PresheafOfModules.sections.eval s
        (op (finitePolynomialCechBasicOpen K 0 ![i])))
  change a ∈ (finitePolynomialPositiveTwistGlobalCechChartBase K m 0 ![i] s *
      AddMonoidAlgebra.single (positiveTwistShift m i) 1).coeff.support at ha
  change a ∈ (awayToLaurent (K := K) 0 ![i] z *
      AddMonoidAlgebra.single (positiveTwistShift m i) 1).coeff.support at ha
  obtain ⟨b, hb, rfl⟩ :=
    (FinitePolynomialTwistLaurent.mul_single_mem_support_iff (K := K)
      (awayToLaurent (K := K) 0 ![i] z)
      (positiveTwistShift m i) a).mp ha
  have hbase := awayToLaurent_support_properties (K := K) 0 ![i] z b hb
  constructor
  · rw [FinitePolynomialLaurentLocalization.totalDegree_add, hbase.1,
      FinitePolynomialTwistLaurent.totalDegree_positiveTwistShift]
    simp
  · have hneg :=
      (FinitePolynomialTwistLaurent.negativeSupport_add_positiveTwistShift_subset m i b).trans
        hbase.2
    simpa using hneg

/-- The restored Laurent representatives of a global positive-twist section
agree on all four standard coordinate charts. -/
theorem finitePolynomialPositiveTwistGlobalChartLaurent_eq
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections) (i j : σ) :
    finitePolynomialPositiveTwistGlobalChartLaurent K m s i =
      finitePolynomialPositiveTwistGlobalChartLaurent K m s j := by
  let pair : Fin 2 → σ := ![i, j]
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
  have hi := finitePolynomialPositiveTwistGlobalChartLaurent_restrict_face
    K m 0 faceI pair s
  have hj := finitePolynomialPositiveTwistGlobalChartLaurent_restrict_face
    K m 0 faceJ pair s
  let kI : σ := (deleteTuple faceI pair) 0
  let kJ : σ := (deleteTuple faceJ pair) 0
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
  change _ = finitePolynomialPositiveTwistGlobalCechChartBase K m 0
    (deleteTuple faceI pair) s *
      AddMonoidAlgebra.single (positiveTwistShift m kI) 1 at hi'
  change _ = finitePolynomialPositiveTwistGlobalCechChartBase K m 0
    (deleteTuple faceJ pair) s *
      AddMonoidAlgebra.single (positiveTwistShift m kJ) 1 at hj'
  have hbaseI := congrArg
    (fun t => finitePolynomialPositiveTwistGlobalCechChartBase K m 0 t s) hdelI
  have hbaseJ := congrArg
    (fun t => finitePolynomialPositiveTwistGlobalCechChartBase K m 0 t s) hdelJ
  have hind := finitePolynomialPositiveTwistChartLaurent_independent K 1 pair m kI
    (dvd_trans
      (finitePolynomialCoordinate_zero_dvd_cechDenominator
        (K := K) 0 (deleteTuple faceI pair))
      ⟨_, finitePolynomialCechDenominator_succ_eq_deleteTuple_mul
        (K := K) 0 faceI pair⟩) kJ
    (dvd_trans
      (finitePolynomialCoordinate_zero_dvd_cechDenominator
        (K := K) 0 (deleteTuple faceJ pair))
      ⟨_, finitePolynomialCechDenominator_succ_eq_deleteTuple_mul
        (K := K) 0 faceJ pair⟩)
    (PresheafOfModules.sections.eval s (op (finitePolynomialCechBasicOpen K 1 pair)))
  calc
    finitePolynomialPositiveTwistGlobalChartLaurent K m s i =
        finitePolynomialPositiveTwistGlobalCechChartBase K m 0
            (deleteTuple faceI pair) s *
          AddMonoidAlgebra.single (positiveTwistShift m kI) 1 := by
      rw [finitePolynomialPositiveTwistGlobalChartLaurent, hbaseI, hkI]
    _ = awayToLaurent (K := K) 1 pair
          (finitePolynomialPositiveTwistChartAway K 1 pair m kI
            (dvd_trans
              (finitePolynomialCoordinate_zero_dvd_cechDenominator
                (K := K) 0 (deleteTuple faceI pair))
              ⟨_, finitePolynomialCechDenominator_succ_eq_deleteTuple_mul
                (K := K) 0 faceI pair⟩)
            (PresheafOfModules.sections.eval s
              (op (finitePolynomialCechBasicOpen K 1 pair)))) *
          AddMonoidAlgebra.single (positiveTwistShift m kI) 1 := hi'.symm
    _ = awayToLaurent (K := K) 1 pair
          (finitePolynomialPositiveTwistChartAway K 1 pair m kJ
            (dvd_trans
              (finitePolynomialCoordinate_zero_dvd_cechDenominator
                (K := K) 0 (deleteTuple faceJ pair))
              ⟨_, finitePolynomialCechDenominator_succ_eq_deleteTuple_mul
                (K := K) 0 faceJ pair⟩)
            (PresheafOfModules.sections.eval s
              (op (finitePolynomialCechBasicOpen K 1 pair)))) *
          AddMonoidAlgebra.single (positiveTwistShift m kJ) 1 := hind
    _ = finitePolynomialPositiveTwistGlobalCechChartBase K m 0
            (deleteTuple faceJ pair) s *
          AddMonoidAlgebra.single (positiveTwistShift m kJ) 1 := hj'
    _ = finitePolynomialPositiveTwistGlobalChartLaurent K m s j := by
      rw [finitePolynomialPositiveTwistGlobalChartLaurent, hbaseJ, hkJ]

/-- The chart Laurent representative of the global section attached to a
homogeneous polynomial is the Laurent image of that polynomial. -/
theorem finitePolynomialPositiveTwistGlobalChartLaurent_of_homogeneous
    (m : ℕ) (p : PS m) (i : σ) :
    finitePolynomialPositiveTwistGlobalChartLaurent K m
        (positiveGlobalSectionOfHomogeneous PS m p) i =
      polynomialToLaurent (K := K) (p : MvPolynomial (σ) K) := by
  let t : Fin 1 → σ := ![i]
  let s := positiveGlobalSectionOfHomogeneous PS m p
  let z := finitePolynomialPositiveTwistChartAway K 0 t m (t 0)
    (finitePolynomialCoordinate_zero_dvd_cechDenominator (K := K) 0 t)
    (PresheafOfModules.sections.eval s (op (finitePolynomialCechBasicOpen K 0 t)))
  have hval := genericLocalizationMap_finitePolynomialPositiveTwistChartAway K 0 t m (t 0)
    (finitePolynomialCoordinate_zero_dvd_cechDenominator (K := K) 0 t)
    (PresheafOfModules.sections.eval s (op (finitePolynomialCechBasicOpen K 0 t)))
  have hgen := awayToSection_positiveGeneric_apply K 0 t z
  change ((((ProjectiveSpectrum.Proj.awayToSection PS
      (finitePolynomialCechDenominator (K := K) 0 t)).1 z).val
        (cechGenericPoint K 0 t)).val) = _ at hgen
  change _ = _ *
    (((ProjectiveSpectrum.Proj.awayToSection PS
      (finitePolynomialCechDenominator (K := K) 0 t)).1 z).val
        (cechGenericPoint K 0 t)).val at hval
  rw [hgen] at hval
  have hcross : z.val *
        algebraMap (MvPolynomial (σ) K)
          (Localization.Away (finitePolynomialCechDenominator (K := K) 0 t))
          ((degreeOnePower PS (finitePolynomialCoordinate K (t 0)) m : PS m) :
            MvPolynomial (σ) K) =
      algebraMap (MvPolynomial (σ) K)
        (Localization.Away (finitePolynomialCechDenominator (K := K) 0 t))
        (p : MvPolynomial (σ) K) := by
    apply positiveGenericLocalizationMap_injective K 0 t
    rw [map_mul, positiveGenericLocalizationMap_algebraMap K 0 t,
      positiveGenericLocalizationMap_algebraMap K 0 t]
    change positiveGenericLocalizationMap K 0 t z.val *
        algebraMap (MvPolynomial (σ) K)
          (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
          ((degreeOnePower PS (finitePolynomialCoordinate K (t 0)) m : PS m) :
            MvPolynomial (σ) K) =
      algebraMap (MvPolynomial (σ) K)
        (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
        (p : MvPolynomial (σ) K)
    calc
      _ = algebraMap (MvPolynomial (σ) K)
            (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
            ((degreeOnePower PS (finitePolynomialCoordinate K (t 0)) m : PS m) :
              MvPolynomial (σ) K) *
          positiveGenericLocalizationMap K 0 t z.val := mul_comm _ _
      _ = (PresheafOfModules.sections.eval s
            (op (finitePolynomialCechBasicOpen K 0 t))).1 (cechGenericPoint K 0 t) := hval.symm
      _ = Localization.mk (p : MvPolynomial (σ) K)
            ⟨1, Submonoid.one_mem _⟩ := rfl
      _ = _ := Localization.mk_one_eq_algebraMap _
  have hL := congrArg (localizationAwayToLaurent (K := K) 0 t) hcross
  simp only [map_mul, localizationAwayToLaurent_algebraMap,
    polynomialToLaurent_degreeOnePower K m] at hL
  change awayToLaurent (K := K) 0 t z *
      AddMonoidAlgebra.single (positiveTwistShift m (t 0)) 1 =
    polynomialToLaurent (K := K) (p : MvPolynomial (σ) K) at hL
  simpa [finitePolynomialPositiveTwistGlobalChartLaurent,
    finitePolynomialPositiveTwistGlobalCechChartBase, t, s, z] using hL

/-- A Laurent exponent which can have a negative coordinate only at every
one of two distinct coordinate indices has no negative coordinates. -/
lemma negativeSupport_eq_empty_of_subset_singletons
    (a : FinitePolynomialLaurentLocalization.LaurentExponent (σ := σ))
    (i₀ i₁ : σ) (hne : i₀ ≠ i₁)
    (h₀ : negativeSupport a ⊆ ({i₀} : Set (σ)))
    (h₁ : negativeSupport a ⊆ ({i₁} : Set (σ))) :
    negativeSupport a = ∅ := by
  ext j
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hj
  have hj₀ : j = i₀ := by simpa using h₀ hj
  have hj₁ : j = i₁ := by simpa using h₁ hj
  exact hne (hj₀.symm.trans hj₁)

/-- Once the Laurent representatives on all standard charts agree, their
common monomials are ordinary nonnegative monomials of degree `m`. -/
theorem finitePolynomialPositiveTwist_commonLaurent_support
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections)
    (g : FinitePolynomialLaurentLocalization.LaurentPolynomial (σ := σ) K)
    (hg : ∀ i, finitePolynomialPositiveTwistGlobalChartLaurent K m s i = g) :
    ∀ a ∈ g.coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a = ∅ := by
  intro a ha
  have hsupport (i : σ) :
      totalDegree a = (m : ℤ) ∧
        negativeSupport a ⊆ ({i} : Set (σ)) := by
    apply finitePolynomialPositiveTwistGlobalChartLaurent_support K m s i
    simpa [hg i] using ha
  obtain ⟨i₀, i₁, hne⟩ := exists_pair_ne σ
  exact ⟨(hsupport i₀).1,
    negativeSupport_eq_empty_of_subset_singletons a i₀ i₁ hne
      (hsupport i₀).2 (hsupport i₁).2⟩

/-- Convert a Laurent exponent known to be nonnegative coordinatewise into
an ordinary multivariate-polynomial exponent. -/
def nonnegativeExponentToNat
    (a : FinitePolynomialLaurentLocalization.LaurentExponent (σ := σ)) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ Int.toNat (a i)

@[simp] lemma nonnegativeExponentToNat_apply
    (a : FinitePolynomialLaurentLocalization.LaurentExponent (σ := σ)) (i : σ) :
    nonnegativeExponentToNat a i = Int.toNat (a i) := rfl

lemma exponentToInt_nonnegativeExponentToNat
    (a : FinitePolynomialLaurentLocalization.LaurentExponent (σ := σ))
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
    (a : FinitePolynomialLaurentLocalization.LaurentExponent (σ := σ)) (m : ℕ)
    (hdegree : totalDegree a = (m : ℤ))
    (ha : negativeSupport a = ∅) :
    (nonnegativeExponentToNat a).degree = m := by
  have htotal := totalDegree_exponentToInt (nonnegativeExponentToNat a)
  rw [exponentToInt_nonnegativeExponentToNat a ha, hdegree] at htotal
  rw [Finsupp.degree_apply, ← finsupp_sum_eq_sum_support]
  exact_mod_cast htotal.symm

lemma nonnegativeLaurentMonomial_mem_homogeneous
    (a : FinitePolynomialLaurentLocalization.LaurentExponent (σ := σ)) (c : K) (m : ℕ)
    (hdegree : totalDegree a = (m : ℤ))
    (ha : negativeSupport a = ∅) :
    MvPolynomial.monomial (nonnegativeExponentToNat a) c ∈ PS m := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_monomial c
    (nonnegativeExponentToNat_degree a m hdegree ha)

/-- The ordinary polynomial obtained by interpreting every nonnegative
Laurent exponent as a natural exponent. -/
noncomputable def polynomialOfNonnegativeLaurent
    (g : FinitePolynomialLaurentLocalization.LaurentPolynomial (σ := σ) K) :
    MvPolynomial (σ) K :=
  ∑ a ∈ g.coeff.support,
    MvPolynomial.monomial (nonnegativeExponentToNat a) (g.coeff a)

/-- A Laurent polynomial supported in nonnegative degree-`m` exponents is
the Laurent image of an actual homogeneous polynomial of degree `m`. -/
theorem polynomialOfNonnegativeLaurent_mem_and_map
    (g : FinitePolynomialLaurentLocalization.LaurentPolynomial (σ := σ) K) (m : ℕ)
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
    (g : FinitePolynomialLaurentLocalization.LaurentPolynomial (σ := σ) K)
    (hg : ∀ i, finitePolynomialPositiveTwistGlobalChartLaurent K m s i = g) :
    ∃ p : PS m, polynomialToLaurent (K := K) (p : MvPolynomial (σ) K) = g := by
  let p := polynomialOfNonnegativeLaurent K g
  have hp := polynomialOfNonnegativeLaurent_mem_and_map K g m
    (finitePolynomialPositiveTwist_commonLaurent_support K m s g hg)
  exact ⟨⟨p, hp.1⟩, hp.2⟩

/-- Every global positive-twist section determines a homogeneous polynomial
with the same Laurent representative on every standard chart. -/
theorem exists_homogeneous_polynomial_of_positiveTwist
    (m : ℕ)
    (s : (positiveSheafOfModules PS m).sections) :
    ∃ p : PS m, ∀ i,
      polynomialToLaurent (K := K) (p : MvPolynomial (σ) K) =
        finitePolynomialPositiveTwistGlobalChartLaurent K m s i := by
  obtain ⟨p, hp⟩ :=
    exists_homogeneous_polynomial_of_positiveTwist_commonLaurent
      K m s (finitePolynomialPositiveTwistGlobalChartLaurent K m s (Classical.arbitrary σ))
      (fun i => finitePolynomialPositiveTwistGlobalChartLaurent_eq K m s i (Classical.arbitrary σ))
  exact ⟨p, fun i => hp.trans
    (finitePolynomialPositiveTwistGlobalChartLaurent_eq K m s (Classical.arbitrary σ) i)⟩

lemma eq_of_mul_positiveTwistShift_eq
    (m : ℕ) (i : σ)
    {a b : FinitePolynomialLaurentLocalization.LaurentPolynomial (σ := σ) K}
    (h : a * AddMonoidAlgebra.single (positiveTwistShift m i) 1 =
      b * AddMonoidAlgebra.single (positiveTwistShift m i) 1) :
    a = b := by
  let p := AddMonoidAlgebra.single (positiveTwistShift m i) (1 : K)
  let q := AddMonoidAlgebra.single (twistShift m i) (1 : K)
  change a * p = b * p at h
  calc
    a = a * 1 := by rw [mul_one]
    _ = a * (p * q) := by rw [FinitePolynomialTwistLaurent.positiveTwistShift_mul_twistShift K m i]
    _ = (a * p) * q := by ring
    _ = (b * p) * q := by rw [h]
    _ = b * (p * q) := by ring
    _ = b := by rw [FinitePolynomialTwistLaurent.positiveTwistShift_mul_twistShift K m i, mul_one]

/-- Equality of restored Laurent representatives on one coordinate chart
implies equality of the two section restrictions to that chart. -/
lemma finitePolynomialPositiveTwist_restrict_eq_of_chartLaurent_eq
    (m : ℕ)
    (s t : (positiveSheafOfModules PS m).sections) (i : σ)
    (h : finitePolynomialPositiveTwistGlobalChartLaurent K m s i =
      finitePolynomialPositiveTwistGlobalChartLaurent K m t i) :
    PresheafOfModules.sections.eval s (op (finitePolynomialCechBasicOpen K 0 ![i])) =
      PresheafOfModules.sections.eval t (op (finitePolynomialCechBasicOpen K 0 ![i])) := by
  have hbase : finitePolynomialPositiveTwistGlobalCechChartBase K m 0 ![i] s =
      finitePolynomialPositiveTwistGlobalCechChartBase K m 0 ![i] t := by
    apply eq_of_mul_positiveTwistShift_eq K m i
    simpa only [finitePolynomialPositiveTwistGlobalChartLaurent] using h
  have haway :
      finitePolynomialPositiveTwistChartAway K 0 ![i] m (![i] 0)
          (finitePolynomialCoordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
          (PresheafOfModules.sections.eval s
            (op (finitePolynomialCechBasicOpen K 0 ![i]))) =
        finitePolynomialPositiveTwistChartAway K 0 ![i] m (![i] 0)
          (finitePolynomialCoordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
          (PresheafOfModules.sections.eval t
            (op (finitePolynomialCechBasicOpen K 0 ![i]))) := by
    apply awayToLaurent_injective (K := K) 0 ![i]
    simpa only [finitePolynomialPositiveTwistGlobalCechChartBase] using hbase
  let e := finitePolynomialPositiveTwistBasicOpenIsoAway K
    (finitePolynomialCechDenominator (K := K) 0 ![i]) 1
    (finitePolynomialCechDenominator_mem (K := K) 0 ![i]) (by decide)
    (![i] 0) (finitePolynomialCoordinate_zero_dvd_cechDenominator (K := K) 0 ![i]) m
  change e.hom (PresheafOfModules.sections.eval s
      (op (finitePolynomialCechBasicOpen K 0 ![i]))) =
    e.hom (PresheafOfModules.sections.eval t
      (op (finitePolynomialCechBasicOpen K 0 ![i]))) at haway
  have hinv := congrArg (fun q => e.inv q) haway
  have hinv' :
      e.inv (e.hom (PresheafOfModules.sections.eval s
        (op (finitePolynomialCechBasicOpen K 0 ![i])))) =
      e.inv (e.hom (PresheafOfModules.sections.eval t
        (op (finitePolynomialCechBasicOpen K 0 ![i])))) := hinv
  have hs := e.hom_inv_id_apply
    (PresheafOfModules.sections.eval s (op (finitePolynomialCechBasicOpen K 0 ![i])))
  have ht := e.hom_inv_id_apply
    (PresheafOfModules.sections.eval t (op (finitePolynomialCechBasicOpen K 0 ![i])))
  exact hs.symm.trans (hinv'.trans ht)

lemma finitePolynomialCechSingleOpen_eq_standard (i : σ) :
    finitePolynomialCechBasicOpen K 0 ![i] = finitePolynomialStandardOpen (K := K) i := by
  change AlgebraicGeometry.Proj.basicOpen PS
      (finitePolynomialCechDenominator (K := K) 0 ![i]) =
    AlgebraicGeometry.Proj.basicOpen PS (MvPolynomial.X i)
  congr 1
  simp [finitePolynomialCechDenominator]

lemma finitePolynomialCechSingleOpen_iSup :
    ⨆ i : σ, finitePolynomialCechBasicOpen K 0 ![i] = ⊤ := by
  simp_rw [finitePolynomialCechSingleOpen_eq_standard K]
  exact finitePolynomialStandardOpen_iSup K

/-- Global positive-twist sections are determined by their standard restored
Laurent chart representatives. -/
theorem finitePolynomialPositiveTwist_global_eq_of_chartLaurent_eq
    (m : ℕ)
    (s t : (positiveSheafOfModules PS m).sections)
    (h : ∀ i, finitePolynomialPositiveTwistGlobalChartLaurent K m s i =
      finitePolynomialPositiveTwistGlobalChartLaurent K m t i) :
    s = t := by
  let M := positiveSheafOfModules PS m
  let G : TopCat.Sheaf AddCommGrpCat (Proj PS) :=
    (SheafOfModules.toSheaf (Proj PS).ringCatSheaf).obj M
  have htop : PresheafOfModules.sections.eval s
        (op (⊤ : Opens (Proj PS))) =
      PresheafOfModules.sections.eval t
        (op (⊤ : Opens (Proj PS))) := by
    apply G.eq_of_locally_eq'
      (fun i : σ => finitePolynomialCechBasicOpen K 0 ![i])
      (⊤ : Opens (Proj PS))
      (fun _ => homOfLE le_top)
      (by rw [finitePolynomialCechSingleOpen_iSup K])
    intro i
    change (positiveSheafOfModules PS m).presheaf.map
        (homOfLE (show finitePolynomialCechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval s
            (op (⊤ : Opens (Proj PS)))) =
      (positiveSheafOfModules PS m).presheaf.map
        (homOfLE (show finitePolynomialCechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval t
            (op (⊤ : Opens (Proj PS))))
    have hsres : (positiveSheafOfModules PS m).presheaf.map
          (homOfLE (show finitePolynomialCechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval s
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval s
          (op (finitePolynomialCechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property s _
    have htres : (positiveSheafOfModules PS m).presheaf.map
          (homOfLE (show finitePolynomialCechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval t
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval t
          (op (finitePolynomialCechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property t _
    rw [hsres, htres]
    exact finitePolynomialPositiveTwist_restrict_eq_of_chartLaurent_eq K m s t i (h i)
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
twist on projective space. -/
theorem finitePolynomial_positiveGlobalSectionOfHomogeneous_surjective
    (m : ℕ) :
    Function.Surjective (positiveGlobalSectionOfHomogeneous PS m) := by
  intro s
  obtain ⟨p, hp⟩ := exists_homogeneous_polynomial_of_positiveTwist K m s
  refine ⟨p, ?_⟩
  apply finitePolynomialPositiveTwist_global_eq_of_chartLaurent_eq K m
  intro i
  exact (finitePolynomialPositiveTwistGlobalChartLaurent_of_homogeneous K m p i).trans
    (hp i)


/-- The map to actual compatible global sections is injective by the native chart formula. -/
theorem finitePolynomial_positiveGlobalSectionOfHomogeneous_injective
    (m : ℕ) : Function.Injective (positiveGlobalSectionOfHomogeneous PS m) := by
  intro p q h
  have hL := congrArg
    (fun s => finitePolynomialPositiveTwistGlobalChartLaurent K m s (Classical.arbitrary σ)) h
  rw [finitePolynomialPositiveTwistGlobalChartLaurent_of_homogeneous,
    finitePolynomialPositiveTwistGlobalChartLaurent_of_homogeneous] at hL
  exact Subtype.ext (polynomialToLaurent_injective (K := K) hL)

/-- All positive native twists, including degree zero, have exactly homogeneous-polynomial sections. -/
def finitePolynomialHomogeneousSectionsEquiv (m : ℕ) :
    PS m ≃ (positiveSheafOfModules PS m).sections :=
  Equiv.ofBijective (positiveGlobalSectionOfHomogeneous PS m)
    ⟨finitePolynomial_positiveGlobalSectionOfHomogeneous_injective K m,
      finitePolynomial_positiveGlobalSectionOfHomogeneous_surjective K m⟩

end PfaffianDescent.ProjectiveFiniteNative

end
