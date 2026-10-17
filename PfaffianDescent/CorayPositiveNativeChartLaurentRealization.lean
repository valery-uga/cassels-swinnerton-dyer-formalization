import PfaffianDescent.P3PositiveTwistGlobalSections

/-! Positive-twist Laurent representatives of ACTUAL native chart sections.
The inverse uses the existing actual chart frame and homogeneous localization,
not a supplied chart equivalence. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open LaurentLocalization TwistLaurent
open TwistCechTerms TwistCechTerms.GenericEvaluation
open scoped AddMonoidAlgebra BigOperators
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

private def p3PositiveAwayToLaurent
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    HomogeneousLocalization.Away PS (p3CechDenominator (K := K) n f) →+
      LaurentLocalization.LaurentPolynomial K where
  toFun z := awayToLaurent (K := K) n f z *
    AddMonoidAlgebra.single (positiveTwistShift m (f 0)) 1
  map_zero' := by simp
  map_add' x y := by simp [add_mul]

private theorem p3PositiveAwayToLaurent_injective
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    Function.Injective (p3PositiveAwayToLaurent K m n f) := by
  intro x y h
  apply awayToLaurent_injective (K := K) n f
  exact (isUnit_single_one (K := K) (positiveTwistShift m (f 0))).mul_right_cancel h

private theorem p3PositiveAwayToLaurent_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 4)
    (z : HomogeneousLocalization.Away PS (p3CechDenominator (K := K) n f)) :
    ∀ a ∈ (p3PositiveAwayToLaurent K m n f z).coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ :=
    (mul_single_mem_support_iff (K := K)
      (awayToLaurent (K := K) n f z) (positiveTwistShift m (f 0)) a).mp ha
  have hbase := awayToLaurent_support_properties (K := K) n f z b hb
  constructor
  · rw [totalDegree_add, hbase.1, totalDegree_positiveTwistShift]
    simp
  · exact (negativeSupport_add_positiveTwistShift_subset m (f 0) b).trans hbase.2

private theorem exists_p3PositiveAwayToLaurent_eq_of_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 4)
    (g : LaurentLocalization.LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ z : HomogeneousLocalization.Away PS (p3CechDenominator (K := K) n f),
      p3PositiveAwayToLaurent K m n f z = g := by
  let gneg := g * AddMonoidAlgebra.single (twistShift m (f 0)) 1
  have hgneg : ∀ a ∈ gneg.coeff.support,
      totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ :=
      (mul_single_mem_support_iff (K := K) g (twistShift m (f 0)) a).mp ha
    have hbase := hg b hb
    constructor
    · rw [totalDegree_add, hbase.1, totalDegree_twistShift]
      simp
    · exact negativeSupport_add_twistShift_subset n m f b hbase.2
  obtain ⟨z, hz⟩ := exists_awayToLaurent_eq_of_support (K := K) n f gneg hgneg
  refine ⟨z, ?_⟩
  change awayToLaurent (K := K) n f z *
    AddMonoidAlgebra.single (positiveTwistShift m (f 0)) 1 = g
  rw [hz]
  change (g * AddMonoidAlgebra.single (twistShift m (f 0)) 1) *
    AddMonoidAlgebra.single (positiveTwistShift m (f 0)) 1 = g
  rw [mul_assoc, twistShift_mul_positiveTwistShift K m (f 0), mul_one]

/-- Restoring the actual chart frame gives a positive-degree Laurent
representative of the SAME native positive-twist section. -/
def p3PositiveNativeChartToLaurent
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    Γ(positiveSheafOfModules PS m, cechBasicOpen K n f) →+
      LaurentLocalization.LaurentPolynomial K where
  toFun s := p3PositiveAwayToLaurent K m n f
    (p3PositiveTwistChartAway K n f m (f 0)
      (p3Coordinate_zero_dvd_cechDenominator (K := K) n f) s)
  map_zero' := by simp [p3PositiveTwistChartAway]
  map_add' x y := by simp [p3PositiveTwistChartAway]

/-- The actual native positive-chart Laurent map is injective. -/
theorem p3PositiveNativeChartToLaurent_injective
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    Function.Injective (p3PositiveNativeChartToLaurent K m n f) := by
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso
    (p3PositiveTwistBasicOpenIsoAway K (p3CechDenominator (K := K) n f)
      (n + 1) (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
      (f 0) (p3Coordinate_zero_dvd_cechDenominator (K := K) n f) m).hom).1
  exact p3PositiveAwayToLaurent_injective K m n f h

/-- Native chart representatives have exactly the prescribed total degree
and can have negative exponents only at the actually inverted coordinates. -/
theorem p3PositiveNativeChartToLaurent_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 4)
    (s : Γ(positiveSheafOfModules PS m, cechBasicOpen K n f)) :
    ∀ a ∈ (p3PositiveNativeChartToLaurent K m n f s).coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  exact p3PositiveAwayToLaurent_support K m n f
    (p3PositiveTwistChartAway K n f m (f 0)
      (p3Coordinate_zero_dvd_cechDenominator (K := K) n f) s)

/-- Every positive-degree Laurent representative with the actual coordinate
support comes from a section of the SAME native positive-twist sheaf. -/
theorem exists_p3PositiveNativeChartToLaurent_eq_of_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 4)
    (g : LaurentLocalization.LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ Set.range f) :
    ∃ s : Γ(positiveSheafOfModules PS m, cechBasicOpen K n f),
      p3PositiveNativeChartToLaurent K m n f s = g := by
  obtain ⟨z, hz⟩ := exists_p3PositiveAwayToLaurent_eq_of_support K m n f g hg
  let e := p3PositiveTwistBasicOpenIsoAway K (p3CechDenominator (K := K) n f)
    (n + 1) (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
    (f 0) (p3Coordinate_zero_dvd_cechDenominator (K := K) n f) m
  refine ⟨e.inv z, ?_⟩
  change p3PositiveAwayToLaurent K m n f (e.hom (e.inv z)) = g
  rw [Iso.inv_hom_id_apply]
  exact hz

/-- Actual positive-sheaf restriction along a coordinate-cover face is the
SAME Laurent representative. Both chart frames are internally derived. -/
theorem p3PositiveNativeChartToLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4)
    (s : Γ(positiveSheafOfModules PS m, cechBasicOpen K n (deleteTuple i f))) :
    let hST : cechBasicOpen K (n + 1) f ≤ cechBasicOpen K n (deleteTuple i f) :=
      AlgebraicGeometry.Proj.basicOpen_mono PS
        (p3CechDenominator (K := K) n (deleteTuple i f))
        (p3CechDenominator (K := K) (n + 1) f)
        ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
    p3PositiveNativeChartToLaurent K m (n + 1) f
        ((positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s) =
      p3PositiveNativeChartToLaurent K m n (deleteTuple i f) s := by
  dsimp only
  let del := deleteTuple i f
  let hx := p3CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f
  let hdiv := dvd_trans (p3Coordinate_zero_dvd_cechDenominator (K := K) n del) ⟨_, hx⟩
  let hST : cechBasicOpen K (n + 1) f ≤ cechBasicOpen K n del :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (p3CechDenominator (K := K) n del) (p3CechDenominator (K := K) (n + 1) f) ⟨_, hx⟩
  let sT := (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s
  have hind := p3PositiveTwistChartLaurent_independent K (n + 1) f m
    (f 0) (p3Coordinate_zero_dvd_cechDenominator (K := K) (n + 1) f)
    (del 0) hdiv sT
  have hface := p3PositiveTwistChartLaurent_restrict_face K m n i f s
  calc
    p3PositiveNativeChartToLaurent K m (n + 1) f sT =
        awayToLaurent (K := K) (n + 1) f
          (p3PositiveTwistChartAway K (n + 1) f m (del 0) hdiv sT) *
          AddMonoidAlgebra.single (positiveTwistShift m (del 0)) 1 := hind
    _ = awayToLaurent (K := K) n del
          (p3PositiveTwistChartAway K n del m (del 0)
            (p3Coordinate_zero_dvd_cechDenominator (K := K) n del) s) *
          AddMonoidAlgebra.single (positiveTwistShift m (del 0)) 1 :=
      congrArg (fun z => z * AddMonoidAlgebra.single (positiveTwistShift m (del 0)) 1) hface
    _ = p3PositiveNativeChartToLaurent K m n del s := rfl

end PfaffianDescent.ProjectiveNegativeTwist
