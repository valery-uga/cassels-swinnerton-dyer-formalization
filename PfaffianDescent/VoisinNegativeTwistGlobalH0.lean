import PfaffianDescent.VoisinNegativeTwistCechH0
import PfaffianDescent.VoisinTwistCechFaceNaturality

/-!
# Global sections of negative twists on projective three-space

The Laurent representatives of a global section agree on overlaps. Since a
negative-twist representative is constrained to have its negative exponents
in the chart's inverted coordinate, compatibility across two distinct
charts forces every exponent to be nonnegative. Strictly negative total
degree then makes every representative zero.
-/

noncomputable section

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open LaurentLocalization TwistLaurent TwistCechTerms
open TwistCechTerms.GenericEvaluation

universe u

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The Laurent representative of a global negative-twist section on one
ordered standard-cover intersection. -/
noncomputable def p3NegativeTwistGlobalCechLaurent
    (m n : ℕ) (f : Fin (n + 1) → Fin 4)
    (s : (sheafOfModules PS m).sections) :
    LaurentLocalization.LaurentPolynomial K :=
  twistAwayToLaurent (K := K) m n f
    (chartAway K n f m (f 0)
      (p3Coordinate_zero_dvd_cechDenominator (K := K) n f)
      (PresheafOfModules.sections.eval s (op (cechBasicOpen K n f))))

/-- Every monomial in a global section's local representative has the
negative twist degree and can have negative exponents only in the inverted
coordinates of that chart. -/
theorem p3NegativeTwistGlobalCechLaurent_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 4)
    (s : (sheafOfModules PS m).sections) :
    ∀ a ∈ (p3NegativeTwistGlobalCechLaurent K m n f s).coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  exact twistAwayToLaurent_support_properties (K := K) m n f
    (chartAway K n f m (f 0)
      (p3Coordinate_zero_dvd_cechDenominator (K := K) n f)
      (PresheafOfModules.sections.eval s (op (cechBasicOpen K n f))))

/-- Restricting a global section along a Čech face leaves its Laurent
representative unchanged. -/
theorem p3NegativeTwistGlobalCechLaurent_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4)
    (s : (sheafOfModules PS m).sections) :
    p3NegativeTwistGlobalCechLaurent K m (n + 1) f s =
      p3NegativeTwistGlobalCechLaurent K m n (deleteTuple i f) s := by
  let hST : cechBasicOpen K (n + 1) f ≤
      cechBasicOpen K n (deleteTuple i f) :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (p3CechDenominator (K := K) n (deleteTuple i f))
      (p3CechDenominator (K := K) (n + 1) f)
      ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul K n i f⟩
  have hsec' :
      (sheafOfModules PS m).presheaf.map (homOfLE hST).op
        (PresheafOfModules.sections.eval s
          (op (cechBasicOpen K n (deleteTuple i f)))) =
      PresheafOfModules.sections.eval s
        (op (cechBasicOpen K (n + 1) f)) :=
    PresheafOfModules.sections_property s (homOfLE hST).op
  have hface := twistAwayToLaurent_restrict_face K m n i f
    (PresheafOfModules.sections.eval s
      (op (cechBasicOpen K n (deleteTuple i f))))
  dsimp only at hface
  rw [hsec'] at hface
  exact hface

/-- The Laurent representatives of a global section on any two standard
coordinate charts are equal. -/
theorem p3NegativeTwistGlobalChartLaurent_eq
    (m : ℕ) (s : (sheafOfModules PS m).sections) (i j : Fin 4) :
    p3NegativeTwistGlobalCechLaurent K m 0 ![i] s =
      p3NegativeTwistGlobalCechLaurent K m 0 ![j] s := by
  let pair : Fin 2 → Fin 4 := ![i, j]
  have hdelI : deleteTuple (1 : Fin 2) pair = ![i] := by
    funext k
    fin_cases k
    rfl
  have hdelJ : deleteTuple (0 : Fin 2) pair = ![j] := by
    funext k
    fin_cases k
    rfl
  calc
    p3NegativeTwistGlobalCechLaurent K m 0 ![i] s =
        p3NegativeTwistGlobalCechLaurent K m 1 pair s := by
      rw [← hdelI]
      exact (p3NegativeTwistGlobalCechLaurent_face K m 0 1 pair s).symm
    _ = p3NegativeTwistGlobalCechLaurent K m 0 ![j] s := by
      rw [← hdelJ]
      exact p3NegativeTwistGlobalCechLaurent_face K m 0 0 pair s

/-- Every standard-chart Laurent representative of a section of `O(-m)`
vanishes when `m > 0`. -/
theorem p3NegativeTwistGlobalChartLaurent_eq_zero
    (m : ℕ) (hm : 0 < m)
    (s : (sheafOfModules PS m).sections) (i : Fin 4) :
    p3NegativeTwistGlobalCechLaurent K m 0 ![i] s = 0 := by
  let g := p3NegativeTwistGlobalCechLaurent K m 0 ![i] s
  apply laurent_eq_zero_of_negative_degree_and_nonnegative_support K m hm g
  intro a ha
  have hi := p3NegativeTwistGlobalCechLaurent_support K m 0 ![i] s a ha
  have haone : a ∈
      (p3NegativeTwistGlobalCechLaurent K m 0 ![1] s).coeff.support := by
    rw [← p3NegativeTwistGlobalChartLaurent_eq K m s i 1]
    exact ha
  have hj := p3NegativeTwistGlobalCechLaurent_support K m 0 ![1] s a haone
  by_cases h : i = 1
  · subst i
    have hazero : a ∈
        (p3NegativeTwistGlobalCechLaurent K m 0 ![0] s).coeff.support := by
      rw [← p3NegativeTwistGlobalChartLaurent_eq K m s 1 0]
      exact ha
    have hk := p3NegativeTwistGlobalCechLaurent_support K m 0 ![0] s a hazero
    refine ⟨hi.1, ?_⟩
    exact negativeSupport_eq_empty_of_subset_singletons a
      (by simpa using hk.2) (by simpa using hj.2)
  · refine ⟨hi.1, ?_⟩
    ext k
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hk
    have hki : k = i := by simpa using hi.2 hk
    have hk1 : k = 1 := by simpa using hj.2 hk
    exact h (hki.symm.trans hk1)

/-- A strictly negative twist on projective three-space has no nonzero
global sections. -/
theorem p3_negativeTwist_sections_subsingleton_of_pos
    (m : ℕ) (hm : 0 < m) :
    Subsingleton (sheafOfModules PS m).sections := by
  refine ⟨fun s t => ?_⟩
  have hlocal (i : Fin 4) :
      PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 ![i])) =
        PresheafOfModules.sections.eval t (op (cechBasicOpen K 0 ![i])) := by
    have hlaurent :
        p3NegativeTwistGlobalCechLaurent K m 0 ![i] s =
          p3NegativeTwistGlobalCechLaurent K m 0 ![i] t := by
      rw [p3NegativeTwistGlobalChartLaurent_eq_zero K m hm s i,
        p3NegativeTwistGlobalChartLaurent_eq_zero K m hm t i]
    have haway :
        chartAway K 0 ![i] m i
            (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
            (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 ![i]))) =
          chartAway K 0 ![i] m i
            (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
            (PresheafOfModules.sections.eval t (op (cechBasicOpen K 0 ![i]))) := by
      apply twistAwayToLaurent_injective (K := K) m 0 ![i]
      exact hlaurent
    let e := p3NegativeTwistBasicOpenIsoAway K
      (p3CechDenominator (K := K) 0 ![i]) 1
      (p3CechDenominator_mem (K := K) 0 ![i]) (by decide)
      i (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i]) m
    change e.hom
        (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 ![i]))) =
      e.hom
        (PresheafOfModules.sections.eval t (op (cechBasicOpen K 0 ![i])))
      at haway
    exact (ConcreteCategory.bijective_of_isIso e.hom).1 haway
  let M := sheafOfModules PS m
  let G : TopCat.Sheaf AddCommGrpCat (Proj PS) :=
    (SheafOfModules.toSheaf (Proj PS).ringCatSheaf).obj M
  have htop : PresheafOfModules.sections.eval s
        (op (⊤ : Opens (Proj PS))) =
      PresheafOfModules.sections.eval t
        (op (⊤ : Opens (Proj PS))) := by
    apply G.eq_of_locally_eq'
      (fun i : Fin 4 => cechBasicOpen K 0 ![i])
      (⊤ : Opens (Proj PS))
      (fun _ => homOfLE le_top)
      (by rw [p3CechSingleOpen_iSup K])
    intro i
    change M.presheaf.map
        (homOfLE (show cechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval s
            (op (⊤ : Opens (Proj PS)))) =
      M.presheaf.map
        (homOfLE (show cechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval t
            (op (⊤ : Opens (Proj PS))))
    have hsres : M.presheaf.map
          (homOfLE (show cechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval s
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval s
          (op (cechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property s _
    have htres : M.presheaf.map
          (homOfLE (show cechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval t
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval t
          (op (cechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property t _
    rw [hsres, htres]
    exact hlocal i
  apply PresheafOfModules.sections_ext
  intro U
  let r := M.presheaf.map
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

end PfaffianDescent.ProjectiveNegativeTwist
