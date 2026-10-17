import PfaffianDescent.PlanePositiveTwistGlobalSections
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-!
# Global sections of negative twists on projective three-space

The Laurent representatives of a global section agree on overlaps. Since a
negative-twist representative is constrained to have its negative exponents
in the chart's inverted coordinate, compatibility across two distinct
charts forces every exponent to be nonnegative. Strictly negative total
degree then makes every representative zero.
-/

noncomputable section

namespace PfaffianDescent.ProjectivePlaneNative

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist PlaneLaurentLocalization PlaneTwistLaurent PlaneTwistCechTerms
open PlaneTwistCechTerms.GenericEvaluation

universe u

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K

/-- A Laurent polynomial of negative total degree whose monomials all have
nonnegative exponents is zero. -/
theorem laurent_eq_zero_of_negative_degree_and_nonnegative_support
    (m : ℕ) (hm : 0 < m)
    (g : PlaneLaurentLocalization.LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      PlaneLaurentLocalization.totalDegree a = -(m : ℤ) ∧ negativeSupport a = ∅) :
    g = 0 := by
  ext a
  by_contra ha
  have hmem : a ∈ g.coeff.support := Finsupp.mem_support_iff.mpr ha
  obtain ⟨hdegree, hsupport⟩ := hg a hmem
  have hnonneg (i : Fin 3) : 0 ≤ a i := by
    by_contra hi
    have hineg : i ∈ negativeSupport a := by
      change a i < 0
      omega
    rw [hsupport] at hineg
    simp at hineg
  have htotal : 0 ≤ PlaneLaurentLocalization.totalDegree a := by
    unfold PlaneLaurentLocalization.totalDegree
    exact Finset.sum_nonneg fun i _ => hnonneg i
  omega


/-- The Laurent representative of a global negative-twist section on one
ordered standard-cover intersection. -/
noncomputable def p2NegativeTwistGlobalCechLaurent
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (s : (sheafOfModules PS m).sections) :
    PlaneLaurentLocalization.LaurentPolynomial K :=
  twistAwayToLaurent (K := K) m n f
    (chartAway K n f m (f 0)
      (p2Coordinate_zero_dvd_cechDenominator (K := K) n f)
      (PresheafOfModules.sections.eval s (op (p2CechBasicOpen K n f))))

/-- Every monomial in a global section's local representative has the
negative twist degree and can have negative exponents only in the inverted
coordinates of that chart. -/
theorem p2NegativeTwistGlobalCechLaurent_support
    (m n : ℕ) (f : Fin (n + 1) → Fin 3)
    (s : (sheafOfModules PS m).sections) :
    ∀ a ∈ (p2NegativeTwistGlobalCechLaurent K m n f s).coeff.support,
      totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
  exact twistAwayToLaurent_support_properties (K := K) m n f
    (chartAway K n f m (f 0)
      (p2Coordinate_zero_dvd_cechDenominator (K := K) n f)
      (PresheafOfModules.sections.eval s (op (p2CechBasicOpen K n f))))

/-- Restricting a global section along a Čech face leaves its Laurent
representative unchanged. -/
theorem p2NegativeTwistGlobalCechLaurent_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3)
    (s : (sheafOfModules PS m).sections) :
    p2NegativeTwistGlobalCechLaurent K m (n + 1) f s =
      p2NegativeTwistGlobalCechLaurent K m n (deleteTuple i f) s := by
  let hST : p2CechBasicOpen K (n + 1) f ≤
      p2CechBasicOpen K n (deleteTuple i f) :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (p2CechDenominator (K := K) n (deleteTuple i f))
      (p2CechDenominator (K := K) (n + 1) f)
      ⟨_, p2CechDenominator_succ_eq_deleteTuple_mul K n i f⟩
  have hsec' :
      (sheafOfModules PS m).presheaf.map (homOfLE hST).op
        (PresheafOfModules.sections.eval s
          (op (p2CechBasicOpen K n (deleteTuple i f)))) =
      PresheafOfModules.sections.eval s
        (op (p2CechBasicOpen K (n + 1) f)) :=
    PresheafOfModules.sections_property s (homOfLE hST).op
  have hface := twistAwayToLaurent_restrict_face K m n i f
    (PresheafOfModules.sections.eval s
      (op (p2CechBasicOpen K n (deleteTuple i f))))
  dsimp only at hface
  rw [hsec'] at hface
  exact hface

/-- The Laurent representatives of a global section on any two standard
coordinate charts are equal. -/
theorem p2NegativeTwistGlobalChartLaurent_eq
    (m : ℕ) (s : (sheafOfModules PS m).sections) (i j : Fin 3) :
    p2NegativeTwistGlobalCechLaurent K m 0 ![i] s =
      p2NegativeTwistGlobalCechLaurent K m 0 ![j] s := by
  let pair : Fin 2 → Fin 3 := ![i, j]
  have hdelI : deleteTuple (1 : Fin 2) pair = ![i] := by
    funext k
    fin_cases k
    rfl
  have hdelJ : deleteTuple (0 : Fin 2) pair = ![j] := by
    funext k
    fin_cases k
    rfl
  calc
    p2NegativeTwistGlobalCechLaurent K m 0 ![i] s =
        p2NegativeTwistGlobalCechLaurent K m 1 pair s := by
      rw [← hdelI]
      exact (p2NegativeTwistGlobalCechLaurent_face K m 0 1 pair s).symm
    _ = p2NegativeTwistGlobalCechLaurent K m 0 ![j] s := by
      rw [← hdelJ]
      exact p2NegativeTwistGlobalCechLaurent_face K m 0 0 pair s

/-- Every standard-chart Laurent representative of a section of `O(-m)`
vanishes when `m > 0`. -/
theorem p2NegativeTwistGlobalChartLaurent_eq_zero
    (m : ℕ) (hm : 0 < m)
    (s : (sheafOfModules PS m).sections) (i : Fin 3) :
    p2NegativeTwistGlobalCechLaurent K m 0 ![i] s = 0 := by
  let g := p2NegativeTwistGlobalCechLaurent K m 0 ![i] s
  apply laurent_eq_zero_of_negative_degree_and_nonnegative_support K m hm g
  intro a ha
  have hi := p2NegativeTwistGlobalCechLaurent_support K m 0 ![i] s a ha
  have haone : a ∈
      (p2NegativeTwistGlobalCechLaurent K m 0 ![1] s).coeff.support := by
    rw [← p2NegativeTwistGlobalChartLaurent_eq K m s i 1]
    exact ha
  have hj := p2NegativeTwistGlobalCechLaurent_support K m 0 ![1] s a haone
  by_cases h : i = 1
  · subst i
    have hazero : a ∈
        (p2NegativeTwistGlobalCechLaurent K m 0 ![0] s).coeff.support := by
      rw [← p2NegativeTwistGlobalChartLaurent_eq K m s 1 0]
      exact ha
    have hk := p2NegativeTwistGlobalCechLaurent_support K m 0 ![0] s a hazero
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
theorem p2_negativeTwist_sections_subsingleton_of_pos
    (m : ℕ) (hm : 0 < m) :
    Subsingleton (sheafOfModules PS m).sections := by
  refine ⟨fun s t => ?_⟩
  have hlocal (i : Fin 3) :
      PresheafOfModules.sections.eval s (op (p2CechBasicOpen K 0 ![i])) =
        PresheafOfModules.sections.eval t (op (p2CechBasicOpen K 0 ![i])) := by
    have hlaurent :
        p2NegativeTwistGlobalCechLaurent K m 0 ![i] s =
          p2NegativeTwistGlobalCechLaurent K m 0 ![i] t := by
      rw [p2NegativeTwistGlobalChartLaurent_eq_zero K m hm s i,
        p2NegativeTwistGlobalChartLaurent_eq_zero K m hm t i]
    have haway :
        chartAway K 0 ![i] m i
            (p2Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
            (PresheafOfModules.sections.eval s (op (p2CechBasicOpen K 0 ![i]))) =
          chartAway K 0 ![i] m i
            (p2Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
            (PresheafOfModules.sections.eval t (op (p2CechBasicOpen K 0 ![i]))) := by
      apply twistAwayToLaurent_injective (K := K) m 0 ![i]
      exact hlaurent
    let e := p2NegativeTwistBasicOpenIsoAway K
      (p2CechDenominator (K := K) 0 ![i]) 1
      (p2CechDenominator_mem (K := K) 0 ![i]) (by decide)
      i (p2Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i]) m
    change e.hom
        (PresheafOfModules.sections.eval s (op (p2CechBasicOpen K 0 ![i]))) =
      e.hom
        (PresheafOfModules.sections.eval t (op (p2CechBasicOpen K 0 ![i])))
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
      (fun i : Fin 3 => p2CechBasicOpen K 0 ![i])
      (⊤ : Opens (Proj PS))
      (fun _ => homOfLE le_top)
      (by rw [p2CechSingleOpen_iSup K])
    intro i
    change M.presheaf.map
        (homOfLE (show p2CechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval s
            (op (⊤ : Opens (Proj PS)))) =
      M.presheaf.map
        (homOfLE (show p2CechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval t
            (op (⊤ : Opens (Proj PS))))
    have hsres : M.presheaf.map
          (homOfLE (show p2CechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval s
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval s
          (op (p2CechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property s _
    have htres : M.presheaf.map
          (homOfLE (show p2CechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval t
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval t
          (op (p2CechBasicOpen K 0 ![i])) :=
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

/-- No actual top-open negative section survives, independently of the
chosen original base-field action. -/
theorem p2_negativeTwist_topSections_subsingleton_of_pos
    (pi : Proj PS ⟶ Spec (CommRingCat.of K)) (m : ℕ) (hm : 0 < m) :
    Subsingleton (SchemeModuleOpenSectionsOver pi (sheafOfModules PS m) ⊤) := by
  letI : Subsingleton (sheafOfModules PS m).sections :=
    p2_negativeTwist_sections_subsingleton_of_pos K m hm
  exact (schemeModuleSectionsEquivTop (sheafOfModules PS m)).symm.injective.subsingleton

end PfaffianDescent.ProjectivePlaneNative
