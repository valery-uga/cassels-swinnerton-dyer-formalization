import PfaffianDescent.FinitePolynomialLaurentCharts
noncomputable section
namespace PfaffianDescent.ProjectiveFiniteNative
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist
open scoped BigOperators
universe u w
variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nontrivial σ]
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "S" => MvPolynomial (σ) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (σ) K
abbrev finitePolynomialCechBasicOpen (n : ℕ) (f : Fin (n + 1) → σ) :
    Scheme.Opens (Proj PS) := Proj.basicOpen PS (finitePolynomialCechDenominator (K := K) n f)

abbrev finitePolynomialPositiveTwistChartAway (n : ℕ) (f : Fin (n + 1) → σ)
    (m : ℕ) (i : σ) (hi : MvPolynomial.X i ∣ finitePolynomialCechDenominator (K := K) n f)
    (s : Γ(positiveSheafOfModules PS m, finitePolynomialCechBasicOpen K n f)) :
    HomogeneousLocalization.Away PS (finitePolynomialCechDenominator (K := K) n f) :=
  (finitePolynomialPositiveTwistBasicOpenIsoAway K (finitePolynomialCechDenominator (K := K) n f)
    (n + 1) (finitePolynomialCechDenominator_mem (K := K) n f) (Nat.succ_pos n) i hi m).hom s

end PfaffianDescent.ProjectiveFiniteNative
end
noncomputable section
namespace PfaffianDescent.FinitePolynomialTwistCechTerms
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open FinitePolynomialLaurentLocalization FinitePolynomialTwistLaurent ProjectiveNegativeTwist ProjectiveFiniteNative
universe u
variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nontrivial σ]
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "S" => MvPolynomial (σ) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (σ) K
def finitePolynomialGenericPoint : ProjectiveSpectrum PS where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot
  not_irrelevant_le := by
    intro h
    have hx : (MvPolynomial.X (Classical.arbitrary σ : σ) : S) ∈ (⊥ : HomogeneousIdeal PS) :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem PS (by decide : 0 < 1)
        (MvPolynomial.isHomogeneous_X K (Classical.arbitrary σ)))
    change (MvPolynomial.X (Classical.arbitrary σ : σ) : S) ∈ (⊥ : Ideal S) at hx
    exact MvPolynomial.X_ne_zero (Classical.arbitrary σ) (Ideal.mem_bot.mp hx)

@[simp] lemma finitePolynomialGenericPoint_asHomogeneousIdeal :
    (finitePolynomialGenericPoint (σ := σ) K).asHomogeneousIdeal = ⊥ := rfl

@[simp] lemma finitePolynomialGenericPoint_pointIdeal :
    pointIdeal PS (finitePolynomialGenericPoint (σ := σ) K) = ⊥ := by
  simp [pointIdeal, finitePolynomialGenericPoint]

lemma finitePolynomialGenericPoint_mem_basicOpen_cechDenominator
    (n : ℕ) (f : Fin (n + 1) → σ) :
    finitePolynomialGenericPoint (σ := σ) K ∈ AlgebraicGeometry.Proj.basicOpen PS
      (finitePolynomialCechDenominator (K := K) n f) := by
  change finitePolynomialCechDenominator (K := K) n f ∉
    (finitePolynomialGenericPoint (σ := σ) K).asHomogeneousIdeal
  change finitePolynomialCechDenominator (K := K) n f ∉ (⊥ : Ideal S)
  rw [Ideal.mem_bot]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => MvPolynomial.X_ne_zero (f i))

namespace GenericEvaluation
variable (n : ℕ) (f : Fin (n + 1) → σ)
local notation "D" => finitePolynomialCechDenominator (K := K) n f
lemma cechDenominator_ne_zero : D ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => MvPolynomial.X_ne_zero (f i))

lemma cechDenominator_mem_genericPrimeCompl :
    D ∈ (⊥ : Ideal S).primeCompl := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_bot]
  exact cechDenominator_ne_zero K n f

lemma genericPowersLE :
    Submonoid.powers D ≤
      Submonoid.comap (RingHom.id S) (⊥ : Ideal S).primeCompl := by
  intro x hx
  change x ∈ (⊥ : Ideal S).primeCompl
  exact (Submonoid.powers_le.mpr
    (cechDenominator_mem_genericPrimeCompl K n f)) hx

abbrev cechBasicOpen : Scheme.Opens (Proj PS) :=
  AlgebraicGeometry.Proj.basicOpen PS D

abbrev cechGenericPoint : cechBasicOpen K n f :=
  ⟨finitePolynomialGenericPoint (σ := σ) K,
    finitePolynomialGenericPoint_mem_basicOpen_cechDenominator K n f⟩

lemma polynomialToLaurent_degreeOnePower (m : ℕ) (k : σ) :
    polynomialToLaurent (K := K)
        ((degreeOnePower PS (finitePolynomialCoordinate K k) m : PS m) : S) =
      AddMonoidAlgebra.single (positiveTwistShift m k) 1 := by
  simp only [degreeOnePower, finitePolynomialCoordinate, map_pow, polynomialToLaurent_X,
    positiveTwistShift, coordinateExponent, AddMonoidAlgebra.single_pow, one_pow]

lemma positiveTwistShift_mul_twistShift (m : ℕ) (k : σ) :
    AddMonoidAlgebra.single (positiveTwistShift m k) (1 : K) *
      AddMonoidAlgebra.single (twistShift m k) 1 = 1 := by
  rw [AddMonoidAlgebra.single_mul_single]
  simp [positiveTwistShift, twistShift, AddMonoidAlgebra.one_def]

lemma twistShift_mul_positiveTwistShift (m : ℕ) (k : σ) :
    AddMonoidAlgebra.single (twistShift m k) (1 : K) *
      AddMonoidAlgebra.single (positiveTwistShift m k) 1 = 1 := by
  rw [mul_comm, positiveTwistShift_mul_twistShift K m k]

end GenericEvaluation
end PfaffianDescent.FinitePolynomialTwistCechTerms
end
noncomputable section
namespace PfaffianDescent.FinitePolynomialPositiveTwistNaturality
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist ProjectiveFiniteNative FinitePolynomialLaurentLocalization FinitePolynomialTwistLaurent
open FinitePolynomialTwistCechTerms FinitePolynomialTwistCechTerms.GenericEvaluation
open scoped AddMonoidAlgebra
universe u
variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nontrivial σ]
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (σ) K
@[simp] lemma finitePolynomialGenericPoint_positivePointIdeal :
    positivePointIdeal PS (finitePolynomialGenericPoint (σ := σ) K) = ⊥ :=
  finitePolynomialGenericPoint_pointIdeal K

section CommonBasicOpen

variable (n : ℕ) (f : Fin (n + 1) → σ)
local notation "D" => finitePolynomialCechDenominator (K := K) n f

lemma positiveGenericPowersLE :
    Submonoid.powers D ≤ Submonoid.comap
      (RingHom.id (MvPolynomial (σ) K))
      (positivePointIdeal PS (finitePolynomialGenericPoint (σ := σ) K)).primeCompl := by
  intro x hx
  have hx' := genericPowersLE K n f hx
  simpa only [Submonoid.mem_comap, RingHom.id_apply,
    finitePolynomialGenericPoint_positivePointIdeal] using hx'



noncomputable def positiveGenericLocalizationMap :
    Localization.Away D →+* PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K) :=
  IsLocalization.map (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
    (RingHom.id (MvPolynomial (σ) K))
    (positiveGenericPowersLE K n f)

lemma positiveGenericLocalizationMap_injective :
    Function.Injective (positiveGenericLocalizationMap K n f) := by
  exact IsLocalization.map_injective_of_injective'
    (Submonoid.powers D) (MvPolynomial (σ) K)
    (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
    (f := RingHom.id (MvPolynomial (σ) K))
    (Rₘ := Localization.Away D)
    (N := (positivePointIdeal PS (finitePolynomialGenericPoint (σ := σ) K)).primeCompl)
    (positiveGenericPowersLE K n f)
    (by
      intro h
      exact h (Ideal.zero_mem (positivePointIdeal PS (finitePolynomialGenericPoint (σ := σ) K))))
    (fun _ _ h => h)

lemma positiveGenericLocalizationMap_algebraMap
    (x : MvPolynomial (σ) K) :
    positiveGenericLocalizationMap K n f
        (algebraMap (MvPolynomial (σ) K) (Localization.Away D) x) =
      algebraMap (MvPolynomial (σ) K)
        (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K)) x := by
  exact IsLocalization.map_eq (positiveGenericPowersLE K n f) x

lemma awayToSection_positiveGeneric_apply
    (z : HomogeneousLocalization.Away PS D) :
    (((ProjectiveSpectrum.Proj.awayToSection PS D).1 z).val
      ⟨finitePolynomialGenericPoint (σ := σ) K,
        finitePolynomialGenericPoint_mem_basicOpen_cechDenominator K n f⟩).val =
      positiveGenericLocalizationMap K n f z.val := by
  dsimp only [finitePolynomialGenericPoint]
  unfold positiveGenericLocalizationMap
  rw [AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_apply]
  rfl




lemma awayToSection_finitePolynomialPositiveTwistChartAway
    (m : ℕ) (i : σ)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(positiveSheafOfModules PS m, finitePolynomialCechBasicOpen K n f)) :
    (ProjectiveSpectrum.Proj.awayToSection PS D).hom
        (finitePolynomialPositiveTwistChartAway K n f m i hdiv s) =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          (finitePolynomialCechBasicOpen K n f).topIso.hom
        ((finitePolynomialPositiveTwistSectionsIsoUnit K (finitePolynomialCechBasicOpen K n f) i
          (AlgebraicGeometry.Proj.basicOpen_mono PS
            (MvPolynomial.X i) D hdiv) m).hom s) := by
  let U := finitePolynomialCechBasicOpen K n f
  let e := AlgebraicGeometry.Proj.basicOpenIsoAway PS D
    (finitePolynomialCechDenominator_mem (K := K) n f) (Nat.succ_pos n)
  change e.hom
      ((finitePolynomialPositiveTwistBasicOpenIsoAway K D (n + 1)
        (finitePolynomialCechDenominator_mem (K := K) n f) (Nat.succ_pos n)
        i hdiv m).hom s) = _
  change e.hom (e.inv
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
      U.topIso.hom
      ((finitePolynomialPositiveTwistSectionsIsoUnit K U i
        (AlgebraicGeometry.Proj.basicOpen_mono PS
          (MvPolynomial.X i) D hdiv) m).hom s))) = _
  exact e.inv_hom_id_apply _



lemma genericLocalizationMap_finitePolynomialPositiveTwistChartAway
    (m : ℕ) (i : σ)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(positiveSheafOfModules PS m, finitePolynomialCechBasicOpen K n f)) :
    s.1 (cechGenericPoint K n f) =
      algebraMap (MvPolynomial (σ) K)
          (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
          ((degreeOnePower PS (finitePolynomialCoordinate K i) m : PS m) :
            MvPolynomial (σ) K) *
        (((ProjectiveSpectrum.Proj.awayToSection PS D).1
          (finitePolynomialPositiveTwistChartAway K n f m i hdiv s)).val
            (cechGenericPoint K n f)).val := by
  let U := finitePolynomialCechBasicOpen K n f
  let hU := AlgebraicGeometry.Proj.basicOpen_mono PS
    (MvPolynomial.X i) D hdiv
  let r := (finitePolynomialPositiveTwistSectionsIsoUnit K U i hU m).hom s
  have hinv := finitePolynomialPositiveTwistSectionsIsoUnit_inv_apply_val K U i hU m r
    (cechGenericPoint K n f)
  have hcancel : (finitePolynomialPositiveTwistSectionsIsoUnit K U i hU m).inv r = s := by
    exact (finitePolynomialPositiveTwistSectionsIsoUnit K U i hU m).hom_inv_id_apply s
  rw [hcancel] at hinv
  rw [hinv]
  congr 1
  have haway := awayToSection_finitePolynomialPositiveTwistChartAway K n f m i hdiv s
  have hfun :
      (ProjectiveSpectrum.Proj.awayToSection PS D).1
          (finitePolynomialPositiveTwistChartAway K n f m i hdiv s) =
        (ProjectiveSpectrum.Proj.awayToSection PS D).hom
          (finitePolynomialPositiveTwistChartAway K n f m i hdiv s) := rfl
  have haway' := haway.symm.trans hfun.symm
  simpa only [U, r] using
    congrArg (fun q => (q.1 (cechGenericPoint K n f)).val) haway'



lemma finitePolynomialPositiveTwistChartAway_cross_mul
    (m : ℕ) (i : σ)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (j : σ) (hdivj : MvPolynomial.X (R := K) j ∣ D)
    (s : Γ(positiveSheafOfModules PS m, finitePolynomialCechBasicOpen K n f)) :
    (finitePolynomialPositiveTwistChartAway K n f m i hdiv s).val *
        algebraMap (MvPolynomial (σ) K) (Localization.Away D)
          ((degreeOnePower PS (finitePolynomialCoordinate K i) m : PS m) :
            MvPolynomial (σ) K) =
      (finitePolynomialPositiveTwistChartAway K n f m j hdivj s).val *
        algebraMap (MvPolynomial (σ) K) (Localization.Away D)
          ((degreeOnePower PS (finitePolynomialCoordinate K j) m : PS m) :
            MvPolynomial (σ) K) := by
  apply positiveGenericLocalizationMap_injective K n f
  rw [map_mul, map_mul,
    positiveGenericLocalizationMap_algebraMap K n f,
    positiveGenericLocalizationMap_algebraMap K n f]
  have hi := genericLocalizationMap_finitePolynomialPositiveTwistChartAway
    K n f m i hdiv s
  have hj := genericLocalizationMap_finitePolynomialPositiveTwistChartAway
    K n f m j hdivj s
  have hgi := awayToSection_positiveGeneric_apply K n f
    (finitePolynomialPositiveTwistChartAway K n f m i hdiv s)
  have hgj := awayToSection_positiveGeneric_apply K n f
    (finitePolynomialPositiveTwistChartAway K n f m j hdivj s)
  change ((((ProjectiveSpectrum.Proj.awayToSection PS D).1
      (finitePolynomialPositiveTwistChartAway K n f m i hdiv s)).val
        (cechGenericPoint K n f)).val) = _ at hgi
  change ((((ProjectiveSpectrum.Proj.awayToSection PS D).1
      (finitePolynomialPositiveTwistChartAway K n f m j hdivj s)).val
        (cechGenericPoint K n f)).val) = _ at hgj
  have hsections :
      (((ProjectiveSpectrum.Proj.awayToSection PS D).1
          (finitePolynomialPositiveTwistChartAway K n f m i hdiv s)).val
            (cechGenericPoint K n f)).val *
          algebraMap (MvPolynomial (σ) K)
            (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
            ((degreeOnePower PS (finitePolynomialCoordinate K i) m : PS m) :
              MvPolynomial (σ) K) =
        (((ProjectiveSpectrum.Proj.awayToSection PS D).1
          (finitePolynomialPositiveTwistChartAway K n f m j hdivj s)).val
            (cechGenericPoint K n f)).val *
          algebraMap (MvPolynomial (σ) K)
            (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
            ((degreeOnePower PS (finitePolynomialCoordinate K j) m : PS m) :
              MvPolynomial (σ) K) := by
    calc
      _ = algebraMap (MvPolynomial (σ) K)
            (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
            ((degreeOnePower PS (finitePolynomialCoordinate K i) m : PS m) :
              MvPolynomial (σ) K) *
          (((ProjectiveSpectrum.Proj.awayToSection PS D).1
            (finitePolynomialPositiveTwistChartAway K n f m i hdiv s)).val
              (cechGenericPoint K n f)).val := mul_comm _ _
      _ = s.1 (cechGenericPoint K n f) := hi.symm
      _ = algebraMap (MvPolynomial (σ) K)
            (PositiveFiber PS (finitePolynomialGenericPoint (σ := σ) K))
            ((degreeOnePower PS (finitePolynomialCoordinate K j) m : PS m) :
              MvPolynomial (σ) K) *
          (((ProjectiveSpectrum.Proj.awayToSection PS D).1
            (finitePolynomialPositiveTwistChartAway K n f m j hdivj s)).val
              (cechGenericPoint K n f)).val := hj
      _ = _ := mul_comm _ _
  rw [hgi, hgj] at hsections
  exact hsections



lemma finitePolynomialPositiveTwistChartLaurent_independent
    (m : ℕ) (i : σ)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (j : σ) (hdivj : MvPolynomial.X (R := K) j ∣ D)
    (s : Γ(positiveSheafOfModules PS m, finitePolynomialCechBasicOpen K n f)) :
    awayToLaurent (K := K) n f
        (finitePolynomialPositiveTwistChartAway K n f m i hdiv s) *
        AddMonoidAlgebra.single (positiveTwistShift m i) 1 =
      awayToLaurent (K := K) n f
        (finitePolynomialPositiveTwistChartAway K n f m j hdivj s) *
        AddMonoidAlgebra.single (positiveTwistShift m j) 1 := by
  have hcross := finitePolynomialPositiveTwistChartAway_cross_mul
    K n f m i hdiv j hdivj s
  have hL := congrArg (localizationAwayToLaurent (K := K) n f) hcross
  simp only [map_mul, localizationAwayToLaurent_algebraMap,
    polynomialToLaurent_degreeOnePower K m] at hL
  change (localizationAwayToLaurent (K := K) n f)
        (finitePolynomialPositiveTwistChartAway K n f m i hdiv s).val *
        AddMonoidAlgebra.single (positiveTwistShift m i) 1 =
      (localizationAwayToLaurent (K := K) n f)
        (finitePolynomialPositiveTwistChartAway K n f m j hdivj s).val *
        AddMonoidAlgebra.single (positiveTwistShift m j) 1
  exact hL

end CommonBasicOpen




lemma finitePolynomialPositiveTwistChartLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → σ)
    (s : Γ(positiveSheafOfModules PS m,
      finitePolynomialCechBasicOpen K n (deleteTuple i f))) :
    let hS := finitePolynomialCoordinate_zero_dvd_cechDenominator
      (K := K) n (deleteTuple i f)
    let hx := finitePolynomialCechDenominator_succ_eq_deleteTuple_mul
      (K := K) n i f
    let hST : finitePolynomialCechBasicOpen K (n + 1) f ≤
        finitePolynomialCechBasicOpen K n (deleteTuple i f) :=
      AlgebraicGeometry.Proj.basicOpen_mono PS
        (finitePolynomialCechDenominator (K := K) n (deleteTuple i f))
        (finitePolynomialCechDenominator (K := K) (n + 1) f) ⟨_, hx⟩
    let sT : Γ(positiveSheafOfModules PS m, finitePolynomialCechBasicOpen K (n + 1) f) :=
      (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s
    awayToLaurent (K := K) (n + 1) f
        (finitePolynomialPositiveTwistChartAway K (n + 1) f m
          ((deleteTuple i f) 0) (dvd_trans hS ⟨_, hx⟩) sT) =
      awayToLaurent (K := K) n (deleteTuple i f)
        (finitePolynomialPositiveTwistChartAway K n (deleteTuple i f) m
          ((deleteTuple i f) 0) hS s) := by
  dsimp only
  let del := deleteTuple i f
  let denS := finitePolynomialCechDenominator (K := K) n del
  let denT := finitePolynomialCechDenominator (K := K) (n + 1) f
  let hx : denT = denS * MvPolynomial.X (R := K) (f i) :=
    finitePolynomialCechDenominator_succ_eq_deleteTuple_mul (K := K) n i f
  let hS := finitePolynomialCoordinate_zero_dvd_cechDenominator (K := K) n del
  let hAlt : MvPolynomial.X (R := K) (del 0) ∣ denT :=
    dvd_trans hS ⟨_, hx⟩
  let hST : finitePolynomialCechBasicOpen K (n + 1) f ≤ finitePolynomialCechBasicOpen K n del :=
    AlgebraicGeometry.Proj.basicOpen_mono PS denS denT ⟨_, hx⟩
  let sT : Γ(positiveSheafOfModules PS m, finitePolynomialCechBasicOpen K (n + 1) f) :=
    (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s
  let zS := finitePolynomialPositiveTwistChartAway K n del m (del 0) hS s
  let zT := finitePolynomialPositiveTwistChartAway K (n + 1) f m (del 0) hAlt sT
  have hnat := positiveTwistBasicOpenIsoAway_natural K
    denS (MvPolynomial.X (R := K) (f i)) denT (n + 1) 1
    (finitePolynomialCechDenominator_mem (K := K) n del)
    (coordinate_mem_degree_one (K := K) (f i)) (Nat.succ_pos n) hx
    (del 0) hS m
  have hres : zT = awayFaceMap (K := K) n i f zS := by
    have happ := congrArg (fun q => q s) hnat
    simp only [ConcreteCategory.comp_apply] at happ
    change _ = _
    convert happ using 1
    rfl
  change awayToLaurent (K := K) (n + 1) f zT =
    awayToLaurent (K := K) n del zS
  rw [hres, awayToLaurent_awayFaceMap]


end PfaffianDescent.FinitePolynomialPositiveTwistNaturality

end
