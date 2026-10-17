import PfaffianDescent.PlaneNegativeChartGenericNaturality
/-! SOURCE ONLY / UNCHECKED. Native three-coordinate positive chart independence,
proved through the original injective generic field evaluation, followed by
actual coordinate-cover face restriction. No comparison outcome is a premise. -/
noncomputable section
namespace PfaffianDescent.PlanePositiveTwistNaturality
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist ProjectivePlaneNative PlaneLaurentLocalization PlaneTwistLaurent
open PlaneTwistCechTerms PlaneTwistCechTerms.GenericEvaluation
open scoped AddMonoidAlgebra
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K
@[simp] lemma p2GenericPoint_positivePointIdeal :
    positivePointIdeal PS (p2GenericPoint K) = ⊥ :=
  p2GenericPoint_pointIdeal K

section CommonBasicOpen

variable (n : ℕ) (f : Fin (n + 1) → Fin 3)
local notation "D" => p2CechDenominator (K := K) n f

lemma positiveGenericPowersLE :
    Submonoid.powers D ≤ Submonoid.comap
      (RingHom.id (MvPolynomial (Fin 3) K))
      (positivePointIdeal PS (p2GenericPoint K)).primeCompl := by
  intro x hx
  have hx' := genericPowersLE K n f hx
  simpa only [Submonoid.mem_comap, RingHom.id_apply,
    p2GenericPoint_positivePointIdeal] using hx'

/-- The localization map from a Cech denominator directly into the ambient
fiber used by the positive twist at the generic point. -/
noncomputable def positiveGenericLocalizationMap :
    Localization.Away D →+* PositiveFiber PS (p2GenericPoint K) :=
  IsLocalization.map (PositiveFiber PS (p2GenericPoint K))
    (RingHom.id (MvPolynomial (Fin 3) K))
    (positiveGenericPowersLE K n f)

lemma positiveGenericLocalizationMap_injective :
    Function.Injective (positiveGenericLocalizationMap K n f) := by
  exact IsLocalization.map_injective_of_injective'
    (Submonoid.powers D) (MvPolynomial (Fin 3) K)
    (PositiveFiber PS (p2GenericPoint K))
    (f := RingHom.id (MvPolynomial (Fin 3) K))
    (Rₘ := Localization.Away D)
    (N := (positivePointIdeal PS (p2GenericPoint K)).primeCompl)
    (positiveGenericPowersLE K n f)
    (by
      intro h
      exact h (Ideal.zero_mem (positivePointIdeal PS (p2GenericPoint K))))
    (fun _ _ h => h)

lemma positiveGenericLocalizationMap_algebraMap
    (x : MvPolynomial (Fin 3) K) :
    positiveGenericLocalizationMap K n f
        (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away D) x) =
      algebraMap (MvPolynomial (Fin 3) K)
        (PositiveFiber PS (p2GenericPoint K)) x := by
  exact IsLocalization.map_eq (positiveGenericPowersLE K n f) x

lemma awayToSection_positiveGeneric_apply
    (z : HomogeneousLocalization.Away PS D) :
    (((ProjectiveSpectrum.Proj.awayToSection PS D).1 z).val
      ⟨p2GenericPoint K,
        p2GenericPoint_mem_basicOpen_cechDenominator K n f⟩).val =
      positiveGenericLocalizationMap K n f z.val := by
  dsimp only [p2GenericPoint]
  unfold positiveGenericLocalizationMap
  rw [AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_apply]
  rfl

/-- Undoing the homogeneous-localization presentation of a positive chart
coordinate gives the ordinary structure-function supplied by the local
trivialization. -/
lemma awayToSection_p2PositiveTwistChartAway
    (m : ℕ) (i : Fin 3)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K n f)) :
    (ProjectiveSpectrum.Proj.awayToSection PS D).hom
        (p2PositiveTwistChartAway K n f m i hdiv s) =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          (p2CechBasicOpen K n f).topIso.hom
        ((p2PositiveTwistSectionsIsoUnit K (p2CechBasicOpen K n f) i
          (AlgebraicGeometry.Proj.basicOpen_mono PS
            (MvPolynomial.X i) D hdiv) m).hom s) := by
  let U := p2CechBasicOpen K n f
  let e := AlgebraicGeometry.Proj.basicOpenIsoAway PS D
    (p2CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
  change e.hom
      ((p2PositiveTwistBasicOpenIsoAway K D (n + 1)
        (p2CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
        i hdiv m).hom s) = _
  change e.hom (e.inv
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
      U.topIso.hom
      ((p2PositiveTwistSectionsIsoUnit K U i
        (AlgebraicGeometry.Proj.basicOpen_mono PS
          (MvPolynomial.X i) D hdiv) m).hom s))) = _
  exact e.inv_hom_id_apply _

/-- At the generic point, a positive-twist section is its chart coordinate
multiplied by the chart basis `X_i^m`. -/
lemma genericLocalizationMap_p2PositiveTwistChartAway
    (m : ℕ) (i : Fin 3)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K n f)) :
    s.1 (cechGenericPoint K n f) =
      algebraMap (MvPolynomial (Fin 3) K)
          (PositiveFiber PS (p2GenericPoint K))
          ((degreeOnePower PS (p2Coordinate K i) m : PS m) :
            MvPolynomial (Fin 3) K) *
        (((ProjectiveSpectrum.Proj.awayToSection PS D).1
          (p2PositiveTwistChartAway K n f m i hdiv s)).val
            (cechGenericPoint K n f)).val := by
  let U := p2CechBasicOpen K n f
  let hU := AlgebraicGeometry.Proj.basicOpen_mono PS
    (MvPolynomial.X i) D hdiv
  let r := (p2PositiveTwistSectionsIsoUnit K U i hU m).hom s
  have hinv := p2PositiveTwistSectionsIsoUnit_inv_apply_val K U i hU m r
    (cechGenericPoint K n f)
  have hcancel : (p2PositiveTwistSectionsIsoUnit K U i hU m).inv r = s := by
    exact (p2PositiveTwistSectionsIsoUnit K U i hU m).hom_inv_id_apply s
  rw [hcancel] at hinv
  rw [hinv]
  congr 1
  have haway := awayToSection_p2PositiveTwistChartAway K n f m i hdiv s
  have hfun :
      (ProjectiveSpectrum.Proj.awayToSection PS D).1
          (p2PositiveTwistChartAway K n f m i hdiv s) =
        (ProjectiveSpectrum.Proj.awayToSection PS D).hom
          (p2PositiveTwistChartAway K n f m i hdiv s) := rfl
  have haway' := haway.symm.trans hfun.symm
  simpa only [U, r] using
    congrArg (fun q => (q.1 (cechGenericPoint K n f)).val) haway'

/-- Two positive chart coordinates of the same section agree after each is
multiplied by its own chart basis. -/
lemma p2PositiveTwistChartAway_cross_mul
    (m : ℕ) (i : Fin 3)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (j : Fin 3) (hdivj : MvPolynomial.X (R := K) j ∣ D)
    (s : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K n f)) :
    (p2PositiveTwistChartAway K n f m i hdiv s).val *
        algebraMap (MvPolynomial (Fin 3) K) (Localization.Away D)
          ((degreeOnePower PS (p2Coordinate K i) m : PS m) :
            MvPolynomial (Fin 3) K) =
      (p2PositiveTwistChartAway K n f m j hdivj s).val *
        algebraMap (MvPolynomial (Fin 3) K) (Localization.Away D)
          ((degreeOnePower PS (p2Coordinate K j) m : PS m) :
            MvPolynomial (Fin 3) K) := by
  apply positiveGenericLocalizationMap_injective K n f
  rw [map_mul, map_mul,
    positiveGenericLocalizationMap_algebraMap K n f,
    positiveGenericLocalizationMap_algebraMap K n f]
  have hi := genericLocalizationMap_p2PositiveTwistChartAway
    K n f m i hdiv s
  have hj := genericLocalizationMap_p2PositiveTwistChartAway
    K n f m j hdivj s
  have hgi := awayToSection_positiveGeneric_apply K n f
    (p2PositiveTwistChartAway K n f m i hdiv s)
  have hgj := awayToSection_positiveGeneric_apply K n f
    (p2PositiveTwistChartAway K n f m j hdivj s)
  change ((((ProjectiveSpectrum.Proj.awayToSection PS D).1
      (p2PositiveTwistChartAway K n f m i hdiv s)).val
        (cechGenericPoint K n f)).val) = _ at hgi
  change ((((ProjectiveSpectrum.Proj.awayToSection PS D).1
      (p2PositiveTwistChartAway K n f m j hdivj s)).val
        (cechGenericPoint K n f)).val) = _ at hgj
  have hsections :
      (((ProjectiveSpectrum.Proj.awayToSection PS D).1
          (p2PositiveTwistChartAway K n f m i hdiv s)).val
            (cechGenericPoint K n f)).val *
          algebraMap (MvPolynomial (Fin 3) K)
            (PositiveFiber PS (p2GenericPoint K))
            ((degreeOnePower PS (p2Coordinate K i) m : PS m) :
              MvPolynomial (Fin 3) K) =
        (((ProjectiveSpectrum.Proj.awayToSection PS D).1
          (p2PositiveTwistChartAway K n f m j hdivj s)).val
            (cechGenericPoint K n f)).val *
          algebraMap (MvPolynomial (Fin 3) K)
            (PositiveFiber PS (p2GenericPoint K))
            ((degreeOnePower PS (p2Coordinate K j) m : PS m) :
              MvPolynomial (Fin 3) K) := by
    calc
      _ = algebraMap (MvPolynomial (Fin 3) K)
            (PositiveFiber PS (p2GenericPoint K))
            ((degreeOnePower PS (p2Coordinate K i) m : PS m) :
              MvPolynomial (Fin 3) K) *
          (((ProjectiveSpectrum.Proj.awayToSection PS D).1
            (p2PositiveTwistChartAway K n f m i hdiv s)).val
              (cechGenericPoint K n f)).val := mul_comm _ _
      _ = s.1 (cechGenericPoint K n f) := hi.symm
      _ = algebraMap (MvPolynomial (Fin 3) K)
            (PositiveFiber PS (p2GenericPoint K))
            ((degreeOnePower PS (p2Coordinate K j) m : PS m) :
              MvPolynomial (Fin 3) K) *
          (((ProjectiveSpectrum.Proj.awayToSection PS D).1
            (p2PositiveTwistChartAway K n f m j hdivj s)).val
              (cechGenericPoint K n f)).val := hj
      _ = _ := mul_comm _ _
  rw [hgi, hgj] at hsections
  exact hsections

/-- Restoring the chart basis makes the Laurent representative of a
positive-twist section independent of the chosen coordinate. -/
lemma p2PositiveTwistChartLaurent_independent
    (m : ℕ) (i : Fin 3)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (j : Fin 3) (hdivj : MvPolynomial.X (R := K) j ∣ D)
    (s : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K n f)) :
    awayToLaurent (K := K) n f
        (p2PositiveTwistChartAway K n f m i hdiv s) *
        AddMonoidAlgebra.single (positiveTwistShift m i) 1 =
      awayToLaurent (K := K) n f
        (p2PositiveTwistChartAway K n f m j hdivj s) *
        AddMonoidAlgebra.single (positiveTwistShift m j) 1 := by
  have hcross := p2PositiveTwistChartAway_cross_mul
    K n f m i hdiv j hdivj s
  have hL := congrArg (localizationAwayToLaurent (K := K) n f) hcross
  simp only [map_mul, localizationAwayToLaurent_algebraMap,
    polynomialToLaurent_degreeOnePower K m] at hL
  change (localizationAwayToLaurent (K := K) n f)
        (p2PositiveTwistChartAway K n f m i hdiv s).val *
        AddMonoidAlgebra.single (positiveTwistShift m i) 1 =
      (localizationAwayToLaurent (K := K) n f)
        (p2PositiveTwistChartAway K n f m j hdivj s).val *
        AddMonoidAlgebra.single (positiveTwistShift m j) 1
  exact hL

end CommonBasicOpen

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a positive chart coordinate along a Cech face does not
change its Laurent expansion when the same coordinate is used on both
opens. -/
lemma p2PositiveTwistChartLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 3)
    (s : Γ(positiveSheafOfModules PS m,
      p2CechBasicOpen K n (deleteTuple i f))) :
    let hS := p2Coordinate_zero_dvd_cechDenominator
      (K := K) n (deleteTuple i f)
    let hx := p2CechDenominator_succ_eq_deleteTuple_mul
      (K := K) n i f
    let hST : p2CechBasicOpen K (n + 1) f ≤
        p2CechBasicOpen K n (deleteTuple i f) :=
      AlgebraicGeometry.Proj.basicOpen_mono PS
        (p2CechDenominator (K := K) n (deleteTuple i f))
        (p2CechDenominator (K := K) (n + 1) f) ⟨_, hx⟩
    let sT : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K (n + 1) f) :=
      (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s
    awayToLaurent (K := K) (n + 1) f
        (p2PositiveTwistChartAway K (n + 1) f m
          ((deleteTuple i f) 0) (dvd_trans hS ⟨_, hx⟩) sT) =
      awayToLaurent (K := K) n (deleteTuple i f)
        (p2PositiveTwistChartAway K n (deleteTuple i f) m
          ((deleteTuple i f) 0) hS s) := by
  dsimp only
  let del := deleteTuple i f
  let denS := p2CechDenominator (K := K) n del
  let denT := p2CechDenominator (K := K) (n + 1) f
  let hx : denT = denS * MvPolynomial.X (R := K) (f i) :=
    p2CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f
  let hS := p2Coordinate_zero_dvd_cechDenominator (K := K) n del
  let hAlt : MvPolynomial.X (R := K) (del 0) ∣ denT :=
    dvd_trans hS ⟨_, hx⟩
  let hST : p2CechBasicOpen K (n + 1) f ≤ p2CechBasicOpen K n del :=
    AlgebraicGeometry.Proj.basicOpen_mono PS denS denT ⟨_, hx⟩
  let sT : Γ(positiveSheafOfModules PS m, p2CechBasicOpen K (n + 1) f) :=
    (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s
  let zS := p2PositiveTwistChartAway K n del m (del 0) hS s
  let zT := p2PositiveTwistChartAway K (n + 1) f m (del 0) hAlt sT
  have hnat := positiveTwistBasicOpenIsoAway_natural K
    denS (MvPolynomial.X (R := K) (f i)) denT (n + 1) 1
    (p2CechDenominator_mem (K := K) n del)
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


end PfaffianDescent.PlanePositiveTwistNaturality
